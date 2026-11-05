import Lean.Data.Json
import LeanNative.IR.Codec
import LeanNative.Semantics.Eval
import LeanNative.Transform.Superopt
import LeanNative.Transform.CostAutotune

namespace LeanNative.Driver.CostAutotuneCLI

open Lean LeanNative.IR LeanNative.Semantics LeanNative.Transform

private def operations : List String :=
  ["add", "bitwise", "shift", "cmp", "mul", "div", "fma", "select"]

private def acceptedOperations : List String := operations ++
  ["sub", "mod", "bitAnd", "bitOr", "bitXor", "shl", "shr", "sar", "eq", "lt", "le", "not", "neg",
   "add_sub", "addSub", "div_mod", "divMod", "clz256",
   "add_sub_checked256", "addSubChecked256", "mul_checked256", "mulChecked256",
   "min_gpu_elements", "minGpuElements", "gpu_block_threads", "gpuBlockThreads",
   "matmul_tile_dim", "matmulTileDim"]

private structure Options where
  target : String := "x86_64"
  samplesPath : Option String := none
  json : Bool := false

private def parseOptions (args : List String) : Except String Options := do
  let rec go (args : List String) (opts : Options) (seen : List String) : Except String Options := do
    match args with
    | [] => return opts
    | "--json" :: rest =>
      if seen.contains "--json" then throw "duplicate --json"
      go rest { opts with json := true } ("--json" :: seen)
    | flag :: value :: rest =>
      if flag != "--target" && flag != "--samples-json" then throw s!"unknown option '{flag}'"
      if seen.contains flag then throw s!"duplicate {flag}"
      if value.isEmpty || value.startsWith "-" then throw s!"{flag} requires a value"
      go rest (if flag == "--target" then { opts with target := value }
        else { opts with samplesPath := some value }) (flag :: seen)
    | [flag] => throw s!"unknown option or missing value: {flag}"
  go args {} []

private def positiveNat (j : Json) : Except String Nat := do
  let num ← j.getNum?
  if num.exponent != 0 || num.mantissa <= 0 then throw "elapsedNs and iterations must be positive integers"
  return num.mantissa.toNat

private def parseSample (j : Json) : Except String OpTimingSample := do
  let fields ← j.getObj?
  let keys := fields.foldl (fun acc k _ => k :: acc) ([] : List String)
  if keys.length != 3 || !(keys.all (["operation", "elapsedNs", "iterations"].contains ·)) then
    throw "sample must contain exactly operation, elapsedNs, iterations"
  let operation ← (← j.getObjVal? "operation").getStr?
  if operation.isEmpty then throw "operation must not be empty"
  if !acceptedOperations.contains operation then throw s!"unsupported operation '{operation}'"
  let elapsedNs ← positiveNat (← j.getObjVal? "elapsedNs")
  let iterations ← positiveNat (← j.getObjVal? "iterations")
  return { operation, elapsedNs, iterations }

private def fieldCount (raw : String) : Nat := Id.run do
  let mut quoted := false
  let mut escaped := false
  let mut count := 0
  for c in raw.toList do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then quoted := true
    else if c == ':' then count := count + 1
  return count

def parseSamples (raw : String) : Except String (List OpTimingSample) := do
  let rows ← (← Json.parse raw).getArr?
  if rows.isEmpty then throw "samples array must not be empty"
  let samples ← rows.toList.mapM parseSample
  if fieldCount raw != rows.size * 3 then throw "duplicate sample fields are forbidden"
  return samples

#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":100,\"iterations\":10}]").toOption.isSome
#guard (parseSamples "[]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":0,\"iterations\":10}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":100,\"iterations\":0}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":1.5,\"iterations\":10}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":100,\"iterations\":10,\"extra\":1}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":100,\"elapsedNs\":200,\"iterations\":10}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"unknown\",\"elapsedNs\":100,\"iterations\":10}]").toOption.isNone

@[noinline] private def runLoop (step : UInt64 → UInt64 → UInt64)
    (iterations seed : UInt64) : UInt64 := Id.run do
  let mut i : UInt64 := 0
  let mut x := seed
  while i < iterations do
    x := step x (i ||| 1)
    i := i + 1
  return x

private def operationStep : String → UInt64 → UInt64 → UInt64
  | "add" => fun x y => x + y
  | "bitwise" => fun x y => x ^^^ y
  | "shift" => fun x y => x >>> (y &&& 63)
  | "cmp" => fun x y => if x < y then 1 else 0
  | "mul" => fun x y => x * y
  | "div" => fun x y => x / y
  | "fma" => fun x y => x * y + y
  | _ => fun x y => if (x &&& 1) == 0 then y else x

private def checkHost (target : String) (base : HardwareCostProfile) : IO String := do
  let app ← IO.appPath
  if ["lean", "lean.exe", "lake", "lake.exe"].contains (app.fileName.getD "") then
    throw <| IO.userError "host calibration requires a compiled native executable, not lean --run"
  let host ← IO.Process.output { cmd := "uname", args := #["-m"] }
  if host.exitCode != 0 then throw <| IO.userError "cannot establish host CPU architecture"
  let arch := host.stdout.trimAscii.toString
  let compatible := (base.target == .x86_64 && arch == "x86_64") ||
    (base.target == .arm64 && (arch == "aarch64" || arch == "arm64"))
  if !compatible then
    throw <| IO.userError s!"cannot measure target '{target}' on host '{arch}'; provide --samples-json from that hardware"
  if target == "zen5" then
    let cpu ← IO.FS.readFile "/proc/cpuinfo"
    let lines := cpu.splitOn "\n"
    let family26 := lines.any fun line => match line.splitOn ":" with
      | [key, value] => key.trimAscii.toString == "cpu family" && value.trimAscii.toString == "26"
      | _ => false
    if !(cpu.contains "AuthenticAMD" && family26) then
      throw <| IO.userError "cannot establish Zen 5 host identity; use --target x86_64 or --samples-json"
  if target == "neoverse" || target == "scaleway" then
    throw <| IO.userError s!"cannot establish preset '{target}' host identity; use --target arm64 or --samples-json"
  return arch

private def measureHost (target : String) (base : HardwareCostProfile) : IO (List OpTimingSample × Json) := do
  let arch ← checkHost target base
  let iterations : UInt64 := 2000000
  let mut checksum : UInt64 := (← IO.monoNanosNow).toUInt64 ||| 1
  let mut samples : List OpTimingSample := []
  for operation in operations do
    let step := operationStep operation
    let warm := runLoop step 10000 checksum
    let start ← IO.monoNanosNow
    let result := runLoop step iterations warm
    let stop ← IO.monoNanosNow
    checksum := checksum * 1099511628211 + result + 1
    if stop <= start then throw <| IO.userError "non-positive host timing; calibration aborted"
    samples := samples ++ [{ operation, elapsedNs := stop - start, iterations := iterations.toNat }]
  return (samples, Json.mkObj [
    ("source", .str "host_cpu_wall_clock"), ("hostArchitecture", .str arch),
    ("checksum", toJson checksum.toNat),
    ("method", .str "native UInt64 dependency-chain loops; includes loop/call overhead; integer multiply-add, not floating-point FMA"),
    ("canonicalCorpusExecuted", .bool true), ("tuningMeasured", .bool false)])

def verifyAndAccumulateCorpus (baseMod candMod : LNIRModule) (iters : Nat) :
    Except String (UInt64 × UInt64) := do
  let env := ((VarEnv.empty).bind 0 (.u64 17)).bind 1 (.u64 64)
  let baseDecls := baseMod.decls.filter fun d =>
    d.name == "collatz_steps" || d.name == "tuple_accum_sum"
  let candDecls := candMod.decls.filter fun d =>
    d.name == "collatz_steps" || d.name == "tuple_accum_sum"
  if baseDecls.length != candDecls.length || baseDecls.isEmpty then
    throw "canonical corpus declaration count mismatch"
  let mut checksumB : UInt64 := 14695981039346656037
  let mut checksumC : UInt64 := 14695981039346656037
  for iterIdx in [:iters] do
    let iterU64 := iterIdx.toUInt64
    for (db, dc) in baseDecls.zip candDecls do
      if db.name != dc.name then
        throw s!"canonical corpus declaration order mismatch ({db.name} vs {dc.name})"
      match evalCode 256 env HeapState.empty db.body,
            evalCode 256 env HeapState.empty dc.body with
      | .ok (.u64 vb, _), .ok (.u64 vc, _) =>
        if vb != vc then
          throw s!"canonical corpus evaluation diverged on {db.name} at iter {iterIdx}"
        checksumB := checksumB * 1099511628211 + vb + iterU64
        checksumC := checksumC * 1099511628211 + vc + iterU64
      | _, _ =>
        throw s!"canonical corpus evaluation failed on {db.name} at iter {iterIdx}"
  if checksumB != checksumC then
    throw "canonical corpus rolling checksum diverged"
  return (checksumB, checksumC)

private def evalCorpusChecksums (mod : LNIRModule) (iters : Nat) : Except String UInt64 := do
  let env := ((VarEnv.empty).bind 0 (.u64 17)).bind 1 (.u64 64)
  let decls := mod.decls.filter fun d =>
    d.name == "collatz_steps" || d.name == "tuple_accum_sum"
  if decls.isEmpty then throw "canonical corpus has no target declarations"
  let mut checksum : UInt64 := 14695981039346656037
  for iterIdx in [:iters] do
    let iterU64 := iterIdx.toUInt64
    for d in decls do
      match evalCode 256 env HeapState.empty d.body with
      | .ok (.u64 result, _) =>
        checksum := checksum * 1099511628211 + result + iterU64
      | _ =>
        throw s!"canonical corpus evaluation failed on {d.name}"
  return checksum

private def measureCorpus (profile : HardwareCostProfile) : IO (List CorpusTimingSample × LNIRModule) := do
  let m := mkCanonicalBenchmarkModule8
  let (candMod, report) := superoptModuleWithProfile profile m
  match verifyAndAccumulateCorpus m candMod 8 with
  | .ok _ => pure ()
  | .error msg => throw <| IO.userError msg
  let b0 ← IO.monoNanosNow
  let checksumB ← match evalCorpusChecksums m 128 with
    | .ok v => pure v
    | .error msg => throw <| IO.userError msg
  let b1 ← IO.monoNanosNow
  let c0 ← IO.monoNanosNow
  let checksumC ← match evalCorpusChecksums candMod 128 with
    | .ok v => pure v
    | .error msg => throw <| IO.userError msg
  let c1 ← IO.monoNanosNow
  match verifyAndAccumulateCorpus m candMod 128 with
  | .ok (verB, verC) =>
    if checksumB != checksumC || checksumB != verB || checksumC != verC then
      throw <| IO.userError "canonical corpus evaluation diverged"
  | .error msg => throw <| IO.userError msg
  let bNs := max 1 (b1 - b0)
  let cNs := max 1 (c1 - c0)
  return ([{ baselineNs := bNs, candidateNs := cNs, hits := report.rewritesApplied,
             declName := m.moduleName }], candMod)

private def sampleJson (s : OpTimingSample) : Json := Json.mkObj [
  ("operation", .str s.operation), ("elapsedNs", toJson s.elapsedNs), ("iterations", toJson s.iterations)]

private def receiptJson (r : CalibrationReceipt) : Json := Json.mkObj [
  ("accepted", .bool r.accepted), ("baselineNs", toJson r.baselineNs),
  ("candidateNs", toJson r.candidateNs), ("hits", toJson r.hits)]

def run (args : List String) : IO UInt32 := do
  try
    let opts ← IO.ofExcept (parseOptions args)
    let some base := calibrationPreset opts.target
      | throw <| IO.userError s!"unknown calibration target '{opts.target}'"
    let (samples, provenance) ← match opts.samplesPath with
      | some path => do
        let samples ← IO.ofExcept (parseSamples (← IO.FS.readFile path))
        pure (samples, Json.mkObj [("source", .str "provided_samples"),
          ("hostMeasured", .bool false), ("canonicalCorpusExecuted", .bool true), ("tuningMeasured", .bool false)])
      | none => measureHost opts.target base
    let profile := calibrateHardwareProfile base samples
    let (corpus, _) ← measureCorpus profile
    let (_, receipt) := autotuneSuperoptModule base samples corpus mkCanonicalBenchmarkModule8
    let profileJson ← IO.ofExcept (Json.parse profile.toJson)
    let report := Json.mkObj [("status", .str "calibrated"), ("target", .str opts.target),
      ("profile", profileJson), ("amdahlReceipt", receiptJson receipt),
      ("samples", .arr (samples.map sampleJson).toArray), ("provenance", provenance)]
    if opts.json then IO.println report.compress
    else
      IO.println s!"[calibrate-cost] {opts.target}: {samples.length} timing samples; amdahlAccepted={receipt.accepted} (hits={receipt.hits}, {receipt.baselineNs}ns -> {receipt.candidateNs}ns)"
      IO.println profile.toJson
    return 0
  catch e =>
    if args.contains "--json" then
      IO.println (Json.mkObj [("status", .str "error"), ("error", .str (toString e))]).compress
    else IO.eprintln s!"[calibrate-cost] {e}"
    return 1

end LeanNative.Driver.CostAutotuneCLI
