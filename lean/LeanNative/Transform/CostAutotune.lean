import LeanNative.Transform.Pass
import LeanNative.Transform.Superopt

namespace LeanNative.Transform

open LeanNative.IR

structure OpTimingSample where
  operation : String
  elapsedNs : Nat
  iterations : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

def canonicalTimingOperation : String → String
  | "add" | "sub" | "addSub" | "add_sub" => "add_sub"
  | "bitAnd" | "bitOr" | "bitXor" | "not" | "neg" => "bitwise"
  | "shl" | "shr" | "sar" => "shift"
  | "eq" | "lt" | "le" => "cmp"
  | "div" | "mod" | "divMod" | "div_mod" => "div_mod"
  | "addChecked256" | "subChecked256" | "addSubChecked256" | "add_sub_checked256" =>
    "add_sub_checked256"
  | "mulChecked256" | "mul_checked256" => "mul_checked256"
  | "minGpuElements" => "min_gpu_elements"
  | "gpuBlockThreads" => "gpu_block_threads"
  | "matmulTileDim" => "matmul_tile_dim"
  | operation => operation

def operationMedianNs? (samples : List OpTimingSample) (operation : String) : Option Nat :=
  let values := samples.filterMap fun s =>
    if s.iterations > 0 && s.elapsedNs > 0 &&
        canonicalTimingOperation s.operation == canonicalTimingOperation operation then
      some (max 1 (s.elapsedNs / s.iterations))
    else none
  let sorted := values.mergeSort (fun a b => a ≤ b)
  if sorted.isEmpty then none
  else
    let upper := sorted[sorted.length / 2]?.getD 1
    let lower := sorted[(sorted.length - 1) / 2]?.getD 1
    some ((lower + upper) / 2)

def calibrateHardwareProfile (base : HardwareCostProfile) (samples : List OpTimingSample) :
    HardwareCostProfile :=
  let unit := (operationMedianNs? samples "add_sub").getD 1
  let cost := fun operation preset =>
    match operationMedianNs? samples operation with
    | some ns => max 1 (ns / unit)
    | none => max 1 preset
  let tuning := fun operation preset => max 1 ((operationMedianNs? samples operation).getD preset)
  { base with
    addSubCost := cost "add_sub" base.addSubCost
    bitwiseCost := cost "bitwise" base.bitwiseCost
    shiftCost := cost "shift" base.shiftCost
    cmpCost := cost "cmp" base.cmpCost
    mulCost := cost "mul" base.mulCost
    divModCost := cost "div_mod" base.divModCost
    fmaCost := cost "fma" base.fmaCost
    selectCost := cost "select" base.selectCost
    clz256Cost := cost "clz256" base.clz256Cost
    addSubChecked256Cost := cost "add_sub_checked256" base.addSubChecked256Cost
    mulChecked256Cost := cost "mul_checked256" base.mulChecked256Cost
    minGpuElements := tuning "min_gpu_elements" base.minGpuElements
    gpuBlockThreads := tuning "gpu_block_threads" base.gpuBlockThreads
    matmulTileDim := tuning "matmul_tile_dim" base.matmulTileDim }

def HardwareCostProfile.toJson (p : HardwareCostProfile) : String :=
  let strings := [
    ("profile_id", p.profileId), ("target", p.target.toString),
    ("llvm_target_cpu", p.llvmTargetCpu), ("sm_arch", p.smArch)]
  let numbers := [
    ("add_sub_cost", p.addSubCost), ("bitwise_cost", p.bitwiseCost),
    ("shift_cost", p.shiftCost), ("cmp_cost", p.cmpCost),
    ("mul_cost", p.mulCost), ("div_mod_cost", p.divModCost),
    ("fma_cost", p.fmaCost), ("select_cost", p.selectCost),
    ("clz256_cost", p.clz256Cost), ("add_sub_checked256_cost", p.addSubChecked256Cost),
    ("mul_checked256_cost", p.mulChecked256Cost), ("min_gpu_elements", p.minGpuElements),
    ("gpu_block_threads", p.gpuBlockThreads), ("matmul_tile_dim", p.matmulTileDim)]
  "{" ++ String.intercalate "," (
    strings.map (fun (key, value) => "\"" ++ key ++ "\":\"" ++ jsonEscape value ++ "\"") ++
    numbers.map (fun (key, value) => "\"" ++ key ++ "\":" ++ toString value)) ++ "}"

structure CorpusTimingSample where
  baselineNs : Nat
  candidateNs : Nat
  hits : Nat
  declName : String := ""
  deriving Repr, DecidableEq, Inhabited, BEq

def meetsOnePercentE2EGain (b c : Nat) : Bool :=
  b > 0 && c * 100 <= b * 99

structure CalibrationReceipt where
  profile : HardwareCostProfile
  accepted : Bool
  baselineNs : Nat
  candidateNs : Nat
  hits : Nat
  report : Option SuperoptReport := none
  deriving Repr, DecidableEq, Inhabited, BEq

def aggregateCorpusTimings (corpus : List CorpusTimingSample) : CorpusTimingSample :=
  corpus.foldl (fun total sample =>
    { baselineNs := total.baselineNs + sample.baselineNs
      candidateNs := total.candidateNs + sample.candidateNs
      hits := total.hits + sample.hits })
    { baselineNs := 0, candidateNs := 0, hits := 0 }

def corpusCalibrationReceipt (p : HardwareCostProfile) (corpus : List CorpusTimingSample)
    (rewriteHits : Nat) (report : Option SuperoptReport := none) : CalibrationReceipt :=
  let totals := aggregateCorpusTimings corpus
  { profile := p
    accepted := !corpus.isEmpty && rewriteHits > 0 && totals.hits > 0 &&
      corpus.all (fun s => s.baselineNs > 0 && s.candidateNs > 0) &&
      meetsOnePercentE2EGain totals.baselineNs totals.candidateNs
    baselineNs := totals.baselineNs
    candidateNs := totals.candidateNs
    hits := totals.hits
    report := report }

def pruneCandidateByAmdahl (p : HardwareCostProfile) (corpus : List CorpusTimingSample)
    (m : LNIRModule) : LNIRModule × CalibrationReceipt :=
  let (candidate, report) := superoptModuleWithProfile p m
  let receipt := corpusCalibrationReceipt p corpus report.rewritesApplied (some report)
  (if receipt.accepted then candidate else m, receipt)

def autotuneSuperoptModule (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (m : LNIRModule) : LNIRModule × CalibrationReceipt :=
  let p := calibrateHardwareProfile base samples
  let (candidate, receipt) := pruneCandidateByAmdahl p corpus m
  (candidate, { receipt with profile := if receipt.accepted then p else base })

def autotuneDeclWithAmdahl (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (d : LNIRDecl) : LNIRDecl × CalibrationReceipt :=
  let p := calibrateHardwareProfile base samples
  let (candidate, records) := superoptDeclCore p s!"{p.target.toString}:{p.profileId}" d
  let timings := corpus.filter (fun s => s.declName.isEmpty || s.declName == d.name)
  let receipt := corpusCalibrationReceipt p timings records.length
  (if receipt.accepted then candidate else d,
    { receipt with profile := if receipt.accepted then p else base })

def calibrationPreset : String → Option HardwareCostProfile
  | "zen5" => some { HardwareCostProfile.forTarget .x86_64 with
      profileId := "x86_64_zen5_avx512", llvmTargetCpu := "znver5" }
  | "x86_64" => some (HardwareCostProfile.forTarget .x86_64)
  | "arm64" => some (HardwareCostProfile.forTarget .arm64)
  | "neoverse" => some { HardwareCostProfile.forTarget .arm64 with
      profileId := "arm64_grace_neoverse_v2", llvmTargetCpu := "neoverse-v2" }
  | "scaleway" => some { HardwareCostProfile.forTarget .arm64 with
      profileId := "arm64_scaleway_neoverse", llvmTargetCpu := "neoverse-n1" }
  | "rtx4090" => some { HardwareCostProfile.forTarget .cuda_ptx with
      profileId := "cuda_ada_rtx4090_sm89", smArch := "sm_89" }
  | "sm_89" => some { HardwareCostProfile.forTarget .cuda_ptx with
      profileId := "cuda_ada_sm89", smArch := "sm_89" }
  | "sm_90" => some { HardwareCostProfile.forTarget .cuda_ptx with
      profileId := "cuda_hopper_sm90", smArch := "sm_90" }
  | _ => none

def autotuneCodeWithAmdahl (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (c : LNIRCode) : LNIRCode :=
  let p := calibrateHardwareProfile base samples
  let (candidate, records) := superoptCodeCore p s!"{p.target.toString}:{p.profileId}" "autotune" c
  let receipt := corpusCalibrationReceipt p corpus records.length
  if receipt.accepted then candidate else c

def verifiedCostAutotuneContract (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample)
    (h : ∀ c : LNIRCode,
      LeanNative.Semantics.CodeRefines c (autotuneCodeWithAmdahl base samples corpus c)) :
    VerifiedCodePassContract where
  name := "CostAutotune"
  theoremRef := "LeanNative.Proofs.autotuneCodeWithAmdahl_sound"
  notes := "Hardware-calibrated superoptimization gated by exact >= 1% Amdahl pruning"
  runCode := autotuneCodeWithAmdahl base samples corpus
  sound := h

end LeanNative.Transform
