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
    minGpuElements := max 1 base.minGpuElements
    gpuBlockThreads := max 1 base.gpuBlockThreads
    matmulTileDim := max 1 base.matmulTileDim }

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
  let selection := match p.keptSites? with
    | none => []
    | some sites => ["\"kept_sites\":[" ++ String.intercalate "," (sites.map fun (decl, site) =>
        "{\"decl\":\"" ++ jsonEscape decl ++ "\",\"site\":" ++ toString site ++ "}") ++ "]"]
  "{" ++ String.intercalate "," (
    strings.map (fun (key, value) => "\"" ++ key ++ "\":\"" ++ jsonEscape value ++ "\"") ++
    numbers.map (fun (key, value) => "\"" ++ key ++ "\":" ++ toString value) ++ selection) ++ "}"

structure CorpusTimingSample where
  baselineNs : Nat
  candidateNs : Nat
  hits : Nat
  declName : String := ""
  deriving Repr, DecidableEq, Inhabited, BEq

def meetsOnePercentE2EGain (b c : Nat) : Bool :=
  b > 0 && c * 100 <= b * 99

def corpusProdBaseline (corpus : List CorpusTimingSample) : Nat :=
  corpus.foldl (fun acc s => acc * s.baselineNs) 1

def corpusProdCandidate (corpus : List CorpusTimingSample) : Nat :=
  corpus.foldl (fun acc s => acc * s.candidateNs) 1

def meetsCorpusGeomeanOnePercentGain (corpus : List CorpusTimingSample) : Bool :=
  !corpus.isEmpty &&
    corpus.all (fun s => s.baselineNs > 0 && s.candidateNs > 0) &&
    corpusProdCandidate corpus * (100 ^ corpus.length) <=
      corpusProdBaseline corpus * (99 ^ corpus.length)

structure CandidateAblationSample where
  siteIdx : Nat
  declName : String := ""
  baselineNs : Nat
  soloCandidateNs : Nat
  hits : Nat := 1
  workloadPairs : List (Nat × Nat) := []
  deriving Repr, DecidableEq, Inhabited, BEq

def candidateAblationSurvives (s : CandidateAblationSample) : Bool :=
  s.hits > 0 && s.baselineNs > 0 && s.soloCandidateNs > 0 &&
    meetsCorpusGeomeanOnePercentGain (s.workloadPairs.map fun (b, c) =>
      { baselineNs := b, candidateNs := c, hits := s.hits })

def keepSiteByAblations (ablations : List CandidateAblationSample) (siteIdx : Nat)
    (expectedPairs : Nat := 1) : Bool :=
  let matching := ablations.filter (fun s => s.siteIdx == siteIdx)
  !matching.isEmpty && matching.all (fun s =>
    s.workloadPairs.length == expectedPairs && candidateAblationSurvives s)

def superoptCodeSelective (p : HardwareCostProfile) (targetLabel declName : String)
    (keepIdx : Nat → Bool) : LNIRCode → Nat → LNIRCode × List SuperoptRewriteRecord × Nat
  | .letBind dst ty (.scalar se) k, nextIdx =>
    match superoptScalarExprCore p targetLabel declName se with
    | (se', some r) =>
      let keep := keepIdx nextIdx
      let chosen := if keep then se' else se
      let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k (nextIdx + 1)
      (.letBind dst ty (.scalar chosen) k', if keep then r :: kRecs else kRecs, nextIdx')
    | (_, none) =>
      let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k nextIdx
      (.letBind dst ty (.scalar se) k', kRecs, nextIdx')
  | .letBind dst ty val k, nextIdx =>
    let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k nextIdx
    (.letBind dst ty val k', kRecs, nextIdx')
  | .rawStore pv iv vv ety k, nextIdx =>
    let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k nextIdx
    (.rawStore pv iv vv ety k', kRecs, nextIdx')
  | .incRef ov c k, nextIdx =>
    let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k nextIdx
    (.incRef ov c k', kRecs, nextIdx')
  | .decRef ov c k, nextIdx =>
    let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k nextIdx
    (.decRef ov c k', kRecs, nextIdx')
  | .ite cv t e, nextIdx =>
    let (t', tRecs, midIdx) := superoptCodeSelective p targetLabel declName keepIdx t nextIdx
    let (e', eRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx e midIdx
    (.ite cv t' e', tRecs ++ eRecs, nextIdx')
  | .seqFor iv lv hv av ai aty step k, nextIdx =>
    let (step', sRecs, midIdx) := superoptCodeSelective p targetLabel declName keepIdx step nextIdx
    let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k midIdx
    (.seqFor iv lv hv av ai aty step' k', sRecs ++ kRecs, nextIdx')
  | .parFor ov lv ins ety (.customScalar idxVar inVars body) k, nextIdx =>
    match superoptScalarExprCore p targetLabel declName body with
    | (body', some r) =>
      let keep := keepIdx nextIdx
      let chosen := if keep then body' else body
      let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k (nextIdx + 1)
      (.parFor ov lv ins ety (.customScalar idxVar inVars chosen) k',
        if keep then r :: kRecs else kRecs, nextIdx')
    | (_, none) =>
      let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k nextIdx
      (.parFor ov lv ins ety (.customScalar idxVar inVars body) k', kRecs, nextIdx')
  | .parFor ov lv ins ety kern k, nextIdx =>
    let (k', kRecs, nextIdx') := superoptCodeSelective p targetLabel declName keepIdx k nextIdx
    (.parFor ov lv ins ety kern k', kRecs, nextIdx')
  | .ret v, nextIdx => (.ret v, [], nextIdx)
  | .unreachable, nextIdx => (.unreachable, [], nextIdx)

def superoptDeclSelective (p : HardwareCostProfile) (targetLabel : String)
    (keepIdx : Nat → Bool) (d : LNIRDecl) (nextIdx : Nat) :
    LNIRDecl × List SuperoptRewriteRecord × Nat :=
  let (body', recs, count) := superoptCodeSelective p targetLabel d.name keepIdx d.body 0
  let assurance' :=
    if recs.isEmpty then d.assurance
    else AssuranceLevel.combine d.assurance .verifiedKernelProof
  ({ d with body := body', assurance := assurance' }, recs, nextIdx + count)

def superoptModuleSelective (p : HardwareCostProfile) (keepIdx : String → Nat → Bool)
    (m : LNIRModule) : LNIRModule × SuperoptReport × Nat :=
  let targetLabel := s!"{p.target.toString}:{p.profileId}"
  let costBefore := m.decls.foldl (fun acc d => acc + codeScalarCostWithProfile p d.body) 0
  let (decls', allRecs, totalSites) := m.decls.foldl (fun (dAcc, rAcc, idx) d =>
    let (d', recs, idx') := superoptDeclSelective p targetLabel (keepIdx d.name) d idx
    (dAcc ++ [d'], rAcc ++ recs, idx')
  ) ([], [], 0)
  let m' : LNIRModule := { m with decls := decls' }
  let costAfter := m'.decls.foldl (fun acc d => acc + codeScalarCostWithProfile p d.body) 0
  (m', {
    moduleName := m.moduleName
    schemaVersion := "lean-native-superopt-v1"
    target := targetLabel
    totalDecls := m.decls.length
    rewritesApplied := allRecs.length
    totalCostBefore := costBefore
    totalCostAfter := costAfter
    records := allRecs
  }, totalSites)

def superoptModuleWithProfile (p : HardwareCostProfile) (m : LNIRModule) : LNIRModule × SuperoptReport :=
  let (candidate, report, _) := superoptModuleSelective p
    (fun decl idx => p.keptSites?.all (fun sites => sites.contains (decl, idx))) m
  (candidate, report)

def keepDeclSiteByAblations (ablations : List CandidateAblationSample) (decl : String)
    (expectedPairs : Nat := 1) : Nat → Bool :=
  fun idx => keepSiteByAblations (ablations.filter (fun s => s.declName == decl)) idx expectedPairs

structure CalibrationReceipt where
  profile : HardwareCostProfile
  accepted : Bool
  baselineNs : Nat
  candidateNs : Nat
  hits : Nat
  sitesConsidered : Nat := 0
  sitesPruned : Nat := 0
  report : Option SuperoptReport := none
  deriving Repr, DecidableEq, Inhabited, BEq

def aggregateCorpusTimings (corpus : List CorpusTimingSample) : CorpusTimingSample :=
  corpus.foldl (fun total sample =>
    { baselineNs := total.baselineNs + sample.baselineNs
      candidateNs := total.candidateNs + sample.candidateNs
      hits := total.hits + sample.hits })
    { baselineNs := 0, candidateNs := 0, hits := 0 }

def corpusCalibrationReceipt (p : HardwareCostProfile) (corpus : List CorpusTimingSample)
    (rewriteHits : Nat) (report : Option SuperoptReport := none)
    (sitesConsidered : Nat := rewriteHits) (sitesPruned : Nat := 0) : CalibrationReceipt :=
  let totals := aggregateCorpusTimings corpus
  { profile := p
    accepted := meetsCorpusGeomeanOnePercentGain corpus && rewriteHits > 0 && totals.hits > 0
    baselineNs := totals.baselineNs
    candidateNs := totals.candidateNs
    hits := totals.hits
    sitesConsidered := sitesConsidered
    sitesPruned := sitesPruned
    report := report }

def pruneCandidatesByAblation (p : HardwareCostProfile) (corpus : List CorpusTimingSample)
    (m : LNIRModule) (ablations : List CandidateAblationSample := []) :
    LNIRModule × CalibrationReceipt :=
  let keepIdx := fun decl => keepDeclSiteByAblations ablations decl corpus.length
  let (candidate, report, totalSites) := superoptModuleSelective p keepIdx m
  let pruned := totalSites - report.rewritesApplied
  let sites := m.decls.flatMap fun d =>
    let (_, _, count) := superoptDeclSelective p "" (fun _ => true) d 0
    (List.range count).filterMap fun idx => if keepIdx d.name idx then some (d.name, idx) else none
  let selected := { p with keptSites? := some sites }
  let receipt := corpusCalibrationReceipt selected corpus report.rewritesApplied (some report) totalSites pruned
  (if receipt.accepted then candidate else m, receipt)

def pruneCandidateByAmdahl (p : HardwareCostProfile) (corpus : List CorpusTimingSample)
    (m : LNIRModule) (ablations : List CandidateAblationSample := []) :
    LNIRModule × CalibrationReceipt :=
  pruneCandidatesByAblation p corpus m ablations

def autotuneSuperoptModule (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (m : LNIRModule)
    (ablations : List CandidateAblationSample := []) : LNIRModule × CalibrationReceipt :=
  let p := calibrateHardwareProfile base samples
  let (candidate, receipt) := pruneCandidatesByAblation p corpus m ablations
  (candidate, { receipt with profile :=
    if receipt.accepted then receipt.profile else { base with keptSites? := some [] } })

def autotuneDeclWithAmdahl (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (d : LNIRDecl)
    (ablations : List CandidateAblationSample := []) : LNIRDecl × CalibrationReceipt :=
  let p := calibrateHardwareProfile base samples
  let declAblations := ablations.filter (fun s => s.declName == d.name)
  let keepIdx := fun idx => keepSiteByAblations declAblations idx corpus.length
  let (candidate, records, totalSites) :=
    superoptDeclSelective p s!"{p.target.toString}:{p.profileId}" keepIdx d 0
  let declHits := (aggregateCorpusTimings (corpus.filter (fun s => s.declName == d.name))).hits
  let pruned := totalSites - records.length
  let sites := (List.range totalSites).filterMap fun idx =>
    if keepIdx idx then some (d.name, idx) else none
  let selected := { p with keptSites? := some sites }
  let receipt := corpusCalibrationReceipt selected corpus (if declHits > 0 then records.length else 0)
    none totalSites pruned
  (if receipt.accepted then candidate else d,
    { receipt with profile := if receipt.accepted then selected else { base with keptSites? := some [] } })

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
    (corpus : List CorpusTimingSample) (ablations : List CandidateAblationSample := [])
    (c : LNIRCode) (declName : String := "autotune") : LNIRCode :=
  let p := calibrateHardwareProfile base samples
  let keepIdx := keepDeclSiteByAblations ablations declName corpus.length
  let (candidate, records, totalSites) :=
    superoptCodeSelective p s!"{p.target.toString}:{p.profileId}" declName keepIdx c 0
  let pruned := totalSites - records.length
  let receipt := corpusCalibrationReceipt p corpus records.length none totalSites pruned
  if receipt.accepted then candidate else c

def verifiedCostAutotuneContract (base : HardwareCostProfile) (samples : List OpTimingSample)
    (corpus : List CorpusTimingSample) (ablations : List CandidateAblationSample := [])
    (h : ∀ c : LNIRCode,
      LeanNative.Semantics.CodeRefines c (autotuneCodeWithAmdahl base samples corpus ablations c)) :
    VerifiedCodePassContract where
  name := "CostAutotune"
  theoremRef := "LeanNative.Proofs.autotuneCodeWithAmdahl_sound"
  notes := "Hardware-calibrated superoptimization gated by exact >= 1% Amdahl & ablation pruning"
  runCode := autotuneCodeWithAmdahl base samples corpus ablations
  sound := h

end LeanNative.Transform
