import LeanNative.Transform.CostAutotune
import LeanNative.Proofs.SuperoptSoundness

set_option autoImplicit false

namespace LeanNative.Proofs

open LeanNative.IR LeanNative.Semantics LeanNative.Transform

theorem calibrateHardwareProfile_preserves_target (base : HardwareCostProfile)
    (samples : List OpTimingSample) :
    let p := calibrateHardwareProfile base samples
    p.target = base.target ∧ p.profileId = base.profileId ∧
    p.llvmTargetCpu = base.llvmTargetCpu ∧ p.smArch = base.smArch ∧
    0 < p.addSubCost ∧ 0 < p.bitwiseCost ∧ 0 < p.shiftCost ∧ 0 < p.cmpCost ∧
    0 < p.mulCost ∧ 0 < p.divModCost ∧ 0 < p.fmaCost ∧ 0 < p.selectCost ∧
    0 < p.clz256Cost ∧ 0 < p.addSubChecked256Cost ∧ 0 < p.mulChecked256Cost ∧
    0 < p.minGpuElements ∧ 0 < p.gpuBlockThreads ∧ 0 < p.matmulTileDim := by
  have max_one_pos (n : Nat) : 0 < max 1 n := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 n)
  have cost_pos (op : String) (preset unit : Nat) :
      0 < (match operationMedianNs? samples op with
        | some ns => max 1 (ns / unit)
        | none => max 1 preset) := by
    split <;> exact max_one_pos _
  dsimp only [calibrateHardwareProfile]
  exact ⟨rfl, rfl, rfl, rfl, cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _,
    cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _,
    cost_pos _ _ _, cost_pos _ _ _, cost_pos _ _ _, max_one_pos _, max_one_pos _,
    max_one_pos _⟩

theorem meetsOnePercentE2EGain_iff (b c : Nat) :
    meetsOnePercentE2EGain b c = true ↔ 0 < b ∧ c * 100 ≤ b * 99 := by
  simp [meetsOnePercentE2EGain]

theorem meetsOnePercentE2EGain_rejects_subthreshold (b c : Nat)
    (h : b * 99 < c * 100) : meetsOnePercentE2EGain b c = false := by
  simp [meetsOnePercentE2EGain, Nat.not_le.mpr h]

theorem meetsCorpusGeomeanOnePercentGain_iff (corpus : List CorpusTimingSample) :
    meetsCorpusGeomeanOnePercentGain corpus = true ↔
      corpus ≠ [] ∧
      (∀ s ∈ corpus, 0 < s.baselineNs ∧ 0 < s.candidateNs) ∧
      corpusProdCandidate corpus * (100 ^ corpus.length) ≤
        corpusProdBaseline corpus * (99 ^ corpus.length) := by
  simp [meetsCorpusGeomeanOnePercentGain, Bool.and_assoc]

theorem meetsCorpusGeomeanOnePercentGain_rejects_summed_false_positive :
    let corpus := [
      CorpusTimingSample.mk 10000 9700 1 "k0",
      CorpusTimingSample.mk 100 200 1 "k1"
    ]
    let totals := aggregateCorpusTimings corpus
    meetsOnePercentE2EGain totals.baselineNs totals.candidateNs = true ∧
    meetsCorpusGeomeanOnePercentGain corpus = false := by
  decide

theorem superoptCodeSelective_sound (p : HardwareCostProfile) (targetLabel declName : String)
    (keepIdx : Nat → Bool) (code : LNIRCode) (nextIdx : Nat) :
    CodeRefines code (superoptCodeSelective p targetLabel declName keepIdx code nextIdx).1 := by
  induction code generalizing nextIdx with
  | letBind dst ty val k ih =>
    cases val with
    | scalar se =>
      simp only [superoptCodeSelective]
      cases hse : superoptScalarExprCore p targetLabel declName se with
      | mk se' recOpt =>
        cases recOpt with
        | none =>
          exact CodeRefines.letBind_congr (ExprRefines.refl _) (ih nextIdx)
        | some r =>
          dsimp only []
          have hchoose :
              ExprRefines (.scalar se) (.scalar (if keepIdx nextIdx then se' else se)) := by
            split
            · have hsnd := superoptScalarExprCore_sound p targetLabel declName se
              rw [hse] at hsnd
              exact hsnd
            · exact ExprRefines.refl _
          exact CodeRefines.letBind_congr hchoose (ih (nextIdx + 1))
    | _ =>
      simp only [superoptCodeSelective]
      exact CodeRefines.letBind_congr (ExprRefines.refl _) (ih nextIdx)
  | rawStore pv iv vv ety k ih =>
    simp only [superoptCodeSelective]
    exact CodeRefines.rawStore_congr (ih nextIdx)
  | incRef ov c k ih =>
    simp only [superoptCodeSelective]
    exact CodeRefines.incRef_congr (ih nextIdx)
  | decRef ov c k ih =>
    simp only [superoptCodeSelective]
    exact CodeRefines.decRef_congr (ih nextIdx)
  | ite cv t e iht ihe =>
    simp only [superoptCodeSelective]
    exact CodeRefines.ite_congr (iht nextIdx) (ihe _)
  | seqFor iv lv hv av ai aty step k ihs ihk =>
    intro fuel env st v st' hsrc
    simp only [superoptCodeSelective, evalCode] at hsrc ⊢
    cases hlo : env lv with
    | none => simp [hlo] at hsrc
    | some vlo =>
      cases hhi : env hv with
      | none => simp [hlo, hhi] at hsrc
      | some vhi =>
        cases hinit : env ai with
        | none => simp [hlo, hhi, hinit] at hsrc
        | some vinit =>
          simp only [hlo, hhi, hinit] at hsrc ⊢
          cases vlo <;> try simp at hsrc
          cases vhi <;> try simp at hsrc
          rename_i lo hi
          dsimp only [] at hsrc ⊢
          cases hloop :
              evalSeqLoop (hi.toNat - lo.toNat) lo.toNat iv av vinit env st
                (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step) with
          | error err => simp [hloop] at hsrc
          | ok pair =>
            rw [hloop] at hsrc
            have hloop' :=
              evalSeqLoop_refines (hi.toNat - lo.toNat) lo.toNat iv av vinit env st
                (fun stepEnv stepSt => evalCode fuel stepEnv stepSt step)
                (fun stepEnv stepSt =>
                  evalCode fuel stepEnv stepSt
                    (superoptCodeSelective p targetLabel declName keepIdx step nextIdx).1)
                pair (fun sEnv sSt sv sSt' hs => ihs nextIdx fuel sEnv sSt sv sSt' hs) hloop
            rw [hloop']
            exact ihk _ fuel (env.bind av pair.1) pair.2 v st' hsrc
  | parFor ov lv ins ety kern k ih =>
    cases kern with
    | customScalar idxVar inVars body =>
      intro fuel env st v st' hsrc
      simp only [superoptCodeSelective]
      cases hse : superoptScalarExprCore p targetLabel declName body with
      | mk body' recOpt =>
        cases recOpt with
        | none =>
          simp only [evalCode] at hsrc ⊢
          cases hpar : evalParFor fuel env st lv ins (.customScalar idxVar inVars body) with
          | error err => simp [hpar] at hsrc
          | ok pair =>
            rw [hpar] at hsrc
            exact ih nextIdx fuel (env.bind ov pair.1) pair.2 v st' hsrc
        | some r =>
          dsimp only []
          simp only [evalCode] at hsrc ⊢
          cases hpar : evalParFor fuel env st lv ins (.customScalar idxVar inVars body) with
          | error err => simp [hpar] at hsrc
          | ok pair =>
            rw [hpar] at hsrc
            have hchoose :
                ExprRefines (.scalar body)
                  (.scalar (if keepIdx nextIdx then body' else body)) := by
              split
              · have hsnd := superoptScalarExprCore_sound p targetLabel declName body
                rw [hse] at hsnd
                exact hsnd
              · exact ExprRefines.refl _
            have hpar' :=
              evalParFor_customScalar_refines fuel env st lv ins idxVar inVars body
                (if keepIdx nextIdx then body' else body) pair hchoose hpar
            rw [hpar']
            exact ih (nextIdx + 1) fuel (env.bind ov pair.1) pair.2 v st' hsrc
    | _ =>
      simp only [superoptCodeSelective]
      exact CodeRefines.parFor_congr (ih nextIdx)
  | ret _ =>
    simp only [superoptCodeSelective]
    exact CodeRefines.refl _
  | unreachable =>
    simp only [superoptCodeSelective]
    exact CodeRefines.refl _

theorem superoptDeclSelective_sound (p : HardwareCostProfile) (targetLabel : String)
    (keepIdx : Nat → Bool) (d : LNIRDecl) (nextIdx : Nat) :
    CodeRefines d.body (superoptDeclSelective p targetLabel keepIdx d nextIdx).1.body := by
  unfold superoptDeclSelective
  exact superoptCodeSelective_sound p targetLabel d.name keepIdx d.body 0

private theorem foldl_selective_decls_mem_acc (p : HardwareCostProfile) (targetLabel : String)
    (keepIdx : String → Nat → Bool) (ds : List LNIRDecl) (dAcc : List LNIRDecl)
    (rAcc : List SuperoptRewriteRecord) (idx : Nat) (x : LNIRDecl) (hx : x ∈ dAcc) :
    x ∈ (ds.foldl (fun (accD, accR, curIdx) d =>
      let (d', recs, nextIdx) := superoptDeclSelective p targetLabel (keepIdx d.name) d curIdx
      (accD ++ [d'], accR ++ recs, nextIdx)) (dAcc, rAcc, idx)).1 := by
  induction ds generalizing dAcc rAcc idx with
  | nil => exact hx
  | cons d0 rest ih =>
    simp only [List.foldl]
    exact ih
      (dAcc ++ [(superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).1])
      (rAcc ++ (superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).2.1)
      (superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).2.2
      (List.mem_append_left _ hx)

private theorem foldl_selective_decls_refines (p : HardwareCostProfile) (targetLabel : String)
    (keepIdx : String → Nat → Bool) (ds : List LNIRDecl) (dAcc : List LNIRDecl)
    (rAcc : List SuperoptRewriteRecord) (idx : Nat) :
    ∀ d ∈ ds, ∃ d' ∈ (ds.foldl (fun (accD, accR, curIdx) d =>
      let (d', recs, nextIdx) := superoptDeclSelective p targetLabel (keepIdx d.name) d curIdx
      (accD ++ [d'], accR ++ recs, nextIdx)) (dAcc, rAcc, idx)).1,
      CodeRefines d.body d'.body := by
  intro d hd
  induction ds generalizing dAcc rAcc idx with
  | nil => cases hd
  | cons d0 rest ih =>
    simp only [List.foldl, List.mem_cons] at hd ⊢
    cases hd with
    | inl heq =>
      subst d
      refine ⟨(superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).1, ?_,
        superoptDeclSelective_sound p targetLabel (keepIdx d0.name) d0 idx⟩
      exact foldl_selective_decls_mem_acc p targetLabel keepIdx rest
        (dAcc ++ [(superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).1])
        (rAcc ++ (superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).2.1)
        (superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).2.2
        (superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).1
        (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    | inr hmem =>
      exact ih
        (dAcc ++ [(superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).1])
        (rAcc ++ (superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).2.1)
        (superoptDeclSelective p targetLabel (keepIdx d0.name) d0 idx).2.2 hmem

theorem superoptModuleSelective_sound (p : HardwareCostProfile) (keepIdx : String → Nat → Bool)
    (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModuleSelective p keepIdx m).1.decls,
      CodeRefines d.body d'.body := by
  intro d hd
  unfold superoptModuleSelective
  exact foldl_selective_decls_refines p s!"{p.target.toString}:{p.profileId}"
    keepIdx m.decls [] [] 0 d hd

theorem superoptModuleWithProfile_sound (p : HardwareCostProfile) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (superoptModuleWithProfile p m).1.decls, CodeRefines d.body d'.body := by
  unfold superoptModuleWithProfile
  exact superoptModuleSelective_sound p
    (fun decl idx => p.keptSites?.all (fun sites => sites.contains (decl, idx))) m

theorem superoptModuleWithCalibratedProfile_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (m : LNIRModule) :
    ∀ d ∈ m.decls,
      ∃ d' ∈ (superoptModuleWithProfile (calibrateHardwareProfile base samples) m).1.decls,
        CodeRefines d.body d'.body :=
  superoptModuleWithProfile_sound (calibrateHardwareProfile base samples) m

theorem autotuneCodeWithAmdahl_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample)
    (ablations : List CandidateAblationSample := []) (c : LNIRCode) (declName : String := "autotune") :
    CodeRefines c (autotuneCodeWithAmdahl base samples corpus ablations c declName) := by
  unfold autotuneCodeWithAmdahl
  dsimp only []
  split
  · exact superoptCodeSelective_sound _ _ _ _ c 0
  · exact CodeRefines.refl _

theorem autotuneCodeWithAmdahl_uncalibrated_preserves (base : HardwareCostProfile)
    (samples : List OpTimingSample) (ablations : List CandidateAblationSample := [])
    (c : LNIRCode) :
    autotuneCodeWithAmdahl base samples [] ablations c = c := by
  simp [autotuneCodeWithAmdahl, corpusCalibrationReceipt, meetsCorpusGeomeanOnePercentGain]

theorem autotuneDeclWithAmdahl_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample) (d : LNIRDecl)
    (ablations : List CandidateAblationSample := []) :
    CodeRefines d.body (autotuneDeclWithAmdahl base samples corpus d ablations).1.body := by
  unfold autotuneDeclWithAmdahl
  dsimp only []
  have gate (accept : Bool) (candidate : LNIRDecl) (h : CodeRefines d.body candidate.body) :
      CodeRefines d.body (if accept then candidate else d).body := by
    cases accept
    · exact CodeRefines.refl _
    · exact h
  exact gate _ _ (superoptDeclSelective_sound _ _ _ d 0)

theorem autotuneSuperoptModule_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample) (m : LNIRModule)
    (ablations : List CandidateAblationSample := []) :
    ∀ d ∈ m.decls, ∃ d' ∈ (autotuneSuperoptModule base samples corpus m ablations).1.decls,
      CodeRefines d.body d'.body := by
  intro d hd
  unfold autotuneSuperoptModule pruneCandidatesByAblation
  dsimp only []
  split
  · exact superoptModuleSelective_sound (calibrateHardwareProfile base samples)
      (keepDeclSiteByAblations ablations) m d hd
  · exact ⟨d, hd, CodeRefines.refl _⟩

theorem costAutotune_amdahl_gate_nonvacuous :
    let base := HardwareCostProfile.forTarget .x86_64
    let p := calibrateHardwareProfile base []
    let e := ScalarExpr.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)
    let fused := ScalarExpr.fma (.var 0) (.var 1) (.var 2)
    let d : LNIRDecl := {
      name := "fma", params := [], retTy := .i64
      body := .letBind 3 .i64 (.scalar e) (.ret 3) }
    let m : LNIRModule := { moduleName := "amdahl", decls := [d] }
    let good := autotuneSuperoptModule base []
      [CorpusTimingSample.mk 1000 990 1 ""] m
      [{ siteIdx := 0, declName := "fma", baselineNs := 1000, soloCandidateNs := 980 }]
    let bad := autotuneSuperoptModule base []
      [CorpusTimingSample.mk 1000 991 1 ""] m
      [{ siteIdx := 0, declName := "fma", baselineNs := 1000, soloCandidateNs := 980 }]
    let ablatedReject := autotuneSuperoptModule base []
      [CorpusTimingSample.mk 1000 990 1 ""] m
      [CandidateAblationSample.mk 0 "fma" 1000 995 1 []]
    scalarExprCostWithProfile p fused < scalarExprCostWithProfile p e ∧
    good.2.accepted = true ∧
    bad.2.accepted = false ∧
    ablatedReject.2.accepted = false ∧
    good.1.decls.map (·.body) = [.letBind 3 .i64 (.scalar fused) (.ret 3)] ∧
    bad.1 = m ∧
    ablatedReject.1 = m ∧
    good.2.profile.keptSites? = some [("fma", 0)] ∧
    bad.2.profile = { base with keptSites? := some [] } ∧
    ablatedReject.2.profile = { base with keptSites? := some [] } ∧
    good.2.report.map (·.rewritesApplied) = some 1 ∧
    bad.2.report.map (·.rewritesApplied) = some 1 ∧
    ablatedReject.2.sitesPruned = 1 := by
  have hp : calibrateHardwareProfile (HardwareCostProfile.forTarget .x86_64) [] =
      HardwareCostProfile.forTarget .x86_64 := by
    simp [calibrateHardwareProfile, operationMedianNs?, HardwareCostProfile.forTarget]
  have hv0 : synthesizeCandidates .x86_64 (.var 0) = [.var 0] := by
    rw [synthesizeCandidates.eq_def]; decide
  have hv1 : synthesizeCandidates .x86_64 (.var 1) = [.var 1] := by
    rw [synthesizeCandidates.eq_def]; decide
  have hv2 : synthesizeCandidates .x86_64 (.var 2) = [.var 2] := by
    rw [synthesizeCandidates.eq_def]; decide
  have hmul : synthesizeCandidates .x86_64 (.binOp .mul (.var 0) (.var 1)) =
      [.binOp .mul (.var 0) (.var 1)] := by
    rw [synthesizeCandidates.eq_def]
    simp only [hv0, hv1]
    decide
  have hcands : synthesizeCandidates .x86_64
      (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) =
      [.fma (.var 0) (.var 1) (.var 2),
       .binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)] := by
    rw [synthesizeCandidates.eq_def]
    simp only [hmul, hv2]
    decide
  have hso (lbl : String) :
      ∃ r : SuperoptRewriteRecord,
        superoptScalarExprCore (HardwareCostProfile.forTarget .x86_64) lbl "fma"
          (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) =
          (.fma (.var 0) (.var 1) (.var 2), some r) := by
    unfold superoptScalarExprCore
    have htgt : (HardwareCostProfile.forTarget .x86_64).target = .x86_64 := rfl
    simp only [htgt, hcands, List.foldl]
    have hstep1 :
        (checkSuperoptScalarVerified
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.fma (.var 0) (.var 1) (.var 2)) &&
          fastCheckScalarEquiv
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.fma (.var 0) (.var 1) (.var 2)) &&
          symCheckScalarEquiv
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.fma (.var 0) (.var 1) (.var 2)) &&
          decide (scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.fma (.var 0) (.var 1) (.var 2)) <
            scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)))) = true := by decide
    have hstep2 :
        (checkSuperoptScalarVerified
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) &&
          fastCheckScalarEquiv
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) &&
          symCheckScalarEquiv
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))
            (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) &&
          decide (scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) <
            scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.fma (.var 0) (.var 1) (.var 2)))) = false := by decide
    have hguard :
        ((ScalarExpr.fma (.var 0) (.var 1) (.var 2) !=
            ScalarExpr.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) &&
          decide (scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.fma (.var 0) (.var 1) (.var 2)) <
            scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
              (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)))) = true := by decide
    simp only [hstep1, hstep2, ite_true]
    exact ⟨_, rfl⟩
  let lbl :=
    toString (HardwareCostProfile.forTarget .x86_64).target.toString ++
      toString ":" ++
      toString (HardwareCostProfile.forTarget .x86_64).profileId
  have hlbl :
      toString (HardwareCostProfile.forTarget .x86_64).target.toString ++
        toString ":" ++
        toString (HardwareCostProfile.forTarget .x86_64).profileId =
        lbl := rfl
  rcases hso lbl with ⟨r, hr⟩
  rcases hso "" with ⟨r0, hr0⟩
  have hcodeKeep :
      superoptCodeSelective (HardwareCostProfile.forTarget .x86_64) lbl "fma"
        (keepSiteByAblations [CandidateAblationSample.mk 0 "fma" 1000 980 1 []])
        (.letBind 3 .i64 (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3)) 0 =
      (.letBind 3 .i64 (.scalar (.fma (.var 0) (.var 1) (.var 2))) (.ret 3), [r], 1) := by
    rw [superoptCodeSelective, hr]
    simp [superoptCodeSelective, keepSiteByAblations, candidateAblationSurvives, meetsOnePercentE2EGain]
  have hcodePrune :
      superoptCodeSelective (HardwareCostProfile.forTarget .x86_64) lbl "fma"
        (keepSiteByAblations [CandidateAblationSample.mk 0 "fma" 1000 995 1 []])
        (.letBind 3 .i64 (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3)) 0 =
      (.letBind 3 .i64 (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3), [], 1) := by
    rw [superoptCodeSelective, hr]
    simp [superoptCodeSelective, keepSiteByAblations, candidateAblationSurvives, meetsOnePercentE2EGain]
  have hcost :
      scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
        (.fma (.var 0) (.var 1) (.var 2)) <
      scalarExprCostWithProfile (HardwareCostProfile.forTarget .x86_64)
        (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)) := by decide
  have hdeclKeep :
      superoptDeclSelective (HardwareCostProfile.forTarget .x86_64) lbl
        (keepSiteByAblations [CandidateAblationSample.mk 0 "fma" 1000 980 1 []])
        { name := "fma", params := [], retTy := .i64,
          body := .letBind 3 .i64
            (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3) } 0 =
      ({ name := "fma", params := [], retTy := .i64,
         body := .letBind 3 .i64 (.scalar (.fma (.var 0) (.var 1) (.var 2))) (.ret 3),
         assurance := .verifiedKernelProof }, [r], 1) := by
    unfold superoptDeclSelective
    dsimp only []
    rw [hcodeKeep]
    rfl
  have hdeclPrune :
      superoptDeclSelective (HardwareCostProfile.forTarget .x86_64) lbl
        (keepSiteByAblations [CandidateAblationSample.mk 0 "fma" 1000 995 1 []])
        { name := "fma", params := [], retTy := .i64,
          body := .letBind 3 .i64
            (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3) } 0 =
      ({ name := "fma", params := [], retTy := .i64,
         body := .letBind 3 .i64
           (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3),
         assurance := .verifiedKernelProof }, [], 1) := by
    unfold superoptDeclSelective
    dsimp only []
    rw [hcodePrune]
    rfl
  dsimp only []
  simp only [autotuneSuperoptModule, hp]
  simp only [pruneCandidatesByAblation, superoptModuleSelective,
    List.foldl, List.nil_append, hlbl]
  simp only [keepDeclSiteByAblations, List.filter_cons, List.filter_nil, beq_self_eq_true,
    ite_true]
  rw [hdeclKeep, hdeclPrune]
  simp [corpusCalibrationReceipt, meetsCorpusGeomeanOnePercentGain,
    corpusProdBaseline, corpusProdCandidate, aggregateCorpusTimings, hcost,
    superoptDeclSelective, superoptCodeSelective, keepSiteByAblations, candidateAblationSurvives,
    meetsOnePercentE2EGain, hlbl, hr, hr0]


end LeanNative.Proofs
