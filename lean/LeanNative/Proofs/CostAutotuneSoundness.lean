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

theorem superoptModuleWithCalibratedProfile_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (m : LNIRModule) :
    ∀ d ∈ m.decls,
      ∃ d' ∈ (superoptModuleWithProfile (calibrateHardwareProfile base samples) m).1.decls,
        CodeRefines d.body d'.body :=
  superoptModuleWithProfile_sound (calibrateHardwareProfile base samples) m

theorem autotuneCodeWithAmdahl_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample) (c : LNIRCode) :
    CodeRefines c (autotuneCodeWithAmdahl base samples corpus c) := by
  unfold autotuneCodeWithAmdahl
  dsimp only []
  split
  · exact superoptCodeCore_sound _ _ _ c
  · exact CodeRefines.refl _

theorem autotuneCodeWithAmdahl_uncalibrated_preserves (base : HardwareCostProfile)
    (samples : List OpTimingSample) (c : LNIRCode) :
    autotuneCodeWithAmdahl base samples [] c = c := by
  simp [autotuneCodeWithAmdahl, corpusCalibrationReceipt]

theorem autotuneDeclWithAmdahl_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample) (d : LNIRDecl) :
    CodeRefines d.body (autotuneDeclWithAmdahl base samples corpus d).1.body := by
  unfold autotuneDeclWithAmdahl
  dsimp only []
  split
  · exact superoptDeclCore_sound _ _ d
  · exact CodeRefines.refl _

theorem autotuneSuperoptModule_sound (base : HardwareCostProfile)
    (samples : List OpTimingSample) (corpus : List CorpusTimingSample) (m : LNIRModule) :
    ∀ d ∈ m.decls, ∃ d' ∈ (autotuneSuperoptModule base samples corpus m).1.decls,
      CodeRefines d.body d'.body := by
  intro d hd
  unfold autotuneSuperoptModule pruneCandidateByAmdahl
  dsimp only []
  split
  · exact superoptModuleWithCalibratedProfile_sound base samples m d hd
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
    let bad := autotuneSuperoptModule base []
      [CorpusTimingSample.mk 1000 991 1 ""] m
    scalarExprCostWithProfile p fused < scalarExprCostWithProfile p e ∧
    good.2.accepted = true ∧
    bad.2.accepted = false ∧
    good.1.decls.map (·.body) = [.letBind 3 .i64 (.scalar fused) (.ret 3)] ∧
    bad.1 = m ∧
    good.2.profile = p ∧
    bad.2.profile = base ∧
    good.2.report.map (·.rewritesApplied) = some 1 ∧
    bad.2.report.map (·.rewritesApplied) = some 1 := by
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
  dsimp only []
  simp only [autotuneSuperoptModule, pruneCandidateByAmdahl, superoptModuleWithProfile,
    superoptModuleCore, List.foldl, List.nil_append, superoptDeclCore,
    superoptCodeCore, superoptScalarExprCore, hp]
  have htgt : (HardwareCostProfile.forTarget .x86_64).target = .x86_64 := rfl
  simp only [htgt, hcands]
  refine ⟨by decide, by decide, by decide, ?_, ?_, by decide, by decide, by decide, by decide⟩
  · rfl
  · rfl

end LeanNative.Proofs
