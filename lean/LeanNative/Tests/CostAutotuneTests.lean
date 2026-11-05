import LeanNative.Core

namespace LeanNative.Tests.CostAutotuneTests

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Proofs
open LeanNative.Transform

def zen5Preset : HardwareCostProfile :=
  (calibrationPreset "zen5").getD (HardwareCostProfile.forTarget .x86_64)

def neoversePreset : HardwareCostProfile :=
  (calibrationPreset "neoverse").getD (HardwareCostProfile.forTarget .arm64)

def scalewayPreset : HardwareCostProfile :=
  (calibrationPreset "scaleway").getD (HardwareCostProfile.forTarget .arm64)

def rtx4090Preset : HardwareCostProfile :=
  (calibrationPreset "rtx4090").getD (HardwareCostProfile.forTarget .cuda_ptx)

def sm89Preset : HardwareCostProfile :=
  (calibrationPreset "sm_89").getD (HardwareCostProfile.forTarget .cuda_ptx)

def sm90Preset : HardwareCostProfile :=
  (calibrationPreset "sm_90").getD (HardwareCostProfile.forTarget .cuda_ptx)

def zen5Samples : List OpTimingSample :=
  [ { operation := "add", elapsedNs := 100, iterations := 100 }
  , { operation := "add", elapsedNs := 100, iterations := 100 }
  , { operation := "add", elapsedNs := 900, iterations := 100 }
  , { operation := "bitwise", elapsedNs := 100, iterations := 100 }
  , { operation := "shift", elapsedNs := 100, iterations := 100 }
  , { operation := "cmp", elapsedNs := 100, iterations := 100 }
  , { operation := "mul", elapsedNs := 300, iterations := 100 }
  , { operation := "div", elapsedNs := 1800, iterations := 100 }
  , { operation := "fma", elapsedNs := 400, iterations := 100 }
  , { operation := "select", elapsedNs := 200, iterations := 100 }
  , { operation := "clz256", elapsedNs := 300, iterations := 100 }
  , { operation := "add_sub_checked256", elapsedNs := 400, iterations := 100 }
  , { operation := "mul_checked256", elapsedNs := 600, iterations := 100 }
  , { operation := "min_gpu_elements", elapsedNs := 131072, iterations := 1 }
  , { operation := "gpu_block_threads", elapsedNs := 512, iterations := 1 }
  , { operation := "matmul_tile_dim", elapsedNs := 32, iterations := 1 } ]

def cudaHeavyFmaSamples : List OpTimingSample :=
  [ { operation := "add", elapsedNs := 100, iterations := 100 }
  , { operation := "mul", elapsedNs := 200, iterations := 100 }
  , { operation := "fma", elapsedNs := 200, iterations := 100 } ]

def slowFmaSamples : List OpTimingSample :=
  [ { operation := "add", elapsedNs := 100, iterations := 100 }
  , { operation := "mul", elapsedNs := 200, iterations := 100 }
  , { operation := "fma", elapsedNs := 500, iterations := 100 } ]

def fmaDecl : LNIRDecl := {
  name := "autotune_fma"
  params := [ { id := 0, name := "a", ty := .i64, borrow := false }
            , { id := 1, name := "b", ty := .i64, borrow := false }
            , { id := 2, name := "c", ty := .i64, borrow := false } ]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body := .letBind 3 .i64 (.scalar (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2))) (.ret 3)
}

def noopDecl : LNIRDecl := {
  name := "autotune_noop"
  params := [{ id := 0, name := "x", ty := .i64, borrow := false }]
  retTy := .i64
  assurance := .verifiedKernelProof
  isGpuCand := false
  body := .ret 0
}

def fmaModule : LNIRModule := { moduleName := "LeanNative.Tests.AutotuneFma", decls := [fmaDecl] }
def noopModule : LNIRModule := { moduleName := "LeanNative.Tests.AutotuneNoop", decls := [noopDecl] }

def evalDeclU64 (d : LNIRDecl) (a b c : UInt64) : Option UInt64 :=
  let env := (((VarEnv.empty).bind 0 (.u64 a)).bind 1 (.u64 b)).bind 2 (.u64 c)
  match evalCode 64 env HeapState.empty d.body with
  | .ok (.u64 v, _) => some v
  | _ => none

#guard zen5Preset.target == .x86_64
#guard neoversePreset.target == .arm64
#guard scalewayPreset.target == .arm64
#guard rtx4090Preset.target == .cuda_ptx
#guard sm89Preset.smArch == "sm_89"
#guard sm90Preset.smArch == "sm_90"

#guard (let cal := calibrateHardwareProfile zen5Preset zen5Samples
        cal.target == .x86_64 && cal.mulCost == 3 && cal.divModCost == 18 &&
        cal.fmaCost == 4 && cal.minGpuElements == 131072 &&
        cal.gpuBlockThreads == 512 && cal.matmulTileDim == 32)

#guard (let cal := calibrateHardwareProfile zen5Preset zen5Samples
        HardwareCostProfile.fromJson? cal.toJson == some cal)
#guard (HardwareCostProfile.fromJson? neoversePreset.toJson == some neoversePreset)
#guard (HardwareCostProfile.fromJson? scalewayPreset.toJson == some scalewayPreset)
#guard (HardwareCostProfile.fromJson? rtx4090Preset.toJson == some rtx4090Preset)
#guard (HardwareCostProfile.fromJson? sm90Preset.toJson == some sm90Preset)

#guard (let fastP := calibrateHardwareProfile sm90Preset cudaHeavyFmaSamples
        let slowP := calibrateHardwareProfile zen5Preset slowFmaSamples
        let (fastM, fastRep) := superoptModuleWithProfile fastP fmaModule
        let (slowM, slowRep) := superoptModuleWithProfile slowP fmaModule
        fastRep.rewritesApplied == 1 && slowRep.rewritesApplied == 0 && fastM != slowM)

#guard meetsOnePercentE2EGain 1000 990 == true
#guard meetsOnePercentE2EGain 1000 991 == false
#guard meetsOnePercentE2EGain 0 0 == false

#guard (let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 990, hits := 1 }] fmaModule
        r.accepted == true && m' != fmaModule && r.profile == calibrateHardwareProfile sm90Preset cudaHeavyFmaSamples)

#guard (let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 991, hits := 1 }] fmaModule
        r.accepted == false && m' == fmaModule && r.profile == sm90Preset)

#guard (let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 900, hits := 0 }] fmaModule
        r.accepted == false && m' == fmaModule && r.profile == sm90Preset)

#guard (let (m', r) := autotuneSuperoptModule sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 900, hits := 1 }] noopModule
        r.accepted == false && m' == noopModule && r.profile == sm90Preset)

#guard (let (d', r) := autotuneDeclWithAmdahl sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 990, hits := 1, declName := "autotune_fma" }] fmaDecl
        r.accepted == true &&
        evalDeclU64 fmaDecl 7 11 13 == evalDeclU64 d' 7 11 13 &&
        evalDeclU64 d' 7 11 13 == some 90)

#guard (let (d', cert) := costAutotunePass.runDecl fmaDecl
        cert.changed == false && d' == fmaDecl && cert.assurance == .verifiedKernelProof)

#guard (let calPass := costAutotunePassFor sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 990, hits := 1 }]
        let (d', cert) := calPass.runDecl fmaDecl
        cert.changed == true && d' != fmaDecl && cert.assurance == .verifiedKernelProof &&
        evalDeclU64 fmaDecl 7 11 13 == evalDeclU64 d' 7 11 13)

#guard (let subPass := costAutotunePassFor sm90Preset cudaHeavyFmaSamples
          [{ baselineNs := 1000, candidateNs := 991, hits := 1 }]
        let (d', cert) := subPass.runDecl fmaDecl
        cert.changed == false && d' == fmaDecl && cert.assurance == .verifiedKernelProof)

#guard (let m := mkCanonicalBenchmarkModule8
        (LeanNative.Driver.CostAutotuneCLI.verifyAndAccumulateCorpus m m 128).isOk)

#guard (let m := mkCanonicalBenchmarkModule8
        let mutatedDecls := m.decls.map fun d =>
          if d.name == "collatz_steps" then
            { d with body := .letBind 99 .i64 (.scalar (.constU64 777777)) (.ret 99) }
          else d
        let badMod : LNIRModule := { m with decls := mutatedDecls }
        !(LeanNative.Driver.CostAutotuneCLI.verifyAndAccumulateCorpus m badMod 128).isOk)

#guard isRegisteredTheorem "LeanNative.Proofs.calibrateHardwareProfile_preserves_target" == true
#guard isRegisteredTheorem "LeanNative.Proofs.meetsOnePercentE2EGain_iff" == true
#guard isRegisteredTheorem "LeanNative.Proofs.meetsOnePercentE2EGain_rejects_subthreshold" == true
#guard isRegisteredTheorem "LeanNative.Proofs.superoptModuleWithCalibratedProfile_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.autotuneCodeWithAmdahl_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.autotuneCodeWithAmdahl_uncalibrated_preserves" == true
#guard isRegisteredTheorem "LeanNative.Proofs.autotuneDeclWithAmdahl_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.autotuneSuperoptModule_sound" == true
#guard isRegisteredTheorem "LeanNative.Proofs.costAutotune_amdahl_gate_nonvacuous" == true

end LeanNative.Tests.CostAutotuneTests
