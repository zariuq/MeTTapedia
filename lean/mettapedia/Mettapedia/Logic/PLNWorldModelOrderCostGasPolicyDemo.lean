import Mettapedia.Logic.WMGasSensorDriftDemo
import Mettapedia.Logic.PLNWorldModelOrderCostAuditCertificate

/-!
# Gas-Lane Order-Cost Policy Demo (WM-PLN)

Application-lane theorem bridge for Gas Sensor Drift:

- instantiate `WorldModel` on `SensorArrayState`,
- instantiate order-cost semantics via additive merge,
- prove theorem-backed budget policy for batch-order swapping.

Because merge is additive/commutative here, the batch-order swap carries zero
schedule error at each gas query, so a zero-budget policy already passes.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.EvidenceNormalGamma
open Mettapedia.Logic.WMGasSensorDriftDemo

/-- Generic WM view for gas states: query extraction is per-gas Normal-Gamma evidence. -/
noncomputable instance instGenericWorldModelGasSensorArray :
    WorldModel SensorArrayState GasType NormalGammaEvidence where
  evidence := gasEvidence
  evidence_add := by
    intro s₁ s₂ q
    cases q <;> simp [gasEvidence]

/-- Additive overlap layer for gas-state revision (`merge = (+)`). -/
noncomputable def gasAdditiveOverlapLayer :
    OverlapLayer SensorArrayState GasType NormalGammaEvidence Unit where
  merge := fun s₁ s₂ => s₁ + s₂
  overlap := fun _ _ _ => ()
  combine := fun e₁ e₂ _ => e₁ + e₂
  independent := fun _ _ _ => True
  evidence_merge := by
    intro s₁ s₂ q
    simpa using
      (WorldModel.evidence_add'
        (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) s₁ s₂ q)
  additive_of_independent := by
    intro s₁ s₂ q _hind
    simpa using
      (WorldModel.evidence_add'
        (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) s₁ s₂ q)

/-- Gas-lane schedule error wrapper. -/
noncomputable def gasScheduleErrorCount
    (base : SensorArrayState)
    (steps₁ steps₂ : List SensorArrayState)
    (g : GasType) : ℝ≥0∞ := by
  exact
    scheduleErrorCount
      (State := SensorArrayState)
      (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
      (gasAdditiveOverlapLayer)
      base steps₁ steps₂ g

/-- Gas-lane schedule-budget predicate. -/
def gasScheduleErrorBound
    (base : SensorArrayState)
    (steps₁ steps₂ : List SensorArrayState)
    (g : GasType) (B : ℝ≥0∞) : Prop :=
  gasScheduleErrorCount base steps₁ steps₂ g ≤ B

/-- Gas governance policy: accept batch-order swap when order-cost ≤ budget. -/
def gasOrderBudgetPolicy
    (base : SensorArrayState) (g : GasType) (B : ℝ≥0∞) : Prop :=
  gasScheduleErrorBound base [batch1, batch10] [batch10, batch1] g B

/-- Batch-order swapping in the gas lane has zero schedule error (additive merge). -/
theorem gasScheduleErrorCount_batchSwap_eq_zero
    (base : SensorArrayState) (g : GasType) :
    gasScheduleErrorCount base [batch1, batch10] [batch10, batch1] g = 0 := by
  unfold gasScheduleErrorCount
  apply scheduleErrorCount_zero_of_count_eq
    (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
    (L := gasAdditiveOverlapLayer) (base := base) (steps₁ := [batch1, batch10])
    (steps₂ := [batch10, batch1]) (q := g)
  have hstate :
      runMergeSchedule
        (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
        gasAdditiveOverlapLayer base [batch1, batch10] =
      runMergeSchedule
        (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
        gasAdditiveOverlapLayer base [batch10, batch1] := by
    simp [runMergeSchedule, gasAdditiveOverlapLayer, add_comm, add_left_comm]
  exact congrArg
    (fun s =>
      scheduleObservationCount
        (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
        gasAdditiveOverlapLayer s [] g) hstate

/-- Runtime pairwise order check at zero/zero budget for gas batch-order swap. -/
theorem gasRuntimePairwiseOrderCheck_batchSwap_zero
    (base : SensorArrayState) (g : GasType) :
    RuntimePairwiseOrderCheck
      (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
      gasAdditiveOverlapLayer base [batch1, batch10] [batch10, batch1] g 0 0 := by
  unfold RuntimePairwiseOrderCheck
  have hcount :
      scheduleObservationCount
        (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
        gasAdditiveOverlapLayer base [batch1, batch10] g =
      scheduleObservationCount
        (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
        gasAdditiveOverlapLayer base [batch10, batch1] g := by
    have hstate :
        runMergeSchedule
          (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
          gasAdditiveOverlapLayer base [batch1, batch10] =
        runMergeSchedule
          (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
          gasAdditiveOverlapLayer base [batch10, batch1] := by
      simp [runMergeSchedule, gasAdditiveOverlapLayer, add_comm, add_left_comm]
    exact congrArg
      (fun s =>
        AdditiveWorldModel.queryObservationCount
          (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) s g) hstate
  constructor <;> simp [hcount]

/-- Theorem-backed gas policy threshold: zero budget already accepts batch-order swap. -/
theorem gasOrderBudgetPolicy_batchSwap_zero_via_runtimeCertificate
    (base : SensorArrayState) (g : GasType) :
    gasOrderBudgetPolicy base g 0 := by
  unfold gasOrderBudgetPolicy gasScheduleErrorBound
  exact runtimePairwiseOrderCheck_certifies_policyThreshold
    (State := SensorArrayState) (Query := GasType) (Ev := NormalGammaEvidence) (Ov := Unit)
    gasAdditiveOverlapLayer base [batch1, batch10] [batch10, batch1] g 0 0 0
    (gasRuntimePairwiseOrderCheck_batchSwap_zero (base := base) (g := g))
    (by simp)

/-- Concrete policy endpoint: ethanol query under zero budget (base = zero state). -/
theorem gasPolicy_zeroThreshold_ethanol :
    gasOrderBudgetPolicy SensorArrayState.zero GasType.ethanol 0 :=
  gasOrderBudgetPolicy_batchSwap_zero_via_runtimeCertificate
    (base := SensorArrayState.zero) (g := GasType.ethanol)

/-- Concrete policy endpoint: ammonia query under zero budget (base = zero state). -/
theorem gasPolicy_zeroThreshold_ammonia :
    gasOrderBudgetPolicy SensorArrayState.zero GasType.ammonia 0 :=
  gasOrderBudgetPolicy_batchSwap_zero_via_runtimeCertificate
    (base := SensorArrayState.zero) (g := GasType.ammonia)

/-- Concrete policy endpoint: toluene query under zero budget (base = zero state). -/
theorem gasPolicy_zeroThreshold_toluene :
    gasOrderBudgetPolicy SensorArrayState.zero GasType.toluene 0 :=
  gasOrderBudgetPolicy_batchSwap_zero_via_runtimeCertificate
    (base := SensorArrayState.zero) (g := GasType.toluene)

end Mettapedia.Logic
