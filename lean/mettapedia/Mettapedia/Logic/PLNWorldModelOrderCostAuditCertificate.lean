import Mettapedia.Logic.PLNWorldModelOrderCostBounds

/-!
# WM Order-Cost Audit Certificates

Bridge from runtime-facing order checks to theorem-level schedule budgets.

This module provides small certificate theorems:

- pairwise runtime difference checks certify `scheduleErrorBound`,
- threshold monotonicity promotes certified bounds to policy thresholds,
- swap-step checks certify the corresponding two-step schedule policy.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.PLNWorldModelGeneric

variable {State Query Ev Ov : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [AdditiveWorldModel State Query Ev]

/-- Runtime pairwise order check: both directed count gaps are bounded. -/
def RuntimePairwiseOrderCheck
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query)
    (B₁ B₂ : ℝ≥0∞) : Prop :=
  let c₁ :=
    scheduleObservationCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base steps₁ q
  let c₂ :=
    scheduleObservationCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base steps₂ q
  c₁ - c₂ ≤ B₁ ∧ c₂ - c₁ ≤ B₂

/-- Runtime policy pass condition at budget `B`. -/
def RuntimeBudgetPolicyPass
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query)
    (B : ℝ≥0∞) : Prop :=
  scheduleErrorBound
    (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
    L base steps₁ steps₂ q B

/-- Runtime pairwise checks certify a theorem-level schedule bound. -/
theorem runtimePairwiseOrderCheck_certifies_scheduleErrorBound
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query)
    (B₁ B₂ : ℝ≥0∞)
    (hcheck : RuntimePairwiseOrderCheck
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base steps₁ steps₂ q B₁ B₂) :
    RuntimeBudgetPolicyPass
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base steps₁ steps₂ q (B₁ + B₂) := by
  unfold RuntimePairwiseOrderCheck at hcheck
  unfold RuntimeBudgetPolicyPass
  exact scheduleErrorBound_of_pairwise_bounds
    (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
    L base steps₁ steps₂ q B₁ B₂ hcheck.1 hcheck.2

/-- Certified schedule bounds can be promoted to larger policy thresholds. -/
theorem runtimePairwiseOrderCheck_certifies_policyThreshold
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query)
    (B₁ B₂ B : ℝ≥0∞)
    (hcheck : RuntimePairwiseOrderCheck
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base steps₁ steps₂ q B₁ B₂)
    (hbudget : B₁ + B₂ ≤ B) :
    RuntimeBudgetPolicyPass
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base steps₁ steps₂ q B := by
  unfold RuntimeBudgetPolicyPass
  exact le_trans
    (runtimePairwiseOrderCheck_certifies_scheduleErrorBound
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base steps₁ steps₂ q B₁ B₂ hcheck)
    hbudget

/-- Runtime swap-step check for one adjacent inversion. -/
def RuntimeSwapStepCheck
    (L : OverlapLayer State Query Ev Ov)
    (base A B : State) (q : Query)
    (Bnd : ℝ≥0∞) : Prop :=
  swapStepAnomalyBound
    (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
    L base A B q Bnd

/-- Swap-step runtime checks certify the corresponding two-step schedule policy. -/
theorem runtimeSwapStepCheck_certifies_twoStepPolicyThreshold
    (L : OverlapLayer State Query Ev Ov)
    (base A B : State) (q : Query)
    (Bnd : ℝ≥0∞)
    (hcheck : RuntimeSwapStepCheck
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base A B q Bnd) :
    RuntimeBudgetPolicyPass
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base [A, B] [B, A] q Bnd := by
  unfold RuntimeBudgetPolicyPass RuntimeSwapStepCheck at *
  exact scheduleErrorBound_twoStep_of_swapStepBound
    (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
    L base A B q Bnd hcheck

end Mettapedia.Logic
