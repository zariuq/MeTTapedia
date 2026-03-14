import Mettapedia.Logic.ConjugateEvidenceSurface
import Mettapedia.Logic.PLNWorldModelOverlap

/-!
# WM Quantitative Order-Cost Bounds

Quantitative upgrade over predicate-level order sensitivity:

- `SwapAnomalyCount`: symmetric magnitude of count-level order anomaly,
- `SwapAnomalyBound`: budgeted bound for one swap,
- `scheduleErrorCount`: count-level discrepancy between two schedules,
- simple bound constructors and two-step schedule-to-swap bridge.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.PLNWorldModelGeneric

section SwapAnomaly

variable {State Query Ev Ov : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [GenericWorldModel State Query Ev]

/-- Symmetric count-level anomaly of swapping merge order. -/
noncomputable def SwapAnomalyCount
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query) : ℝ≥0∞ :=
  let c₁₂ :=
    GenericWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q
  let c₂₁ :=
    GenericWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) (L.merge W₂ W₁) q
  (c₁₂ - c₂₁) + (c₂₁ - c₁₂)

/-- Budgeted bound for one swap anomaly. -/
def SwapAnomalyBound
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query) (B : ℝ≥0∞) : Prop :=
  SwapAnomalyCount (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q ≤ B

theorem swapAnomalyCount_symm
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query) :
    SwapAnomalyCount (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q =
    SwapAnomalyCount (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₂ W₁ q := by
  simp [SwapAnomalyCount, add_comm]

theorem swapAnomalyCount_zero_of_count_eq
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query)
    (hcount :
      GenericWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
      GenericWorldModel.queryObservationCount
        (State := State) (Query := Query) (Ev := Ev) (L.merge W₂ W₁) q) :
    SwapAnomalyCount (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q = 0 := by
  simp [SwapAnomalyCount, hcount]

theorem swapAnomalyCount_zero_of_commutativeMergeEvidence
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query)
    (hcomm :
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q =
      GenericWorldModel.evidence
        (State := State) (Query := Query) (Ev := Ev) (L.merge W₂ W₁) q) :
    SwapAnomalyCount (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q = 0 := by
  apply swapAnomalyCount_zero_of_count_eq
  unfold GenericWorldModel.queryObservationCount
  simpa using congrArg ConjugateEvidence.observationCount hcomm

theorem swapAnomalyBound_of_pairwise_bounds
    (L : OverlapLayer State Query Ev Ov)
    (W₁ W₂ : State) (q : Query) (B₁ B₂ : ℝ≥0∞)
    (h₁ :
      let c₁₂ :=
        GenericWorldModel.queryObservationCount
          (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q
      let c₂₁ :=
        GenericWorldModel.queryObservationCount
          (State := State) (Query := Query) (Ev := Ev) (L.merge W₂ W₁) q
      c₁₂ - c₂₁ ≤ B₁)
    (h₂ :
      let c₁₂ :=
        GenericWorldModel.queryObservationCount
          (State := State) (Query := Query) (Ev := Ev) (L.merge W₁ W₂) q
      let c₂₁ :=
        GenericWorldModel.queryObservationCount
          (State := State) (Query := Query) (Ev := Ev) (L.merge W₂ W₁) q
      c₂₁ - c₁₂ ≤ B₂) :
    SwapAnomalyBound (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L W₁ W₂ q (B₁ + B₂) := by
  simpa [SwapAnomalyBound, SwapAnomalyCount] using add_le_add h₁ h₂

end SwapAnomaly

section ScheduleError

variable {State Query Ev Ov : Type*}
variable [EvidenceType State] [ConjugateEvidence Ev] [GenericWorldModel State Query Ev]

/-- Run a merge schedule from a chosen base state. -/
def runMergeSchedule
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps : List State) : State :=
  steps.foldl L.merge base

/-- Observation count extracted after running a merge schedule. -/
noncomputable def scheduleObservationCount
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps : List State) (q : Query) : ℝ≥0∞ :=
  GenericWorldModel.queryObservationCount
    (State := State) (Query := Query) (Ev := Ev) (runMergeSchedule L base steps) q

/-- Symmetric count-level discrepancy between two schedules. -/
noncomputable def scheduleErrorCount
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query) : ℝ≥0∞ :=
  let c₁ :=
    scheduleObservationCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₁ q
  let c₂ :=
    scheduleObservationCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₂ q
  (c₁ - c₂) + (c₂ - c₁)

/-- Budgeted bound for schedule discrepancy. -/
def scheduleErrorBound
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query) (B : ℝ≥0∞) : Prop :=
  scheduleErrorCount
    (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₁ steps₂ q ≤ B

theorem scheduleErrorCount_symm
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query) :
    scheduleErrorCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₁ steps₂ q =
    scheduleErrorCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₂ steps₁ q := by
  simp [scheduleErrorCount, add_comm]

theorem scheduleErrorCount_zero_of_count_eq
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query)
    (hcount :
      scheduleObservationCount
        (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₁ q =
      scheduleObservationCount
        (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₂ q) :
    scheduleErrorCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₁ steps₂ q = 0 := by
  simp [scheduleErrorCount, hcount]

theorem scheduleErrorBound_of_pairwise_bounds
    (L : OverlapLayer State Query Ev Ov)
    (base : State) (steps₁ steps₂ : List State) (q : Query) (B₁ B₂ : ℝ≥0∞)
    (h₁ :
      let c₁ :=
        scheduleObservationCount
          (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₁ q
      let c₂ :=
        scheduleObservationCount
          (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₂ q
      c₁ - c₂ ≤ B₁)
    (h₂ :
      let c₁ :=
        scheduleObservationCount
          (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₁ q
      let c₂ :=
        scheduleObservationCount
          (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₂ q
      c₂ - c₁ ≤ B₂) :
    scheduleErrorBound
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base steps₁ steps₂ q (B₁ + B₂) := by
  simpa [scheduleErrorBound, scheduleErrorCount] using add_le_add h₁ h₂

/-- One adjacent-swap anomaly at base state `base`. -/
noncomputable def swapStepAnomalyCount
    (L : OverlapLayer State Query Ev Ov)
    (base A B : State) (q : Query) : ℝ≥0∞ :=
  let cAB :=
    GenericWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) (L.merge (L.merge base A) B) q
  let cBA :=
    GenericWorldModel.queryObservationCount
      (State := State) (Query := Query) (Ev := Ev) (L.merge (L.merge base B) A) q
  (cAB - cBA) + (cBA - cAB)

def swapStepAnomalyBound
    (L : OverlapLayer State Query Ev Ov)
    (base A B : State) (q : Query) (Bnd : ℝ≥0∞) : Prop :=
  swapStepAnomalyCount
    (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base A B q ≤ Bnd

theorem scheduleError_twoStep_eq_swapStepAnomalyCount
    (L : OverlapLayer State Query Ev Ov)
    (base A B : State) (q : Query) :
    scheduleErrorCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base [A, B] [B, A] q =
    swapStepAnomalyCount
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base A B q := by
  rfl

theorem scheduleErrorBound_twoStep_of_swapStepBound
    (L : OverlapLayer State Query Ev Ov)
    (base A B : State) (q : Query) (Bnd : ℝ≥0∞)
    (h : swapStepAnomalyBound
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) L base A B q Bnd) :
    scheduleErrorBound
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov)
      L base [A, B] [B, A] q Bnd := by
  simpa [scheduleErrorBound, scheduleError_twoStep_eq_swapStepAnomalyCount] using h

end ScheduleError

end Mettapedia.Logic
