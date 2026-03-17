import Mettapedia.Logic.PLNProvenanceWMSupportBridge
import Mettapedia.Logic.PLNWorldModelOrderCostBounds
import Provenance.Semirings.Which

/-!
# Provenance Order-Cost Demo (WM-PLN)

Concrete, provenance-backed instantiation of the quantitative order-cost layer:

- state: `KRelation σ (Which (Fin n))`,
- policy merge: right-biased (`latest-wins`) merge,
- anomaly metric: count-level `SwapAnomalyCount` / `scheduleErrorCount`
  using a `Which` count view (`0` for `wbot`, `⊤` for any `wset _`).

This gives a small but explicit application surface for the book:

- positive example (stable): equal query evidence implies zero anomaly;
- negative example (order-cost): two-step schedules can have top error under
  order reversal.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.LP

variable {σ : LPSignature} {n : ℕ}

/-- `Which` count view for order-cost auditing:
`wbot` has count `0`, every `wset _` has count `⊤`. -/
noncomputable def whichTopCountConjugateEvidence {α : Type} [DecidableEq α] :
    ConjugateEvidence (Which α) where
  observationCount
    | Which.wbot => 0
    | Which.wset _ => ⊤
  observationCount_add := by
    intro a b
    cases a with
    | wbot =>
        cases b with
        | wbot =>
            show (0 : ℝ≥0∞) = 0 + 0
            simp
        | wset sb =>
            show (⊤ : ℝ≥0∞) = 0 + ⊤
            simp
    | wset sa =>
        cases b with
        | wbot =>
            show (⊤ : ℝ≥0∞) = ⊤ + 0
            simp
        | wset sb =>
            show (⊤ : ℝ≥0∞) = ⊤ + ⊤
            simp
  observationCount_zero := by
    simp

/-- Global `ConjugateEvidence` instance for `Which` using the top-count view. -/
noncomputable instance instConjugateEvidenceWhichTopCount {α : Type} [DecidableEq α] :
    ConjugateEvidence (Which α) :=
  whichTopCountConjugateEvidence

/-- Right-biased policy merge (`latest-wins`) on provenance states. -/
def provenanceRightBiasMerge
    (_I₁ I₂ : KRelation σ (Which (Fin n))) : KRelation σ (Which (Fin n)) :=
  I₂

/-- Overlap layer induced by the right-biased policy merge. -/
noncomputable def provenanceRightBiasOverlapLayer :
    OverlapLayer (KRelation σ (Which (Fin n))) (GroundAtom σ) (Which (Fin n)) Unit where
  merge := provenanceRightBiasMerge (σ := σ) (n := n)
  overlap := fun _ _ _ => ()
  combine := fun _ e₂ _ => e₂
  independent := fun I₁ _ q => I₁ q = 0
  evidence_merge := by
    intro I₁ I₂ q
    rfl
  additive_of_independent := by
    intro I₁ I₂ q hleft
    change I₂ q = I₁ q + I₂ q
    simp [hleft]

/-- Concrete swap anomaly count for the right-biased provenance layer. -/
noncomputable def provenanceSwapAnomalyCount
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ) : ℝ≥0∞ := by
  exact
    SwapAnomalyCount
      (State := KRelation σ (Which (Fin n)))
      (Query := GroundAtom σ) (Ev := Which (Fin n)) (Ov := Unit)
      (provenanceRightBiasOverlapLayer (σ := σ) (n := n)) I₁ I₂ q

/-- Concrete schedule error count for the right-biased provenance layer. -/
noncomputable def provenanceScheduleErrorCount
    (base : KRelation σ (Which (Fin n)))
    (steps₁ steps₂ : List (KRelation σ (Which (Fin n))))
    (q : GroundAtom σ) : ℝ≥0∞ := by
  exact
    scheduleErrorCount
      (State := KRelation σ (Which (Fin n)))
      (Query := GroundAtom σ) (Ev := Which (Fin n)) (Ov := Unit)
      (provenanceRightBiasOverlapLayer (σ := σ) (n := n))
      base steps₁ steps₂ q

def provenanceScheduleErrorBound
    (base : KRelation σ (Which (Fin n)))
    (steps₁ steps₂ : List (KRelation σ (Which (Fin n))))
    (q : GroundAtom σ) (B : ℝ≥0∞) : Prop :=
  provenanceScheduleErrorCount (σ := σ) (n := n) base steps₁ steps₂ q ≤ B

/-- Positive example:
if the two revisions agree on query `q`, swap anomaly is zero. -/
theorem provenanceSwapAnomalyCount_eq_zero_of_query_eq
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (hq : I₁ q = I₂ q) :
    provenanceSwapAnomalyCount (σ := σ) (n := n) I₁ I₂ q = 0 := by
  unfold provenanceSwapAnomalyCount
  have hcount :
      AdditiveWorldModel.queryObservationCount
        (State := KRelation σ (Which (Fin n)))
        (Query := GroundAtom σ) (Ev := Which (Fin n))
        (provenanceRightBiasMerge (σ := σ) (n := n) I₁ I₂) q =
      AdditiveWorldModel.queryObservationCount
        (State := KRelation σ (Which (Fin n)))
        (Query := GroundAtom σ) (Ev := Which (Fin n))
        (provenanceRightBiasMerge (σ := σ) (n := n) I₂ I₁) q := by
    simpa [AdditiveWorldModel.queryObservationCount, provenanceRightBiasMerge] using
      congrArg ConjugateEvidence.observationCount hq.symm
  exact swapAnomalyCount_zero_of_count_eq
    (State := KRelation σ (Which (Fin n)))
    (Query := GroundAtom σ) (Ev := Which (Fin n)) (Ov := Unit)
    (L := provenanceRightBiasOverlapLayer (σ := σ) (n := n)) I₁ I₂ q hcount

/-- Policy/order-cost example:
if `I₁` is zero and `I₂` is nonzero at `q`, swapping order has top anomaly. -/
theorem provenanceSwapAnomalyCount_eq_top_of_zero_then_nonzero
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (h₁ : I₁ q = 0) (h₂ : I₂ q ≠ 0) :
    provenanceSwapAnomalyCount (σ := σ) (n := n) I₁ I₂ q = ⊤ := by
  have hcount₁ :
      AdditiveWorldModel.queryObservationCount
        (State := KRelation σ (Which (Fin n)))
        (Query := GroundAtom σ) (Ev := Which (Fin n)) I₁ q = 0 := by
    simpa [AdditiveWorldModel.queryObservationCount] using
      congrArg ConjugateEvidence.observationCount h₁
  cases hI₂ : I₂ q with
  | wbot =>
      exfalso
      have hzero : I₂ q = (0 : Which (Fin n)) := by
        rw [hI₂]
        rfl
      exact h₂ hzero
  | wset s =>
      have hcount₂ :
          AdditiveWorldModel.queryObservationCount
            (State := KRelation σ (Which (Fin n)))
            (Query := GroundAtom σ) (Ev := Which (Fin n)) I₂ q = ⊤ := by
        unfold AdditiveWorldModel.queryObservationCount
        change ConjugateEvidence.observationCount (I₂ q) = ⊤
        rw [hI₂]
        rfl
      have hmerge₁₂ :
          AdditiveWorldModel.queryObservationCount
            (State := KRelation σ (Which (Fin n)))
            (Query := GroundAtom σ) (Ev := Which (Fin n))
            ((provenanceRightBiasOverlapLayer (σ := σ) (n := n)).merge I₁ I₂) q = ⊤ := by
        simpa [provenanceRightBiasOverlapLayer, provenanceRightBiasMerge] using hcount₂
      have hmerge₂₁ :
          AdditiveWorldModel.queryObservationCount
            (State := KRelation σ (Which (Fin n)))
            (Query := GroundAtom σ) (Ev := Which (Fin n))
            ((provenanceRightBiasOverlapLayer (σ := σ) (n := n)).merge I₂ I₁) q = 0 := by
        simpa [provenanceRightBiasOverlapLayer, provenanceRightBiasMerge] using hcount₁
      unfold provenanceSwapAnomalyCount SwapAnomalyCount
      rw [hmerge₁₂, hmerge₂₁]
      simp

/-- Two-step schedule order effect for right-biased policy:
`[I₁, I₂]` vs `[I₂, I₁]` can have top schedule error. -/
theorem provenanceScheduleErrorCount_twoStep_eq_top_of_zero_then_nonzero
    (base I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (h₁ : I₁ q = 0) (h₂ : I₂ q ≠ 0) :
    provenanceScheduleErrorCount (σ := σ) (n := n) base [I₁, I₂] [I₂, I₁] q = ⊤ := by
  have hcount₁ :
      AdditiveWorldModel.queryObservationCount
        (State := KRelation σ (Which (Fin n)))
        (Query := GroundAtom σ) (Ev := Which (Fin n)) I₁ q = 0 := by
    simpa [AdditiveWorldModel.queryObservationCount] using
      congrArg ConjugateEvidence.observationCount h₁
  cases hI₂ : I₂ q with
  | wbot =>
      exfalso
      have hzero : I₂ q = (0 : Which (Fin n)) := by
        rw [hI₂]
        rfl
      exact h₂ hzero
  | wset s =>
      have hcount₂ :
          AdditiveWorldModel.queryObservationCount
            (State := KRelation σ (Which (Fin n)))
            (Query := GroundAtom σ) (Ev := Which (Fin n)) I₂ q = ⊤ := by
        unfold AdditiveWorldModel.queryObservationCount
        change ConjugateEvidence.observationCount (I₂ q) = ⊤
        rw [hI₂]
        rfl
      have hstep₁₂ :
          AdditiveWorldModel.queryObservationCount
            (State := KRelation σ (Which (Fin n)))
            (Query := GroundAtom σ) (Ev := Which (Fin n))
            ((provenanceRightBiasOverlapLayer (σ := σ) (n := n)).merge
              ((provenanceRightBiasOverlapLayer (σ := σ) (n := n)).merge base I₁) I₂) q = ⊤ := by
        simpa [provenanceRightBiasOverlapLayer, provenanceRightBiasMerge] using hcount₂
      have hstep₂₁ :
          AdditiveWorldModel.queryObservationCount
            (State := KRelation σ (Which (Fin n)))
            (Query := GroundAtom σ) (Ev := Which (Fin n))
            ((provenanceRightBiasOverlapLayer (σ := σ) (n := n)).merge
              ((provenanceRightBiasOverlapLayer (σ := σ) (n := n)).merge base I₂) I₁) q = 0 := by
        simpa [provenanceRightBiasOverlapLayer, provenanceRightBiasMerge] using hcount₁
      unfold provenanceScheduleErrorCount
      rw [scheduleError_twoStep_eq_swapStepAnomalyCount
        (State := KRelation σ (Which (Fin n)))
        (Query := GroundAtom σ) (Ev := Which (Fin n)) (Ov := Unit)
        (L := provenanceRightBiasOverlapLayer (σ := σ) (n := n))
        (base := base) (A := I₁) (B := I₂) (q := q)]
      unfold swapStepAnomalyCount
      rw [hstep₁₂, hstep₂₁]
      simp

/-- Top-budget schedule bound (always true once top error is established). -/
theorem provenanceScheduleErrorBound_twoStep_top_of_zero_then_nonzero
    (base I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (h₁ : I₁ q = 0) (h₂ : I₂ q ≠ 0) :
    provenanceScheduleErrorBound (σ := σ) (n := n) base [I₁, I₂] [I₂, I₁] q ⊤ := by
  unfold provenanceScheduleErrorBound
  have htop :
      provenanceScheduleErrorCount (σ := σ) (n := n) base [I₁, I₂] [I₂, I₁] q = ⊤ :=
    provenanceScheduleErrorCount_twoStep_eq_top_of_zero_then_nonzero
      (σ := σ) (n := n) base I₁ I₂ q h₁ h₂
  simp [htop]

/-- Zero budget is insufficient in the same noncommutative two-step scenario. -/
theorem provenanceScheduleErrorBound_twoStep_not_zero_of_zero_then_nonzero
    (base I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (h₁ : I₁ q = 0) (h₂ : I₂ q ≠ 0) :
    ¬ provenanceScheduleErrorBound (σ := σ) (n := n) base [I₁, I₂] [I₂, I₁] q 0 := by
  unfold provenanceScheduleErrorBound
  rw [provenanceScheduleErrorCount_twoStep_eq_top_of_zero_then_nonzero
      (σ := σ) (n := n) base I₁ I₂ q h₁ h₂]
  simp

end Mettapedia.Logic
