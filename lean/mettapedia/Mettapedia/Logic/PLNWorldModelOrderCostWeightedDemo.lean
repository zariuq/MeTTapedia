import Mettapedia.Logic.EvidenceWeightedNormalGamma
import Mettapedia.Logic.PLNWorldModelOrderCostBounds

/-!
# Weighted Numeric Order-Cost Demo (WM-PLN)

Concrete numeric variant of the order-cost surface using weighted evidence:

- state: query-indexed `WeightedNormalGammaEvidence`,
- merge policy: right-biased (`latest-wins`),
- anomaly/schedule metrics: `SwapAnomalyCount` and `scheduleErrorCount`.

Unlike the `Which`-top demo, this lane carries finite numeric counts
(`ℝ≥0∞`) induced from effective sample weights.
-/

namespace Mettapedia.Logic

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.ConjugateEvidenceSurface
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.EvidenceWeightedNormalGamma
open Mettapedia.Logic.EvidenceWeightedNormalGamma.WeightedNormalGammaEvidence

/-- Query-indexed weighted state. -/
abbrev WeightedQueryState (Query : Type*) := Query → WeightedNormalGammaEvidence

instance instAddCommMonoidWeightedQueryState {Query : Type*} :
    AddCommMonoid (WeightedQueryState Query) := by
  dsimp [WeightedQueryState]
  infer_instance

instance instEvidenceTypeWeightedQueryState {Query : Type*} :
    EvidenceType (WeightedQueryState Query) :=
  { (inferInstance : AddCommMonoid (WeightedQueryState Query)) with }

instance instGenericWorldModelWeightedQueryState {Query : Type*} :
    WorldModel (WeightedQueryState Query) Query WeightedNormalGammaEvidence where
  evidence S q := S q
  evidence_add W₁ W₂ q := Pi.add_apply W₁ W₂ q

/-- Right-biased weighted merge (`latest-wins`). -/
def weightedRightBiasMerge {Query : Type*}
    (_I₁ I₂ : WeightedQueryState Query) : WeightedQueryState Query :=
  I₂

/-- Overlap layer induced by right-biased weighted merge. -/
noncomputable def weightedRightBiasOverlapLayer {Query : Type*} :
    OverlapLayer (WeightedQueryState Query) Query WeightedNormalGammaEvidence Unit where
  merge := weightedRightBiasMerge
  overlap := fun _ _ _ => ()
  combine := fun _ e₂ _ => e₂
  independent := fun I₁ _ q => I₁ q = 0
  evidence_merge := by
    intro I₁ I₂ q
    simp [weightedRightBiasMerge]
  additive_of_independent := by
    intro I₁ I₂ q hleft
    have hleftE :
        AdditiveWorldModel.extract
          (State := WeightedQueryState Query)
          (Query := Query) (Ev := WeightedNormalGammaEvidence) I₁ q = 0 := by
      simpa using hleft
    simp [weightedRightBiasMerge, hleftE]

/-- Concrete weighted swap anomaly count. -/
noncomputable def weightedSwapAnomalyCount {Query : Type*}
    (I₁ I₂ : WeightedQueryState Query) (q : Query) : ℝ≥0∞ := by
  exact
    SwapAnomalyCount
      (State := WeightedQueryState Query)
      (Query := Query) (Ev := WeightedNormalGammaEvidence) (Ov := Unit)
      (weightedRightBiasOverlapLayer (Query := Query)) I₁ I₂ q

/-- Concrete weighted schedule error count. -/
noncomputable def weightedScheduleErrorCount {Query : Type*}
    (base : WeightedQueryState Query)
    (steps₁ steps₂ : List (WeightedQueryState Query))
    (q : Query) : ℝ≥0∞ := by
  exact
    scheduleErrorCount
      (State := WeightedQueryState Query)
      (Query := Query) (Ev := WeightedNormalGammaEvidence) (Ov := Unit)
      (weightedRightBiasOverlapLayer (Query := Query))
      base steps₁ steps₂ q

/-- Weighted schedule-budget policy predicate. -/
def weightedScheduleErrorBound {Query : Type*}
    (base : WeightedQueryState Query)
    (steps₁ steps₂ : List (WeightedQueryState Query))
    (q : Query) (B : ℝ≥0∞) : Prop :=
  weightedScheduleErrorCount base steps₁ steps₂ q ≤ B

/-- Stable case: if both revisions agree on query `q`, weighted swap anomaly is zero. -/
theorem weightedSwapAnomalyCount_eq_zero_of_query_eq {Query : Type*}
    (I₁ I₂ : WeightedQueryState Query) (q : Query)
    (hq : I₁ q = I₂ q) :
    weightedSwapAnomalyCount I₁ I₂ q = 0 := by
  unfold weightedSwapAnomalyCount
  have hcount :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence)
        (weightedRightBiasMerge I₁ I₂) q =
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence)
        (weightedRightBiasMerge I₂ I₁) q := by
    have hqE :
        AdditiveWorldModel.extract
          (State := WeightedQueryState Query)
          (Query := Query) (Ev := WeightedNormalGammaEvidence) I₁ q =
        AdditiveWorldModel.extract
          (State := WeightedQueryState Query)
          (Query := Query) (Ev := WeightedNormalGammaEvidence) I₂ q := by
      simpa using hq
    unfold AdditiveWorldModel.queryObservationCount
    simpa [weightedRightBiasMerge] using
      congrArg ConjugateEvidence.observationCount hqE.symm
  exact swapAnomalyCount_zero_of_count_eq
    (State := WeightedQueryState Query)
    (Query := Query) (Ev := WeightedNormalGammaEvidence) (Ov := Unit)
    (L := weightedRightBiasOverlapLayer (Query := Query)) I₁ I₂ q hcount

/-- Numeric noncommutative case: zero then weighted-singleton yields anomaly exactly `w`. -/
theorem weightedSwapAnomalyCount_eq_weight_of_zero_then_single {Query : Type*}
    (I₁ I₂ : WeightedQueryState Query) (q : Query) (w : NNReal) (x : ℝ)
    (h₁ : I₁ q = 0)
    (h₂ : I₂ q = WeightedNormalGammaEvidence.single w x) :
    weightedSwapAnomalyCount I₁ I₂ q = (w : ℝ≥0∞) := by
  have hcount₁ :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence) I₁ q = 0 := by
    have h₁E :
        AdditiveWorldModel.extract
          (State := WeightedQueryState Query)
          (Query := Query) (Ev := WeightedNormalGammaEvidence) I₁ q = 0 := by
      simpa using h₁
    unfold AdditiveWorldModel.queryObservationCount
    rw [h₁E]
    exact ConjugateEvidence.observationCount_zero (Ev := WeightedNormalGammaEvidence)
  have hcount₂ :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence) I₂ q = (w : ℝ≥0∞) := by
    have h₂E :
        AdditiveWorldModel.extract
          (State := WeightedQueryState Query)
          (Query := Query) (Ev := WeightedNormalGammaEvidence) I₂ q =
        WeightedNormalGammaEvidence.single w x := by
      simpa using h₂
    unfold AdditiveWorldModel.queryObservationCount
    rw [h₂E]
    simpa using
      (WeightedNormalGammaEvidence.observationCount_single (w := w) (x := x))
  have hmerge₁₂ :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence)
        ((weightedRightBiasOverlapLayer (Query := Query)).merge I₁ I₂) q = (w : ℝ≥0∞) := by
    simpa [weightedRightBiasOverlapLayer, weightedRightBiasMerge] using hcount₂
  have hmerge₂₁ :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence)
        ((weightedRightBiasOverlapLayer (Query := Query)).merge I₂ I₁) q = 0 := by
    simpa [weightedRightBiasOverlapLayer, weightedRightBiasMerge] using hcount₁
  unfold weightedSwapAnomalyCount SwapAnomalyCount
  rw [hmerge₁₂, hmerge₂₁]
  simp

/-- Two-step order effect under right-bias: `[I₁, I₂]` vs `[I₂, I₁]` yields error `w`. -/
theorem weightedScheduleErrorCount_twoStep_eq_weight_of_zero_then_single {Query : Type*}
    (base I₁ I₂ : WeightedQueryState Query) (q : Query) (w : NNReal) (x : ℝ)
    (h₁ : I₁ q = 0)
    (h₂ : I₂ q = WeightedNormalGammaEvidence.single w x) :
    weightedScheduleErrorCount base [I₁, I₂] [I₂, I₁] q = (w : ℝ≥0∞) := by
  have hcount₁ :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence) I₁ q = 0 := by
    have h₁E :
        AdditiveWorldModel.extract
          (State := WeightedQueryState Query)
          (Query := Query) (Ev := WeightedNormalGammaEvidence) I₁ q = 0 := by
      simpa using h₁
    unfold AdditiveWorldModel.queryObservationCount
    rw [h₁E]
    exact ConjugateEvidence.observationCount_zero (Ev := WeightedNormalGammaEvidence)
  have hcount₂ :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence) I₂ q = (w : ℝ≥0∞) := by
    have h₂E :
        AdditiveWorldModel.extract
          (State := WeightedQueryState Query)
          (Query := Query) (Ev := WeightedNormalGammaEvidence) I₂ q =
        WeightedNormalGammaEvidence.single w x := by
      simpa using h₂
    unfold AdditiveWorldModel.queryObservationCount
    rw [h₂E]
    simpa using
      (WeightedNormalGammaEvidence.observationCount_single (w := w) (x := x))
  have hstep₁₂ :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence)
        ((weightedRightBiasOverlapLayer (Query := Query)).merge
          ((weightedRightBiasOverlapLayer (Query := Query)).merge base I₁) I₂) q = (w : ℝ≥0∞) := by
    simpa [weightedRightBiasOverlapLayer, weightedRightBiasMerge] using hcount₂
  have hstep₂₁ :
      AdditiveWorldModel.queryObservationCount
        (State := WeightedQueryState Query)
        (Query := Query) (Ev := WeightedNormalGammaEvidence)
        ((weightedRightBiasOverlapLayer (Query := Query)).merge
          ((weightedRightBiasOverlapLayer (Query := Query)).merge base I₂) I₁) q = 0 := by
    simpa [weightedRightBiasOverlapLayer, weightedRightBiasMerge] using hcount₁
  unfold weightedScheduleErrorCount
  rw [scheduleError_twoStep_eq_swapStepAnomalyCount
    (State := WeightedQueryState Query)
    (Query := Query) (Ev := WeightedNormalGammaEvidence) (Ov := Unit)
    (L := weightedRightBiasOverlapLayer (Query := Query))
    (base := base) (A := I₁) (B := I₂) (q := q)]
  unfold swapStepAnomalyCount
  rw [hstep₁₂, hstep₂₁]
  simp

/-- The weighted two-step order error is certified under budget `w`. -/
theorem weightedScheduleErrorBound_twoStep_weight_of_zero_then_single {Query : Type*}
    (base I₁ I₂ : WeightedQueryState Query) (q : Query) (w : NNReal) (x : ℝ)
    (h₁ : I₁ q = 0)
    (h₂ : I₂ q = WeightedNormalGammaEvidence.single w x) :
    weightedScheduleErrorBound base [I₁, I₂] [I₂, I₁] q (w : ℝ≥0∞) := by
  unfold weightedScheduleErrorBound
  rw [weightedScheduleErrorCount_twoStep_eq_weight_of_zero_then_single
      (base := base) (I₁ := I₁) (I₂ := I₂) (q := q) (w := w) (x := x) h₁ h₂]

/-- Any strictly positive weighted order error fails a zero-budget policy. -/
theorem weightedScheduleErrorBound_twoStep_not_zero_of_pos_weight {Query : Type*}
    (base I₁ I₂ : WeightedQueryState Query) (q : Query) (w : NNReal) (x : ℝ)
    (hw : 0 < w)
    (h₁ : I₁ q = 0)
    (h₂ : I₂ q = WeightedNormalGammaEvidence.single w x) :
    ¬ weightedScheduleErrorBound base [I₁, I₂] [I₂, I₁] q 0 := by
  unfold weightedScheduleErrorBound
  rw [weightedScheduleErrorCount_twoStep_eq_weight_of_zero_then_single
      (base := base) (I₁ := I₁) (I₂ := I₂) (q := q) (w := w) (x := x) h₁ h₂]
  have hw0 : (w : ℝ≥0∞) ≠ 0 := by
    simpa using (show w ≠ 0 from ne_of_gt hw)
  simp [hw0]

end Mettapedia.Logic
