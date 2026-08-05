import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.FairSafety

/-!
# Optimal survival-priority under explicit calibration assumptions

At equal visible candidate cost, expected exact discoveries are additive in
the candidates' true success probabilities.  A threshold-separated top set
therefore maximizes that expectation when the score is calibrated to those
probabilities.  The theorem is deliberately conditional: a two-candidate
fixture shows that a reversed calibration reverses the ranking.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping

open Finset BigOperators

variable {Candidate : Type*} [DecidableEq Candidate]

/-- Expected number of exact checker successes for a finite candidate set. -/
def expectedExactDiscoveries
    (successProbability : Candidate → ℝ) (selected : Finset Candidate) : ℝ :=
  ∑ candidate ∈ selected, successProbability candidate

/-- The selected set consists of candidates on or above a common score
threshold, while every unselected candidate in the visible pool is on or
below it. -/
def ThresholdSeparated
    (score : Candidate → ℝ) (pool selected : Finset Candidate)
    (threshold : ℝ) : Prop :=
  selected ⊆ pool ∧
    (∀ candidate ∈ selected, threshold ≤ score candidate) ∧
    (∀ candidate ∈ pool, candidate ∉ selected → score candidate ≤ threshold)

/-- Equal visible cost is represented by equal finite submission counts. -/
def EqualVisibleCost (left right : Finset Candidate) : Prop :=
  left.card = right.card

private theorem sum_sdiff_decomposition
    (score : Candidate → ℝ) (left right : Finset Candidate) :
    (∑ candidate ∈ left, score candidate) =
      (∑ candidate ∈ left ∩ right, score candidate) +
        ∑ candidate ∈ left \ right, score candidate := by
  rw [← Finset.sum_union]
  · congr 1
    ext candidate
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · apply Finset.disjoint_left.mpr
    intro candidate hinter hdiff
    exact (Finset.mem_sdiff.mp hdiff).2 (Finset.mem_inter.mp hinter).2

private theorem card_sdiff_eq_card_sdiff_of_card_eq
    {left right : Finset Candidate} (hcard : left.card = right.card) :
    (left \ right).card = (right \ left).card := by
  have hleft := Finset.card_sdiff_add_card_inter left right
  have hright := Finset.card_sdiff_add_card_inter right left
  rw [Finset.inter_comm right left] at hright
  omega

/-- Exchange theorem: a threshold-separated top set maximizes total score
among every equal-cardinality subset of the same visible pool. -/
theorem thresholdSeparated_maximizes_sum
    (score : Candidate → ℝ) (pool chosen alternative : Finset Candidate)
    (threshold : ℝ)
    (htop : ThresholdSeparated score pool chosen threshold)
    (haltSubset : alternative ⊆ pool)
    (hcost : EqualVisibleCost chosen alternative) :
    (∑ candidate ∈ alternative, score candidate) ≤
      ∑ candidate ∈ chosen, score candidate := by
  have hcard : (chosen \ alternative).card = (alternative \ chosen).card :=
    card_sdiff_eq_card_sdiff_of_card_eq hcost
  have hlower : ((chosen \ alternative).card : ℝ) * threshold ≤
      ∑ candidate ∈ chosen \ alternative, score candidate := by
    calc
      ((chosen \ alternative).card : ℝ) * threshold =
          ∑ _candidate ∈ chosen \ alternative, threshold := by simp
      _ ≤ _ := Finset.sum_le_sum fun candidate hcandidate ↦
        htop.2.1 candidate (Finset.mem_sdiff.mp hcandidate).1
  have hupper : (∑ candidate ∈ alternative \ chosen, score candidate) ≤
      ((alternative \ chosen).card : ℝ) * threshold := by
    calc
      (∑ candidate ∈ alternative \ chosen, score candidate) ≤
          ∑ _candidate ∈ alternative \ chosen, threshold :=
        Finset.sum_le_sum fun candidate hcandidate ↦
          htop.2.2 candidate
            (haltSubset (Finset.mem_sdiff.mp hcandidate).1)
            (Finset.mem_sdiff.mp hcandidate).2
      _ = ((alternative \ chosen).card : ℝ) * threshold := by simp
  have hexchanged :
      (∑ candidate ∈ alternative \ chosen, score candidate) ≤
        ∑ candidate ∈ chosen \ alternative, score candidate := by
    rw [hcard] at hlower
    exact le_trans hupper hlower
  rw [sum_sdiff_decomposition score alternative chosen,
    sum_sdiff_decomposition score chosen alternative,
    Finset.inter_comm alternative chosen]
  simpa [add_comm] using
    add_le_add_left hexchanged
      (∑ candidate ∈ chosen ∩ alternative, score candidate)

/-- Calibrated survival probability is therefore an optimal priority score
inside the equal-cost, visible-pool model. -/
theorem expectedExactDiscoveries_le_of_thresholdSeparated
    (predictedSurvival trueSuccess : Candidate → ℝ)
    (pool chosen alternative : Finset Candidate) (threshold : ℝ)
    (hcalibrated : ∀ candidate ∈ pool,
      predictedSurvival candidate = trueSuccess candidate)
    (htop : ThresholdSeparated predictedSurvival pool chosen threshold)
    (haltSubset : alternative ⊆ pool)
    (hcost : EqualVisibleCost chosen alternative) :
    expectedExactDiscoveries trueSuccess alternative ≤
      expectedExactDiscoveries trueSuccess chosen := by
  have hchosen : ∀ candidate ∈ chosen,
      predictedSurvival candidate = trueSuccess candidate := fun candidate hc ↦
    hcalibrated candidate (htop.1 hc)
  have halt : ∀ candidate ∈ alternative,
      predictedSurvival candidate = trueSuccess candidate := fun candidate hc ↦
    hcalibrated candidate (haltSubset hc)
  unfold expectedExactDiscoveries
  calc
    (∑ candidate ∈ alternative, trueSuccess candidate) =
        ∑ candidate ∈ alternative, predictedSurvival candidate := by
      apply Finset.sum_congr rfl
      intro candidate hcandidate
      exact (halt candidate hcandidate).symm
    _ ≤ ∑ candidate ∈ chosen, predictedSurvival candidate :=
      thresholdSeparated_maximizes_sum predictedSurvival pool chosen
        alternative threshold htop haltSubset hcost
    _ = ∑ candidate ∈ chosen, trueSuccess candidate := by
      apply Finset.sum_congr rfl
      intro candidate hcandidate
      exact hchosen candidate hcandidate

/-! ## Miscalibration counterexample -/

def reversedPrediction : Bool → ℝ
  | false => 1
  | true => 0

def actualSuccess : Bool → ℝ
  | false => 0
  | true => 1

theorem reversedCalibration_selects_strictly_worse_candidate :
    ThresholdSeparated reversedPrediction {false, true} {false} (1 / 2) ∧
      EqualVisibleCost ({false} : Finset Bool) {true} ∧
      expectedExactDiscoveries actualSuccess {false} <
        expectedExactDiscoveries actualSuccess {true} := by
  constructor
  · constructor
    · simp
    · constructor
      · intro candidate hcandidate
        simp at hcandidate
        subst candidate
        norm_num [reversedPrediction]
      · intro candidate huniverse hnot
        fin_cases candidate <;> simp_all [reversedPrediction]
  · constructor
    · rfl
    · norm_num [expectedExactDiscoveries, actualSuccess]

#print axioms thresholdSeparated_maximizes_sum
#print axioms expectedExactDiscoveries_le_of_thresholdSeparated
#print axioms reversedCalibration_selects_strictly_worse_candidate

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping
