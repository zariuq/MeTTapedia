import Mathlib.Tactic

/-!
# Uniform-block expected descent

Randomized block-coordinate convergence theorems require more than a sparse
update rule: every reachable state must satisfy a one-step expected decrease
bound under the declared block distribution.  This file isolates that finite
probabilistic spine without assuming that an arbitrary nonlinear neural
settling map is convex or contractive.

The main theorem turns a statewise uniform-block contraction into a geometric
bound on the recursively averaged gap.  A second theorem derives that
contraction from per-block decrease certificates plus an aggregate-benefit
bound.  A two-coordinate quadratic supplies a nontrivial exact instance,
whereas an identity update shows that merely sampling every block does not
imply contraction.

This is the expectation layer used by randomized block-coordinate descent.
A concrete predictive-coding solver must still prove the appropriate local
smoothness, separability, and aggregate-benefit premises for its own update
map.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace UniformBlockExpectedDescent

universe u v

variable {Block : Type u} {State : Type v}
  [Fintype Block] [Nonempty Block]

/-- Arithmetic mean of a real observable over the finite block set. -/
noncomputable def uniformAverage (value : Block → ℝ) : ℝ :=
  (∑ block, value block) / Fintype.card Block

/-- Recursively averaged gap after independent uniform block choices.  This
definition is an exact finite expectation, not a sampling approximation. -/
noncomputable def meanGapAfter
    (step : Block → State → State) (gap : State → ℝ) :
    ℕ → State → ℝ
  | 0, state => gap state
  | rounds + 1, state =>
      uniformAverage (fun block =>
        meanGapAfter step gap rounds (step block state))

/-- The one-step contract that a concrete block solver must discharge. -/
def HasUniformOneStepContraction
    (step : Block → State → State) (gap : State → ℝ)
    (rate : ℝ) : Prop :=
  ∀ state,
    uniformAverage (fun block => gap (step block state)) ≤
      rate * gap state

theorem card_blocks_pos : 0 < Fintype.card Block :=
  Fintype.card_pos

omit [Nonempty Block] in
theorem uniformAverage_mono
    {left right : Block → ℝ}
    (h : ∀ block, left block ≤ right block) :
    uniformAverage left ≤ uniformAverage right := by
  unfold uniformAverage
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun block _ => h block)
    (Nat.cast_nonneg _)

theorem uniformAverage_const (value : ℝ) :
    uniformAverage (fun _ : Block => value) = value := by
  have hcard : (Fintype.card Block : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (card_blocks_pos (Block := Block)))
  simp [uniformAverage, hcard]

theorem uniformAverage_const_sub (value : ℝ) (benefit : Block → ℝ) :
    uniformAverage (fun block => value - benefit block) =
      value - uniformAverage benefit := by
  have hcard : (Fintype.card Block : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (card_blocks_pos (Block := Block)))
  simp only [uniformAverage, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ]
  field_simp
  ring

omit [Nonempty Block] in
theorem uniformAverage_const_mul (scale : ℝ) (value : Block → ℝ) :
    uniformAverage (fun block => scale * value block) =
      scale * uniformAverage value := by
  simp [uniformAverage, ← Finset.mul_sum]
  ring

/-- Fraction of a finite uniform population whose observable reaches the
declared threshold. -/
noncomputable def uniformTailFraction
    (value : Block → ℝ) (threshold : ℝ) : ℝ :=
  ((Finset.univ.filter fun block => threshold ≤ value block).card : ℝ) /
    Fintype.card Block

/-- Finite Markov spine: for a nonnegative observable, threshold times the
uniform tail fraction is at most the uniform average. -/
theorem uniformTailFraction_mul_threshold_le_average
    (value : Block → ℝ) (threshold : ℝ)
    (hnonnegative : ∀ block, 0 ≤ value block) :
    uniformTailFraction value threshold * threshold ≤
      uniformAverage value := by
  classical
  let tail :=
    Finset.univ.filter fun block : Block => threshold ≤ value block
  have htail :
      (tail.card : ℝ) * threshold ≤ ∑ block ∈ tail, value block := by
    calc
      (tail.card : ℝ) * threshold =
          ∑ _block ∈ tail, threshold := by simp
      _ ≤ ∑ block ∈ tail, value block :=
        Finset.sum_le_sum fun block membership =>
          (Finset.mem_filter.mp membership).2
  have hsubset :
      (∑ block ∈ tail, value block) ≤ ∑ block, value block := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro block membership; exact Finset.mem_univ block)
      (by
        intro block _membership _notInTail
        exact hnonnegative block)
  have hcard : 0 ≤ (Fintype.card Block : ℝ) := by positivity
  calc
    uniformTailFraction value threshold * threshold =
        ((tail.card : ℝ) * threshold) /
          Fintype.card Block := by
      simp only [uniformTailFraction, tail]
      ring
    _ ≤ (∑ block ∈ tail, value block) /
          Fintype.card Block :=
      div_le_div_of_nonneg_right htail hcard
    _ ≤ (∑ block, value block) / Fintype.card Block :=
      div_le_div_of_nonneg_right hsubset hcard
    _ = uniformAverage value := by rfl

/-- A bound on the mean gives the usual finite high-probability tail bound.
The positivity of the accuracy threshold and nonnegativity of the gap are
load-bearing. -/
theorem uniformTailFraction_le_bound_div
    (value : Block → ℝ) (threshold bound : ℝ)
    (hnonnegative : ∀ block, 0 ≤ value block)
    (hthreshold : 0 < threshold)
    (haverage : uniformAverage value ≤ bound) :
    uniformTailFraction value threshold ≤ bound / threshold := by
  apply (le_div_iff₀ hthreshold).2
  exact
    (uniformTailFraction_mul_threshold_le_average
      value threshold hnonnegative).trans haverage

/-- Per-block decrease plus enough average benefit yields the one-step
contract required by the geometric theorem. -/
theorem oneStepContraction_of_aggregateBenefit
    (step : Block → State → State) (gap : State → ℝ)
    (benefit : Block → State → ℝ) (rate : ℝ)
    (hdecrease :
      ∀ state block,
        gap (step block state) ≤ gap state - benefit block state)
    (hbenefit :
      ∀ state,
        (1 - rate) * gap state ≤
          uniformAverage (fun block => benefit block state)) :
    HasUniformOneStepContraction step gap rate := by
  intro state
  calc
    uniformAverage (fun block => gap (step block state)) ≤
        uniformAverage (fun block =>
          gap state - benefit block state) :=
      uniformAverage_mono (fun block => hdecrease state block)
    _ = gap state -
        uniformAverage (fun block => benefit block state) :=
      uniformAverage_const_sub _ _
    _ ≤ gap state - (1 - rate) * gap state :=
      sub_le_sub_left (hbenefit state) _
    _ = rate * gap state := by ring

omit [Nonempty Block] in
/-- Exact linear expected convergence from a statewise uniform-block
contraction.  The theorem concerns the declared finite expectation; it does
not infer the contract from sparsity alone. -/
theorem meanGapAfter_le_geometric
    (step : Block → State → State) (gap : State → ℝ)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (contract : HasUniformOneStepContraction step gap rate)
    (rounds : ℕ) (state : State) :
    meanGapAfter step gap rounds state ≤ rate ^ rounds * gap state := by
  induction rounds generalizing state with
  | zero =>
      simp [meanGapAfter]
  | succ rounds ih =>
      calc
        meanGapAfter step gap (rounds + 1) state =
            uniformAverage (fun block =>
              meanGapAfter step gap rounds (step block state)) := by
          rfl
        _ ≤ uniformAverage (fun block =>
              rate ^ rounds * gap (step block state)) :=
          uniformAverage_mono (fun block => ih (step block state))
        _ = rate ^ rounds *
              uniformAverage (fun block => gap (step block state)) :=
          uniformAverage_const_mul _ _
        _ ≤ rate ^ rounds * (rate * gap state) :=
          mul_le_mul_of_nonneg_left (contract state)
            (pow_nonneg hrate rounds)
        _ = rate ^ (rounds + 1) * gap state := by
          rw [pow_succ]
          ring

/-! ## Exact two-coordinate instance -/

/-- Set the selected Boolean coordinate to zero. -/
def zeroSelectedCoordinate
    (block : Bool) (state : Bool → ℝ) : Bool → ℝ :=
  Function.update state block 0

/-- Separable quadratic gap for the two-coordinate fixture. -/
noncomputable def pairQuadraticGap (state : Bool → ℝ) : ℝ :=
  state false ^ 2 + state true ^ 2

theorem pairQuadratic_oneStep_exact (state : Bool → ℝ) :
    uniformAverage (fun block : Bool =>
      pairQuadraticGap (zeroSelectedCoordinate block state)) =
        (1 / 2 : ℝ) * pairQuadraticGap state := by
  classical
  simp [uniformAverage, pairQuadraticGap, zeroSelectedCoordinate]
  ring

theorem pairQuadratic_has_halfContraction :
    HasUniformOneStepContraction
      zeroSelectedCoordinate pairQuadraticGap (1 / 2 : ℝ) := by
  intro state
  exact le_of_eq (pairQuadratic_oneStep_exact state)

theorem pairQuadratic_meanGap_le
    (rounds : ℕ) (state : Bool → ℝ) :
    meanGapAfter zeroSelectedCoordinate pairQuadraticGap rounds state ≤
      (1 / 2 : ℝ) ^ rounds * pairQuadraticGap state :=
  meanGapAfter_le_geometric
    zeroSelectedCoordinate pairQuadraticGap (1 / 2 : ℝ)
    (by norm_num) pairQuadratic_has_halfContraction rounds state

/-! ## Negative boundary -/

/-- Merely labelling an identity map by every block does no work. -/
def identityBlockStep (_block : Bool) (state : ℝ) : ℝ :=
  state

noncomputable def scalarQuadraticGap (state : ℝ) : ℝ :=
  state ^ 2

theorem identityBlockStep_has_no_halfContraction :
    ¬ HasUniformOneStepContraction
      identityBlockStep scalarQuadraticGap (1 / 2 : ℝ) := by
  intro contract
  have h := contract 1
  norm_num [uniformAverage, identityBlockStep, scalarQuadraticGap] at h

/-- Without nonnegativity, a negative off-tail value can make the average
smaller than threshold times the tail fraction. -/
def signedTailCounterexample : Bool → ℝ
  | false => -100
  | true => 1

theorem signedObservable_breaks_Markov_spine :
    uniformAverage signedTailCounterexample <
      uniformTailFraction signedTailCounterexample 1 * 1 := by
  classical
  have htail :
      (Finset.univ.filter fun block : Bool =>
        (1 : ℝ) ≤ signedTailCounterexample block) = {true} := by
    ext block
    cases block <;> norm_num [signedTailCounterexample]
  have hfraction :
      uniformTailFraction signedTailCounterexample 1 = (1 / 2 : ℝ) := by
    rw [uniformTailFraction, htail]
    norm_num
  rw [hfraction]
  norm_num [uniformAverage, signedTailCounterexample]

#print axioms oneStepContraction_of_aggregateBenefit
#print axioms meanGapAfter_le_geometric
#print axioms uniformTailFraction_le_bound_div
#print axioms pairQuadratic_meanGap_le
#print axioms identityBlockStep_has_no_halfContraction
#print axioms signedObservable_breaks_Markov_spine

end UniformBlockExpectedDescent

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
