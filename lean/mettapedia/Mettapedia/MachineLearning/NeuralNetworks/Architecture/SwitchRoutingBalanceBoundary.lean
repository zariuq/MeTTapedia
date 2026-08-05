import Mathlib

/-!
# Switch-routing load-balance boundary

Fedus, Zoph, and Shazeer, *Switch Transformers* (arXiv:2101.03961),
define the auxiliary routing loss in equations (4)--(6) as

`alpha * N * sum_i f_i * P_i`,

where `f` is the hard dispatch fraction and `P` is the average router
probability.  The paper says the unscaled factor is minimized by uniform
routing.  That conclusion is valid in the self-consistent special case
`f = P`, by Cauchy--Schwarz, but it is false for the two distinct vectors in
the displayed definition.

The counterexample below is induced by a legitimate two-kind token batch:
nine tenths of tokens have probabilities `(0.34, 0.33, 0.33)` and dispatch to
expert zero; one tenth have probabilities `(0, 0.51, 0.49)` and dispatch to
expert one.  Its normalized auxiliary factor is `4653/5000 < 1`, below the
uniform value `1`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

variable {Expert : Type*} [Fintype Expert]

/-- Equations (4)--(6), without the positive hyperparameter `alpha`. -/
def switchRoutingBalanceFactor
    (hardFraction meanProbability : Expert → ℝ) : ℝ :=
  Fintype.card Expert *
    ∑ expert, hardFraction expert * meanProbability expert

/-- Uniform mass over a nonempty finite expert family. -/
def uniformExpertMass (_expert : Expert) : ℝ :=
  1 / Fintype.card Expert

/-- The normalized uniform-routing factor is exactly one. -/
theorem switchRoutingBalanceFactor_uniform [Nonempty Expert] :
    switchRoutingBalanceFactor
      (uniformExpertMass (Expert := Expert))
      (uniformExpertMass (Expert := Expert)) =
      1 := by
  classical
  have card_pos : (0 : ℝ) < Fintype.card Expert := by
    exact_mod_cast Fintype.card_pos
  simp only [switchRoutingBalanceFactor, uniformExpertMass]
  rw [show (∑ _ : Expert,
      (1 / (Fintype.card Expert : ℝ)) *
        (1 / (Fintype.card Expert : ℝ))) =
      Fintype.card Expert *
        ((1 / (Fintype.card Expert : ℝ)) *
          (1 / (Fintype.card Expert : ℝ))) by simp]
  field_simp [ne_of_gt card_pos]

/-- If hard and soft load fractions coincide and sum to one, the source
balance factor is at least its uniform value. -/
theorem one_le_switchRoutingBalanceFactor_selfConsistent
    (mass : Expert → ℝ)
    (sum_one : ∑ expert, mass expert = 1) :
    1 ≤ switchRoutingBalanceFactor mass mass := by
  classical
  have cauchy :
      (∑ expert, mass expert) ^ 2 ≤
        (Fintype.card Expert : ℝ) * ∑ expert, mass expert ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset Expert)) (f := mass))
  rw [sum_one] at cauchy
  simpa [switchRoutingBalanceFactor, pow_two] using cauchy

/-! ## A source-faithful counterexample -/

def nearUniformRouteZero : Fin 3 → ℝ :=
  ![34 / 100, 33 / 100, 33 / 100]

def routeOne : Fin 3 → ℝ :=
  ![0, 51 / 100, 49 / 100]

/-- Nine tenths of the batch dispatch to expert zero and one tenth to expert
one. -/
def counterHardFraction : Fin 3 → ℝ :=
  ![9 / 10, 1 / 10, 0]

/-- Mean router probability for the same two-kind batch. -/
def counterMeanProbability (expert : Fin 3) : ℝ :=
  (9 / 10) * nearUniformRouteZero expert +
    (1 / 10) * routeOne expert

theorem nearUniformRouteZero_is_probability :
    (∀ expert, 0 ≤ nearUniformRouteZero expert) ∧
      ∑ expert, nearUniformRouteZero expert = 1 := by
  constructor
  · intro expert
    fin_cases expert <;> norm_num [nearUniformRouteZero]
  · norm_num [nearUniformRouteZero, Fin.sum_univ_succ]

theorem routeOne_is_probability :
    (∀ expert, 0 ≤ routeOne expert) ∧
      ∑ expert, routeOne expert = 1 := by
  constructor
  · intro expert
    fin_cases expert <;> norm_num [routeOne]
  · norm_num [routeOne, Fin.sum_univ_succ]

/-- Expert zero is a strict argmax for the majority token kind. -/
theorem nearUniformRouteZero_unique_argmax :
    ∀ expert : Fin 3,
      nearUniformRouteZero expert ≤ nearUniformRouteZero 0 ∧
      (expert ≠ 0 →
        nearUniformRouteZero expert < nearUniformRouteZero 0) := by
  intro expert
  fin_cases expert <;> norm_num [nearUniformRouteZero]

/-- Expert one is a strict argmax for the minority token kind. -/
theorem routeOne_unique_argmax :
    ∀ expert : Fin 3,
      routeOne expert ≤ routeOne 1 ∧
      (expert ≠ 1 → routeOne expert < routeOne 1) := by
  intro expert
  fin_cases expert <;> norm_num [routeOne]

theorem counterHardFraction_sums_to_one :
    ∑ expert, counterHardFraction expert = 1 := by
  norm_num [counterHardFraction, Fin.sum_univ_succ]

theorem counterMeanProbability_sums_to_one :
    ∑ expert, counterMeanProbability expert = 1 := by
  norm_num [counterMeanProbability, nearUniformRouteZero, routeOne,
    Fin.sum_univ_succ]

/-- The paper's displayed objective is strictly smaller than its value at
uniform routing for this admissible batch. -/
theorem switch_uniform_is_not_global_minimum :
    switchRoutingBalanceFactor counterHardFraction
      counterMeanProbability =
      4653 / 5000 ∧
    switchRoutingBalanceFactor counterHardFraction
      counterMeanProbability <
      switchRoutingBalanceFactor
        (uniformExpertMass (Expert := Fin 3))
        (uniformExpertMass (Expert := Fin 3)) := by
  constructor
  · norm_num [switchRoutingBalanceFactor, counterHardFraction,
      counterMeanProbability, nearUniformRouteZero, routeOne,
      Fin.sum_univ_succ]
  · rw [switchRoutingBalanceFactor_uniform]
    norm_num [switchRoutingBalanceFactor, counterHardFraction,
      counterMeanProbability, nearUniformRouteZero, routeOne,
      Fin.sum_univ_succ]

#print axioms switchRoutingBalanceFactor_uniform
#print axioms one_le_switchRoutingBalanceFactor_selfConsistent
#print axioms nearUniformRouteZero_unique_argmax
#print axioms routeOne_unique_argmax
#print axioms switch_uniform_is_not_global_minimum

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
