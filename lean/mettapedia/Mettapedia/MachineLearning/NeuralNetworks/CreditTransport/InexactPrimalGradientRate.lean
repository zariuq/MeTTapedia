import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactFirstOrderOracle

/-!
# Primal-gradient rates from an inexact first-order oracle

This module formalizes the nonaccumulating-error mechanism of the primal
gradient method for a strongly convex inexact first-order oracle.  The analytic
layer derives the one-step distance/objective inequality for the unconstrained
Hilbert-space update.  A separate recurrence layer turns any trace satisfying
that inequality into a geometric best-iterate objective bound with a single
additive oracle error.

The recurrence is intentionally reusable by predictive-settling traces: a
runtime need only certify the one-step inequality and objective lower bound.
Negative fixtures show why positive strong convexity, a positive smoothness
constant, and best-iterate selection cannot be omitted.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace InexactPrimalGradientRate

open Set
open scoped InnerProductSpace

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- Unconstrained primal-gradient update using the oracle gradient and rate
`1 / smoothness`. -/
noncomputable def primalStep
    (gradient : State → State) (smoothness : ℝ) (state : State) : State :=
  state - (1 / smoothness) • gradient state

/-- Exact contraction coefficient appearing in the strongly-convex primal
gradient recurrence. -/
noncomputable def contraction (smoothness strongConvexity : ℝ) : ℝ :=
  1 - strongConvexity / smoothness

theorem contraction_nonneg
    {smoothness strongConvexity : ℝ}
    (smoothness_pos : 0 < smoothness)
    (strongConvexity_le : strongConvexity ≤ smoothness) :
    0 ≤ contraction smoothness strongConvexity := by
  unfold contraction
  have : strongConvexity / smoothness ≤ 1 := by
    exact (div_le_one smoothness_pos).2 strongConvexity_le
  linarith

theorem contraction_lt_one
    {smoothness strongConvexity : ℝ}
    (smoothness_pos : 0 < smoothness)
    (strongConvexity_pos : 0 < strongConvexity) :
    contraction smoothness strongConvexity < 1 := by
  unfold contraction
  exact sub_lt_self 1 (div_pos strongConvexity_pos smoothness_pos)

/-- The one-step inequality underlying the primal-gradient rate.  Oracle error
appears once in the objective term; it is not accumulated into the contraction
coefficient. -/
theorem primalStep_distance_sq_le
    {objective value : State → ℝ} {gradient : State → State}
    {delta smoothness strongConvexity : ℝ}
    (oracle :
      InexactFirstOrderOracle.Certificate (Set.univ : Set State)
        objective value gradient delta smoothness strongConvexity)
    (smoothness_pos : 0 < smoothness)
    (state minimizer : State) :
    ‖primalStep gradient smoothness state - minimizer‖ ^ 2 ≤
      contraction smoothness strongConvexity * ‖state - minimizer‖ ^ 2 -
        (2 / smoothness) *
          (objective (primalStep gradient smoothness state) -
            objective minimizer - delta) := by
  let next := primalStep gradient smoothness state
  let difference := state - minimizer
  let rate : ℝ := 1 / smoothness
  have rate_nonneg : 0 ≤ rate := by
    exact le_of_lt (one_div_pos.mpr smoothness_pos)
  have next_sub_state :
      next - state = -(rate • gradient state) := by
    dsimp [next, primalStep, rate]
    module
  have next_sub_minimizer :
      next - minimizer = difference - rate • gradient state := by
    dsimp [next, primalStep, difference, rate]
    module
  have lower := oracle.lower minimizer (Set.mem_univ _) state (Set.mem_univ _)
  have upper := oracle.upper next (Set.mem_univ _) state (Set.mem_univ _)
  have lower_inner :
      strongConvexity / 2 * ‖difference‖ ^ 2 ≤
        objective minimizer - value state +
          ⟪difference, gradient state⟫_ℝ := by
    simpa [show minimizer - state = -difference by
        dsimp [difference]
        abel,
      norm_neg, inner_neg_right, real_inner_comm, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using lower
  have upper_step :
      objective next - value state ≤
        -(rate / 2) * ‖gradient state‖ ^ 2 + delta := by
    rw [next_sub_state, inner_neg_right, inner_smul_right, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg rate_nonneg,
      real_inner_self_eq_norm_sq] at upper
    dsimp [rate] at upper ⊢
    field_simp at upper ⊢
    nlinarith
  rw [next_sub_minimizer, norm_sub_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg rate_nonneg]
  dsimp [contraction, rate, difference, next] at *
  field_simp at *
  nlinarith

/-! ## Abstract nonaccumulating-error recurrence -/

/-- Backward geometric weight accumulated by `steps` best-iterate terms. -/
noncomputable def geometricWeight (factor : ℝ) : ℕ → ℝ
  | 0 => 0
  | steps + 1 => factor * geometricWeight factor steps + 1

/-- Backward geometrically weighted objective gaps, after subtracting the
single-step oracle budget. -/
noncomputable def weightedGap
    (factor delta : ℝ) (gap : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | steps + 1 =>
      factor * weightedGap factor delta gap steps +
        (gap (steps + 1) - delta)

@[simp] theorem geometricWeight_zero (factor : ℝ) :
    geometricWeight factor 0 = 0 := rfl

@[simp] theorem geometricWeight_succ (factor : ℝ) (steps : ℕ) :
    geometricWeight factor (steps + 1) =
      factor * geometricWeight factor steps + 1 := rfl

@[simp] theorem weightedGap_zero
    (factor delta : ℝ) (gap : ℕ → ℝ) :
    weightedGap factor delta gap 0 = 0 := rfl

@[simp] theorem weightedGap_succ
    (factor delta : ℝ) (gap : ℕ → ℝ) (steps : ℕ) :
    weightedGap factor delta gap (steps + 1) =
      factor * weightedGap factor delta gap steps +
        (gap (steps + 1) - delta) := rfl

/-- Algebraic trace contract extracted from the primal-gradient proof. -/
structure TraceCertificate
    (distanceSq gap : ℕ → ℝ)
    (smoothness strongConvexity delta : ℝ) : Prop where
  smoothness_pos : 0 < smoothness
  strongConvexity_pos : 0 < strongConvexity
  strongConvexity_le_smoothness : strongConvexity ≤ smoothness
  distance_nonneg : ∀ steps, 0 ≤ distanceSq steps
  gap_nonneg : ∀ steps, 0 ≤ gap steps
  one_step :
    ∀ steps,
      distanceSq (steps + 1) ≤
        contraction smoothness strongConvexity * distanceSq steps -
          (2 / smoothness) * (gap (steps + 1) - delta)

/-- The distance plus the weighted objective gaps contracts geometrically. -/
theorem weightedPotential_le
    {distanceSq gap : ℕ → ℝ}
    {smoothness strongConvexity delta : ℝ}
    (trace :
      TraceCertificate distanceSq gap smoothness strongConvexity delta)
    (steps : ℕ) :
    distanceSq steps +
        (2 / smoothness) *
          weightedGap (contraction smoothness strongConvexity) delta gap steps ≤
      contraction smoothness strongConvexity ^ steps * distanceSq 0 := by
  let factor := contraction smoothness strongConvexity
  have factor_nonneg : 0 ≤ factor :=
    contraction_nonneg trace.smoothness_pos
      trace.strongConvexity_le_smoothness
  induction steps with
  | zero => simp
  | succ steps ih =>
      have oneStep := trace.one_step steps
      rw [weightedGap_succ, pow_succ]
      dsimp [factor] at factor_nonneg ⊢
      calc
        distanceSq (steps + 1) +
            2 / smoothness *
              (contraction smoothness strongConvexity *
                  weightedGap (contraction smoothness strongConvexity)
                    delta gap steps +
                (gap (steps + 1) - delta)) ≤
            contraction smoothness strongConvexity * distanceSq steps -
                2 / smoothness * (gap (steps + 1) - delta) +
              2 / smoothness *
                (contraction smoothness strongConvexity *
                    weightedGap (contraction smoothness strongConvexity)
                      delta gap steps +
                  (gap (steps + 1) - delta)) := by
          gcongr
        _ =
            contraction smoothness strongConvexity *
              (distanceSq steps +
                2 / smoothness *
                  weightedGap (contraction smoothness strongConvexity)
                    delta gap steps) := by ring
        _ ≤
            contraction smoothness strongConvexity *
              (contraction smoothness strongConvexity ^ steps *
                distanceSq 0) := by
          exact mul_le_mul_of_nonneg_left ih factor_nonneg
        _ =
            contraction smoothness strongConvexity ^ steps *
              contraction smoothness strongConvexity * distanceSq 0 := by ring

theorem geometricWeight_nonneg
    {factor : ℝ} (factor_nonneg : 0 ≤ factor) (steps : ℕ) :
    0 ≤ geometricWeight factor steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [geometricWeight_succ]
      exact add_nonneg (mul_nonneg factor_nonneg ih) zero_le_one

/-- Every nonempty geometric weight contains the current iterate with unit
weight. -/
theorem one_le_geometricWeight
    {factor : ℝ} (factor_nonneg : 0 ≤ factor) {steps : ℕ}
    (steps_pos : 0 < steps) :
    1 ≤ geometricWeight factor steps := by
  obtain ⟨prior, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt steps_pos)
  rw [geometricWeight_succ]
  exact le_add_of_nonneg_left
    (mul_nonneg factor_nonneg (geometricWeight_nonneg factor_nonneg prior))

/-- A lower bound shared by all observed gaps lifts to the weighted gap. -/
theorem geometricWeight_mul_best_sub_delta_le_weightedGap
    {gap : ℕ → ℝ} {factor delta best : ℝ}
    (factor_nonneg : 0 ≤ factor)
    (best_le : ∀ steps, best ≤ gap (steps + 1))
    (steps : ℕ) :
    geometricWeight factor steps * (best - delta) ≤
      weightedGap factor delta gap steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [geometricWeight_succ, weightedGap_succ]
      calc
        (factor * geometricWeight factor steps + 1) * (best - delta) =
            factor * (geometricWeight factor steps * (best - delta)) +
              (best - delta) := by ring
        _ ≤
            factor * weightedGap factor delta gap steps +
              (gap (steps + 1) - delta) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left ih factor_nonneg)
            (sub_le_sub_right (best_le steps) delta)

/-- Geometric best-iterate objective rate with one additive oracle error.
This is the nonaccumulation conclusion of the primal-gradient theorem. -/
theorem bestGap_le_geometric_add_delta
    {distanceSq gap : ℕ → ℝ}
    {smoothness strongConvexity delta best : ℝ}
    (trace :
      TraceCertificate distanceSq gap smoothness strongConvexity delta)
    (best_le : ∀ steps, best ≤ gap (steps + 1))
    {steps : ℕ} (steps_pos : 0 < steps) :
    best ≤
      smoothness / 2 *
          contraction smoothness strongConvexity ^ steps * distanceSq 0 +
        delta := by
  let factor := contraction smoothness strongConvexity
  have factor_nonneg : 0 ≤ factor :=
    contraction_nonneg trace.smoothness_pos
      trace.strongConvexity_le_smoothness
  have distance_zero_nonneg := trace.distance_nonneg 0
  have power_nonneg : 0 ≤ factor ^ steps := pow_nonneg factor_nonneg _
  by_cases below_error : best ≤ delta
  · have main_nonneg :
        0 ≤ smoothness / 2 * factor ^ steps * distanceSq 0 := by
      exact mul_nonneg
        (mul_nonneg
          (div_nonneg (le_of_lt trace.smoothness_pos) (by norm_num))
          power_nonneg)
        distance_zero_nonneg
    dsimp [factor] at main_nonneg ⊢
    linarith
  · have best_sub_delta_pos : 0 < best - delta := sub_pos.mpr
      (lt_of_not_ge below_error)
    have weight_lower :=
      geometricWeight_mul_best_sub_delta_le_weightedGap
        (delta := delta) factor_nonneg best_le steps
    have potential := weightedPotential_le trace steps
    have distance_steps_nonneg := trace.distance_nonneg steps
    have smoothness_factor_pos : 0 < 2 / smoothness :=
      div_pos (by norm_num) trace.smoothness_pos
    have weight_one := one_le_geometricWeight factor_nonneg steps_pos
    have weighted_lower :
        best - delta ≤ geometricWeight factor steps * (best - delta) := by
      nlinarith
    have gap_budget :
        (2 / smoothness) * (best - delta) ≤
          factor ^ steps * distanceSq 0 := by
      calc
        (2 / smoothness) * (best - delta) ≤
            (2 / smoothness) *
              (geometricWeight factor steps * (best - delta)) := by
          exact mul_le_mul_of_nonneg_left weighted_lower
            (le_of_lt smoothness_factor_pos)
        _ ≤
            (2 / smoothness) *
              weightedGap factor delta gap steps := by
          exact mul_le_mul_of_nonneg_left weight_lower
            (le_of_lt smoothness_factor_pos)
        _ ≤ factor ^ steps * distanceSq 0 := by
          dsimp [factor] at potential ⊢
          linarith
    have smoothness_half_nonneg : 0 ≤ smoothness / 2 :=
      div_nonneg (le_of_lt trace.smoothness_pos) (by norm_num)
    have cancellation : smoothness / 2 * (2 / smoothness) = 1 := by
      field_simp [ne_of_gt trace.smoothness_pos]
    calc
      best = (best - delta) + delta := by ring
      _ ≤
          smoothness / 2 * (factor ^ steps * distanceSq 0) + delta := by
        gcongr
        calc
          best - delta =
              (smoothness / 2 * (2 / smoothness)) * (best - delta) := by
            rw [cancellation, one_mul]
          _ =
              smoothness / 2 * ((2 / smoothness) * (best - delta)) := by
            ring
          _ ≤
              smoothness / 2 * (factor ^ steps * distanceSq 0) :=
            mul_le_mul_of_nonneg_left gap_budget smoothness_half_nonneg
      _ =
          smoothness / 2 *
              contraction smoothness strongConvexity ^ steps * distanceSq 0 +
            delta := by
        dsimp [factor]
        ring

/-! ## Positive and negative fixtures -/

noncomputable def exactScalarDistanceSq (steps : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ steps

noncomputable def exactScalarGap (steps : ℕ) : ℝ :=
  if steps = 0 then 1 else (1 / 4 : ℝ) ^ steps

/-- A concrete trace satisfies the abstract contract with zero oracle error. -/
noncomputable def exactScalarTrace :
    TraceCertificate exactScalarDistanceSq exactScalarGap 2 1 0 where
  smoothness_pos := by norm_num
  strongConvexity_pos := by norm_num
  strongConvexity_le_smoothness := by norm_num
  distance_nonneg := by
    intro steps
    exact pow_nonneg (by norm_num) _
  gap_nonneg := by
    intro steps
    simp only [exactScalarGap]
    split
    · norm_num
    · positivity
  one_step := by
    intro steps
    simp [exactScalarDistanceSq, exactScalarGap, contraction, pow_succ]
    ring_nf
    exact le_rfl

theorem exactScalar_best_after_two :
    exactScalarGap 2 ≤
      2 / 2 * contraction 2 1 ^ 2 * exactScalarDistanceSq 0 := by
  norm_num [exactScalarGap, exactScalarDistanceSq, contraction]

/-- Without positive strong convexity, the exact contraction factor is one and
the geometric conclusion cannot certify strict decay. -/
theorem zeroStrongConvexity_has_no_strict_contraction
    (smoothness : ℝ) :
    contraction smoothness 0 = 1 := by
  simp [contraction]

/-- Selecting only the last iterate is not interchangeable with selecting the
best observed iterate: an admissible nonnegative gap sequence may rise. -/
theorem lastGap_can_exceed_earlierGap :
    let gap : ℕ → ℝ := fun steps => if steps = 1 then 0 else 1
    gap 2 > gap 1 := by
  norm_num

#print axioms primalStep_distance_sq_le
#print axioms weightedPotential_le
#print axioms one_le_geometricWeight
#print axioms geometricWeight_mul_best_sub_delta_le_weightedGap
#print axioms bestGap_le_geometric_add_delta
#print axioms exactScalarTrace
#print axioms zeroStrongConvexity_has_no_strict_contraction
#print axioms lastGap_can_exceed_earlierGap

end InexactPrimalGradientRate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
