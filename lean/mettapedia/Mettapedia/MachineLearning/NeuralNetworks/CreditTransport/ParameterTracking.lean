import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.JacobianRemainderContraction

/-!
# Parameter-indexed local tracking for credit solvers

A warm start from the preceding problem is useful only when its previous
error plus the displacement of the new fixed point fits inside the next
solver's certified neighborhood.  This file makes that admission condition
explicit and then reuses local contraction to bound any declared number of
corrective settling steps.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ParameterTracking

open AmortizedInitialization
open LocalAmortizedInitialization

variable {Parameter State : Type*} [NormedAddCommGroup State]

/-- A parameter-indexed solver family with one common certified radius.  The
center at each parameter is required to be the solver's actual fixed point. -/
structure LocalSolverFamily
    (solver : Parameter → State → State) (target : Parameter → State)
    (radius : ℝ) where
  certificate : ∀ parameter,
    LocalContractionCertificate (solver parameter) (target parameter) radius
  target_fixed : ∀ parameter,
    IsFixedPoint (solver parameter) (target parameter)

/-- Previous tracking error plus target drift bounds the new initializer
error.  This is the admission inequality that must be checked before a local
certificate can be reused after a parameter change. -/
theorem initializer_distance_to_nextTarget_le
    (target : Parameter → State)
    (previous next : Parameter) (state : State) (error drift : ℝ)
    (herror : ‖state - target previous‖ ≤ error)
    (hdrift : ‖target previous - target next‖ ≤ drift) :
    ‖state - target next‖ ≤ error + drift := by
  have hdecompose :
      state - target next =
        (state - target previous) + (target previous - target next) := by
    abel
  rw [hdecompose]
  exact le_trans (norm_add_le _ _) (add_le_add herror hdrift)

/-- If the previous error plus fixed-point drift fits inside the common
radius, the old state is admitted to the new solver's local neighborhood. -/
theorem initializer_mem_nextBall
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (_family : LocalSolverFamily solver target radius)
    (previous next : Parameter) (state : State) (error drift : ℝ)
    (herror : ‖state - target previous‖ ≤ error)
    (hdrift : ‖target previous - target next‖ ≤ drift)
    (hadmission : error + drift ≤ radius) :
    InClosedBall (target next) radius state := by
  exact le_trans
    (initializer_distance_to_nextTarget_le target previous next state
      error drift herror hdrift)
    hadmission

/-- After an admitted parameter change, any finite number of corrective
steps contracts the combined previous-error and target-drift budget. -/
theorem parameterized_iterate_tracking_le
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (previous next : Parameter) (state : State) (error drift : ℝ)
    (herror : ‖state - target previous‖ ≤ error)
    (hdrift : ‖target previous - target next‖ ≤ drift)
    (hadmission : error + drift ≤ radius) (steps : ℕ) :
    ‖(solver next)^[steps] state - target next‖ ≤
      (family.certificate next).factor ^ steps * (error + drift) := by
  have hinitial := initializer_mem_nextBall family previous next state
    error drift herror hdrift hadmission
  have htarget : InClosedBall (target next) radius (target next) := by
    simp [InClosedBall, (family.certificate next).radius_nonneg]
  have hgeometric := iterate_initializer_to_fixedPoint_le
    (family.certificate next) (target next) state htarget hinitial
    (family.target_fixed next) steps
  exact le_trans hgeometric
    (mul_le_mul_of_nonneg_left
      (initializer_distance_to_nextTarget_le target previous next state
        error drift herror hdrift)
      (pow_nonneg (family.certificate next).factor_nonneg steps))

/-! ## A moving scalar family and its admission boundary -/

noncomputable def shiftedHalfSolver (target state : ℝ) : ℝ :=
  target + (state - target) / 2

noncomputable def shiftedHalfFamily :
    LocalSolverFamily shiftedHalfSolver (fun target : ℝ => target) 1 where
  certificate := by
    intro target
    refine
      { factor := 1 / 2
        factor_nonneg := by norm_num
        factor_lt_one := by norm_num
        radius_nonneg := by norm_num
        maps_ball := ?_
        contracts_on_ball := ?_ }
    · intro state hstate
      have hrewrite :
          shiftedHalfSolver target state - target = (state - target) / 2 := by
        simp [shiftedHalfSolver]
      rw [InClosedBall, hrewrite, Real.norm_eq_abs, abs_div]
      norm_num
      have hstate' := hstate
      rw [InClosedBall, Real.norm_eq_abs] at hstate'
      nlinarith [abs_nonneg (state - target)]
    · intro left right _ _
      have hrewrite :
          shiftedHalfSolver target left - shiftedHalfSolver target right =
            (left - right) / 2 := by
        simp [shiftedHalfSolver]
        ring
      rw [hrewrite, Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
      norm_num [div_eq_mul_inv, mul_comm]
  target_fixed := by
    intro target
    simp [IsFixedPoint, shiftedHalfSolver]

theorem shiftedHalf_parameterized_twoStep_tracking :
    |(shiftedHalfSolver (1 / 4))^[2] (1 / 2) - 1 / 4| ≤
      (1 / 2 : ℝ) ^ 2 * (1 / 2 + 1 / 4) := by
  simpa [Real.norm_eq_abs, shiftedHalfFamily] using
    parameterized_iterate_tracking_le shiftedHalfFamily
      (0 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ)
      (by norm_num [Real.norm_eq_abs])
      (by norm_num [Real.norm_eq_abs])
      (by norm_num) 2

/-- The admission premise is substantive: a three-quarter error and an
oppositely directed half-unit target move place the old state outside the new
unit neighborhood. -/
theorem shiftedHalf_opposedDrift_not_admitted :
    ¬ InClosedBall (-1 / 2 : ℝ) 1 (3 / 4 : ℝ) := by
  norm_num [InClosedBall, Real.norm_eq_abs]

#print axioms initializer_distance_to_nextTarget_le
#print axioms initializer_mem_nextBall
#print axioms parameterized_iterate_tracking_le
#print axioms shiftedHalf_parameterized_twoStep_tracking
#print axioms shiftedHalf_opposedDrift_not_admitted

end ParameterTracking

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
