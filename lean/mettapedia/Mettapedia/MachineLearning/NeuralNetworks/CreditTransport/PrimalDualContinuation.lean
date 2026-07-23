import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.PrimalDual

/-!
# Dual-leak continuation and equilibrium bias

This file separates the dual ascent rate from quadratic dual leak for the
scalar regularized augmented-Lagrangian instance.  Exact elimination of the
dual variable yields the released residual-penalty objective.  An explicit
continuation path, defined through the hard-constraint endpoint at leak zero,
then gives an exact task-gradient bias and a conservative norm bound.

The results concern equilibrium bias.  They do not identify a finite iterate
with that equilibrium and do not replace a finite-settling or tracking bound.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PrimalDualContinuation

open Instances

/-- Residual-penalty objective obtained after exact dual maximization when the
dual leak is nonzero. -/
noncomputable def scalarReleasedPenaltyObjective
    (problem : ScalarPrimalDualProblem) (prediction primal : ℝ) : ℝ :=
  (primal - problem.target) ^ 2 / 2 +
    (problem.penalty + 1 / problem.dualLeak) *
      (primal - prediction) ^ 2 / 2

/-- Completing the square isolates the exact dual maximizer. -/
theorem scalarDualElimination_identity
    (problem : ScalarPrimalDualProblem) (prediction primal dual : ℝ)
    (hleak : problem.dualLeak ≠ 0) :
    scalarRegularizedAugmentedLagrangian problem prediction primal dual =
      scalarReleasedPenaltyObjective problem prediction primal -
        problem.dualLeak / 2 *
          (dual - (primal - prediction) / problem.dualLeak) ^ 2 := by
  simp [scalarRegularizedAugmentedLagrangian,
    scalarReleasedPenaltyObjective]
  field_simp [hleak]
  ring

/-- At positive leak, exact dual maximization produces the released objective. -/
theorem scalarDualElimination_at_maximizer
    (problem : ScalarPrimalDualProblem) (prediction primal : ℝ)
    (hleak : problem.dualLeak ≠ 0) :
    scalarRegularizedAugmentedLagrangian problem prediction primal
        ((primal - prediction) / problem.dualLeak) =
      scalarReleasedPenaltyObjective problem prediction primal := by
  rw [scalarDualElimination_identity problem prediction primal _ hleak]
  ring

/-- Positive leak makes the eliminated value an upper bound over all dual
states, not merely a stationary substitution. -/
theorem scalarDualElimination_upperBound
    (problem : ScalarPrimalDualProblem) (prediction primal dual : ℝ)
    (hleak : 0 < problem.dualLeak) :
    scalarRegularizedAugmentedLagrangian problem prediction primal dual ≤
      scalarReleasedPenaltyObjective problem prediction primal := by
  rw [scalarDualElimination_identity problem prediction primal dual
    (ne_of_gt hleak)]
  nlinarith [sq_nonneg
    (dual - (primal - prediction) / problem.dualLeak)]

/-- Denominator of the explicit scalar continuation path. -/
noncomputable def scalarContinuationDenominator
    (problem : ScalarPrimalDualProblem) : ℝ :=
  1 + (1 + problem.penalty) * problem.dualLeak

/-- Primal coordinate of the scalar hard-to-soft continuation path.  The
formula extends continuously to leak zero without dividing by the leak. -/
noncomputable def scalarContinuationPrimal
    (problem : ScalarPrimalDualProblem) (prediction : ℝ) : ℝ :=
  prediction + problem.dualLeak * (problem.target - prediction) /
    scalarContinuationDenominator problem

/-- Dual coordinate of the same continuation path. -/
noncomputable def scalarContinuationDual
    (problem : ScalarPrimalDualProblem) (prediction : ℝ) : ℝ :=
  (problem.target - prediction) / scalarContinuationDenominator problem

/-- The explicit path satisfies both primal and dual equilibrium equations. -/
theorem scalarContinuation_equilibrium
    (problem : ScalarPrimalDualProblem) (prediction : ℝ)
    (hdenominator : scalarContinuationDenominator problem ≠ 0) :
    scalarPrimalDualEquilibrium problem prediction
      (scalarContinuationPrimal problem prediction)
      (scalarContinuationDual problem prediction) := by
  constructor
  · change
      (prediction + problem.dualLeak * (problem.target - prediction) /
          scalarContinuationDenominator problem) - problem.target +
        (problem.target - prediction) /
          scalarContinuationDenominator problem +
        problem.penalty *
          ((prediction + problem.dualLeak * (problem.target - prediction) /
              scalarContinuationDenominator problem) - prediction) = 0
    field_simp [hdenominator]
    unfold scalarContinuationDenominator
    ring
  · change
      (prediction + problem.dualLeak * (problem.target - prediction) /
          scalarContinuationDenominator problem) - prediction =
        problem.dualLeak * ((problem.target - prediction) /
          scalarContinuationDenominator problem)
    ring

/-- At zero leak, the path is the exact hard-constraint endpoint. -/
theorem scalarContinuation_zeroLeak_primal
    (problem : ScalarPrimalDualProblem) (prediction : ℝ)
    (hleak : problem.dualLeak = 0) :
    scalarContinuationPrimal problem prediction = prediction := by
  simp [scalarContinuationPrimal, hleak]

theorem scalarContinuation_zeroLeak_dual
    (problem : ScalarPrimalDualProblem) (prediction : ℝ)
    (hleak : problem.dualLeak = 0) :
    scalarContinuationDual problem prediction = problem.target - prediction := by
  simp [scalarContinuationDual, scalarContinuationDenominator, hleak]

/-- Along the explicit continuation path, the residual is exactly the dual
leak times the multiplier. -/
theorem scalarContinuation_residual_eq_leak_mul_dual
    (problem : ScalarPrimalDualProblem) (prediction : ℝ) :
    scalarContinuationPrimal problem prediction - prediction =
      problem.dualLeak * scalarContinuationDual problem prediction := by
  simp [scalarContinuationPrimal, scalarContinuationDual]
  ring

/-- At equilibrium, the composite parameter signal equals the task gradient
at the released primal state. -/
theorem scalarContinuation_compositeGradient_eq_taskGradient
    (problem : ScalarPrimalDualProblem) (prediction : ℝ)
    (hdenominator : scalarContinuationDenominator problem ≠ 0) :
    scalarCompositeParameterGradient problem prediction
        (scalarContinuationPrimal problem prediction)
        (scalarContinuationDual problem prediction) =
      scalarContinuationPrimal problem prediction - problem.target := by
  have hequilibrium := scalarContinuation_equilibrium
    problem prediction hdenominator
  rcases hequilibrium with ⟨hprimal, _⟩
  simp [scalarPrimalGradient, scalarCompositeParameterGradient] at hprimal ⊢
  linarith

/-- Exact equilibrium task-gradient bias caused by constraint release. -/
theorem scalarContinuation_gradientBias_exact
    (problem : ScalarPrimalDualProblem) (prediction : ℝ)
    (hdenominator : scalarContinuationDenominator problem ≠ 0) :
    scalarCompositeParameterGradient problem prediction
          (scalarContinuationPrimal problem prediction)
          (scalarContinuationDual problem prediction) -
        (prediction - problem.target) =
      problem.dualLeak * (problem.target - prediction) /
        scalarContinuationDenominator problem := by
  rw [scalarContinuation_compositeGradient_eq_taskGradient
    problem prediction hdenominator]
  simp [scalarContinuationPrimal]

/-- With nonnegative penalty and leak, the equilibrium gradient bias is at
most leak times the hard-endpoint target gap. -/
theorem abs_scalarContinuation_gradientBias_le
    (problem : ScalarPrimalDualProblem) (prediction : ℝ)
    (hpenalty : 0 ≤ problem.penalty) (hleak : 0 ≤ problem.dualLeak) :
    |scalarCompositeParameterGradient problem prediction
          (scalarContinuationPrimal problem prediction)
          (scalarContinuationDual problem prediction) -
        (prediction - problem.target)| ≤
      problem.dualLeak * |problem.target - prediction| := by
  have hdenominatorOne : 1 ≤ scalarContinuationDenominator problem := by
    unfold scalarContinuationDenominator
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + problem.penalty) hleak]
  have hdenominator : 0 < scalarContinuationDenominator problem :=
    lt_of_lt_of_le zero_lt_one hdenominatorOne
  rw [scalarContinuation_gradientBias_exact problem prediction
    (ne_of_gt hdenominator), abs_div, abs_mul,
      abs_of_nonneg hleak, abs_of_pos hdenominator]
  apply (div_le_iff₀ hdenominator).2
  nlinarith [mul_nonneg hleak (abs_nonneg (problem.target - prediction))]

/-! ## Smooth continuation and budget composition -/

/-- Vary only the dual-leak axis while holding the task, penalty, rates, and
initializer fixed. -/
def withDualLeak
    (problem : ScalarPrimalDualProblem) (leak : ℝ) : ScalarPrimalDualProblem :=
  { problem with dualLeak := leak }

noncomputable def scalarLeakPathPrimal
    (problem : ScalarPrimalDualProblem) (prediction leak : ℝ) : ℝ :=
  prediction + leak * (problem.target - prediction) /
    (1 + (1 + problem.penalty) * leak)

noncomputable def scalarLeakPathDual
    (problem : ScalarPrimalDualProblem) (prediction leak : ℝ) : ℝ :=
  (problem.target - prediction) /
    (1 + (1 + problem.penalty) * leak)

theorem scalarLeakPathPrimal_eq_continuation
    (problem : ScalarPrimalDualProblem) (prediction leak : ℝ) :
    scalarLeakPathPrimal problem prediction leak =
      scalarContinuationPrimal (withDualLeak problem leak) prediction := by
  rfl

theorem scalarLeakPathDual_eq_continuation
    (problem : ScalarPrimalDualProblem) (prediction leak : ℝ) :
    scalarLeakPathDual problem prediction leak =
      scalarContinuationDual (withDualLeak problem leak) prediction := by
  rfl

/-- The hard-to-soft primal path is differentiable wherever its continuation
denominator is nonzero.  At leak zero the derivative is exactly the original
target gap. -/
theorem hasDerivAt_scalarLeakPathPrimal
    (problem : ScalarPrimalDualProblem) (prediction leak : ℝ)
    (hdenominator : 1 + (1 + problem.penalty) * leak ≠ 0) :
    HasDerivAt (scalarLeakPathPrimal problem prediction)
      ((problem.target - prediction) /
        (1 + (1 + problem.penalty) * leak) ^ 2) leak := by
  have hnum : HasDerivAt
      (fun t : ℝ => t * (problem.target - prediction))
      (problem.target - prediction) leak := by
    simpa using (hasDerivAt_id leak).mul_const
      (problem.target - prediction)
  have hden : HasDerivAt
      (fun t : ℝ => 1 + (1 + problem.penalty) * t)
      (1 + problem.penalty) leak := by
    simpa [add_comm] using
      ((hasDerivAt_id leak).const_mul (1 + problem.penalty)).const_add 1
  change HasDerivAt
    (fun t : ℝ => prediction + t * (problem.target - prediction) /
      (1 + (1 + problem.penalty) * t))
    ((problem.target - prediction) /
      (1 + (1 + problem.penalty) * leak) ^ 2) leak
  have hpath := (hnum.div hden hdenominator).const_add prediction
  apply hpath.congr_deriv
  field_simp [hdenominator]
  ring

theorem hasDerivAt_scalarLeakPathPrimal_zero
    (problem : ScalarPrimalDualProblem) (prediction : ℝ) :
    HasDerivAt (scalarLeakPathPrimal problem prediction)
      (problem.target - prediction) 0 := by
  simpa using hasDerivAt_scalarLeakPathPrimal problem prediction 0 (by norm_num)

/-- A four-stage certificate keeps solver, continuation, nonlinear, and
tracking errors explicit instead of collapsing them into one BP cosine. -/
theorem norm_gradientGap_le_four_errors
    {Gradient : Type*} [NormedAddCommGroup Gradient]
    (finite settled released tracked reference : Gradient)
    (solveError biasError nonlinearError trackingError : ℝ)
    (hsolve : ‖finite - settled‖ ≤ solveError)
    (hbias : ‖settled - released‖ ≤ biasError)
    (hnonlinear : ‖released - tracked‖ ≤ nonlinearError)
    (htracking : ‖tracked - reference‖ ≤ trackingError) :
    ‖finite - reference‖ ≤
      solveError + biasError + nonlinearError + trackingError := by
  calc
    ‖finite - reference‖ ≤
        ‖finite - settled‖ + ‖settled - released‖ +
          ‖released - tracked‖ + ‖tracked - reference‖ := by
      calc
        ‖finite - reference‖ ≤ ‖finite - settled‖ + ‖settled - reference‖ := by
          simpa [sub_eq_add_neg, add_assoc] using
            norm_add_le (finite - settled) (settled - reference)
        _ ≤ ‖finite - settled‖ +
              (‖settled - released‖ + ‖released - reference‖) := by
          gcongr
          simpa [sub_eq_add_neg, add_assoc] using
            norm_add_le (settled - released) (released - reference)
        _ ≤ ‖finite - settled‖ +
              (‖settled - released‖ +
                (‖released - tracked‖ + ‖tracked - reference‖)) := by
          gcongr
          simpa [sub_eq_add_neg, add_assoc] using
            norm_add_le (released - tracked) (tracked - reference)
        _ = ‖finite - settled‖ + ‖settled - released‖ +
              ‖released - tracked‖ + ‖tracked - reference‖ := by ring
    _ ≤ solveError + biasError + nonlinearError + trackingError := by
      gcongr

/-- Per-site release budgets add conservatively.  This licenses heterogeneous
leak allocation without pretending that one scalar precision is mandatory. -/
theorem abs_sum_siteBias_le_sum_budget
    {Site : Type*} [Fintype Site]
    (siteBias siteBudget : Site → ℝ)
    (hsite : ∀ site, |siteBias site| ≤ siteBudget site) :
    |∑ site, siteBias site| ≤ ∑ site, siteBudget site := by
  calc
    |∑ site, siteBias site| ≤ ∑ site, |siteBias site| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ site, siteBudget site := Finset.sum_le_sum fun site _ => hsite site

/-! ## Positive and negative fixtures -/

noncomputable def unitLeakyContinuationProblem : ScalarPrimalDualProblem where
  target := 1
  penalty := 1
  primalRate := 1 / 2
  dualRate := 1
  dualLeak := 1
  initialDual := 0

theorem unitLeakyContinuation_coordinates :
    scalarContinuationPrimal unitLeakyContinuationProblem 0 = 1 / 3 ∧
      scalarContinuationDual unitLeakyContinuationProblem 0 = 1 / 3 := by
  norm_num [scalarContinuationPrimal, scalarContinuationDual,
    scalarContinuationDenominator, unitLeakyContinuationProblem]

/-- Positive leak does not retain the hard feasible endpoint in this fixture. -/
theorem unitLeakyContinuation_not_hardFeasible :
    scalarContinuationPrimal unitLeakyContinuationProblem 0 ≠ 0 := by
  norm_num [scalarContinuationPrimal, scalarContinuationDenominator,
    unitLeakyContinuationProblem]

theorem unitLeakyContinuation_gradientBias :
    scalarCompositeParameterGradient unitLeakyContinuationProblem 0
        (scalarContinuationPrimal unitLeakyContinuationProblem 0)
        (scalarContinuationDual unitLeakyContinuationProblem 0) -
      (0 - unitLeakyContinuationProblem.target) = 1 / 3 := by
  norm_num [scalarCompositeParameterGradient, scalarContinuationPrimal,
    scalarContinuationDual, scalarContinuationDenominator,
    unitLeakyContinuationProblem]

#print axioms scalarDualElimination_identity
#print axioms scalarDualElimination_upperBound
#print axioms scalarContinuation_equilibrium
#print axioms scalarContinuation_residual_eq_leak_mul_dual
#print axioms scalarContinuation_gradientBias_exact
#print axioms abs_scalarContinuation_gradientBias_le
#print axioms hasDerivAt_scalarLeakPathPrimal
#print axioms norm_gradientGap_le_four_errors
#print axioms abs_sum_siteBias_le_sum_budget
#print axioms unitLeakyContinuation_not_hardFeasible

end PrimalDualContinuation

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
