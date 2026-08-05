import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.TemporalEquilibrium
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Equilibrium-propagation finite-nudge and finite-settling budgets

Scellier and Bengio's equilibrium-propagation theorem identifies the task
gradient with a zero-nudge contrast of energy partials at exact equilibria.
This file recovers that limit in the solved scalar equilibrium already used by
the common credit-transport theory, then separates two errors that a finite
implementation must control:

* finite-nudge bias, which remains even at exact phase equilibria;
* finite-settling error, represented by the stationarity residual of each
  sampled phase.

The decompositions are exact.  Their absolute-value corollaries are executable
certificates: a trace need only provide the nudge, the two or three phase
residuals, and the task-gradient scale.  The symmetric estimator cancels the
first-order finite-nudge term, but a sharp scalar crossover shows that this does
not make it uniformly better at every finite radius.

Primary correspondence:

* B. Scellier and Y. Bengio, *Equilibrium Propagation: Bridging the Gap between
  Energy-Based Models and Backpropagation*, Frontiers in Computational
  Neuroscience 11 (2017), arXiv:1602.05179, Theorem 1 and Proposition 2.

The source theorem assumes exact equilibria and takes a zero-nudge limit.
Finite-radius and finite-settling guarantees below are additional results for
the declared scalar family; they are not attributed to the source theorem.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.EquilibriumPropagationErrorBudget

open Filter
open Instances

/-! ## Exact recovery of the zero-nudge theorem -/

/-- The equilibrium response has derivative equal to the task gradient at the
free phase.  This is the solved scalar instance of the equilibrium-propagation
limit theorem. -/
theorem scalarEquilibriumResponse_hasDerivAt (theta target : ℝ) :
    HasDerivAt
      (fun beta : ℝ =>
        scalarEnergyParameterPartial theta
          (scalarNudgedEquilibrium theta target beta))
      (scalarEPTaskGradient theta target) 0 := by
  unfold scalarEnergyParameterPartial scalarNudgedEquilibrium
    scalarEPTaskGradient
  have numerator_deriv :
      HasDerivAt (fun beta : ℝ => theta + beta * target) target 0 := by
    simpa [Function.id_def] using
      ((hasDerivAt_id (0 : ℝ)).mul_const target).const_add theta
  have denominator_deriv :
      HasDerivAt (fun beta : ℝ => 1 + beta) 1 0 := by
    simpa [Function.id_def] using
      (hasDerivAt_id (0 : ℝ)).const_add (1 : ℝ)
  have response_deriv :=
    (numerator_deriv.div denominator_deriv (by norm_num)).const_sub theta
  simpa only [Pi.div_apply, mul_one, zero_mul, add_zero, one_pow, div_one,
    neg_sub] using response_deriv

/-- The one-sided contrast tends to the task gradient through nonzero nudges.
The punctured neighborhood records that the finite estimator is undefined at
the limiting nudge itself. -/
theorem scalarOneSidedEP_tendsto_taskGradient (theta target : ℝ) :
    Tendsto (fun beta => scalarOneSidedEP theta target beta)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (scalarEPTaskGradient theta target)) := by
  have derivative_limit :=
    (scalarEquilibriumResponse_hasDerivAt theta target).tendsto_slope_zero
  simpa only [scalarOneSidedEP, zero_add, smul_eq_mul, inv_mul_eq_div] using
    derivative_limit

/-! ## Exact finite-nudge bias -/

/-- Exact first-order finite-radius bias of the one-sided estimator. -/
theorem scalarOneSidedEP_error_exact
    (theta target beta : ℝ) (beta_ne : beta ≠ 0)
    (denominator_ne : 1 + beta ≠ 0) :
    scalarOneSidedEP theta target beta - scalarEPTaskGradient theta target =
      -(beta / (1 + beta)) * scalarEPTaskGradient theta target := by
  rw [scalarOneSidedEP_formula theta target beta beta_ne denominator_ne]
  unfold scalarEPTaskGradient
  field_simp [denominator_ne]
  ring

/-- Exact second-order finite-radius bias of the symmetric estimator. -/
theorem scalarSymmetricEP_error_exact
    (theta target beta : ℝ) (beta_ne : beta ≠ 0)
    (positive_denominator_ne : 1 + beta ≠ 0)
    (negative_denominator_ne : 1 - beta ≠ 0) :
    scalarSymmetricEP theta target beta - scalarEPTaskGradient theta target =
      beta ^ 2 / (1 - beta ^ 2) * scalarEPTaskGradient theta target := by
  rw [scalarSymmetricEP_formula theta target beta beta_ne
    positive_denominator_ne negative_denominator_ne]
  unfold scalarEPTaskGradient
  have square_denominator_ne : 1 - beta ^ 2 ≠ 0 := by
    rw [show 1 - beta ^ 2 = (1 - beta) * (1 + beta) by ring]
    exact mul_ne_zero negative_denominator_ne positive_denominator_ne
  field_simp [square_denominator_ne]
  ring

/-- Below the sharp radius `1/2`, symmetric nudging has strictly smaller
finite-radius error whenever the task gradient is nonzero. -/
theorem scalarSymmetricEP_error_lt_oneSided_of_radius_lt_half
    (theta target beta : ℝ) (beta_pos : 0 < beta) (beta_lt_half : beta < 1 / 2)
    (gradient_ne : scalarEPTaskGradient theta target ≠ 0) :
    |scalarSymmetricEP theta target beta - scalarEPTaskGradient theta target| <
      |scalarOneSidedEP theta target beta - scalarEPTaskGradient theta target| := by
  have beta_ne : beta ≠ 0 := ne_of_gt beta_pos
  have positive_denominator_ne : 1 + beta ≠ 0 := by positivity
  have negative_denominator_ne : 1 - beta ≠ 0 := by nlinarith
  rw [scalarSymmetricEP_error_exact theta target beta beta_ne
    positive_denominator_ne negative_denominator_ne]
  rw [scalarOneSidedEP_error_exact theta target beta beta_ne
    positive_denominator_ne]
  rw [abs_mul, abs_mul, abs_neg]
  have gradient_abs_pos : 0 < |scalarEPTaskGradient theta target| :=
    abs_pos.mpr gradient_ne
  have positive_denominator_pos : 0 < 1 + beta := by positivity
  have square_denominator_pos : 0 < 1 - beta ^ 2 := by nlinarith
  rw [abs_of_pos (div_pos (sq_pos_of_pos beta_pos) square_denominator_pos)]
  rw [abs_of_pos (div_pos beta_pos positive_denominator_pos)]
  apply mul_lt_mul_of_pos_right _ gradient_abs_pos
  rw [div_lt_div_iff₀ square_denominator_pos positive_denominator_pos]
  nlinarith

/-- At radius `1/2`, the two finite-radius errors are exactly equal. -/
theorem scalarSymmetricEP_half_radius_ties_oneSided :
    |scalarSymmetricEP 2 0 (1 / 2) - scalarEPTaskGradient 2 0| =
      |scalarOneSidedEP 2 0 (1 / 2) - scalarEPTaskGradient 2 0| := by
  norm_num [scalarSymmetricEP, scalarOneSidedEP,
    scalarEnergyParameterPartial, scalarNudgedEquilibrium,
    scalarEPTaskGradient, abs_of_nonneg, abs_of_neg]

/-- Beyond the crossover, symmetric nudging can be strictly worse despite its
second-order local bias. -/
theorem scalarSymmetricEP_three_quarters_worse_than_oneSided :
    |scalarOneSidedEP 2 0 (3 / 4) - scalarEPTaskGradient 2 0| <
      |scalarSymmetricEP 2 0 (3 / 4) - scalarEPTaskGradient 2 0| := by
  norm_num [scalarSymmetricEP, scalarOneSidedEP,
    scalarEnergyParameterPartial, scalarNudgedEquilibrium,
    scalarEPTaskGradient, abs_of_nonneg, abs_of_neg]

/-! ## Stationarity residuals and observed finite-settling estimators -/

/-- Stationarity residual of the declared scalar nudged energy at an observed
state. -/
def scalarEPStationarityResidual
    (theta target beta state : ℝ) : ℝ :=
  (1 + beta) * state - (theta + beta * target)

/-- One-sided contrast formed from arbitrary observed phase states. -/
noncomputable def observedOneSidedEP
    (theta beta freeState nudgedState : ℝ) : ℝ :=
  (scalarEnergyParameterPartial theta nudgedState -
    scalarEnergyParameterPartial theta freeState) / beta

/-- Symmetric contrast formed from arbitrary observed positive- and
negative-nudge phase states. -/
noncomputable def observedSymmetricEP
    (theta beta positiveState negativeState : ℝ) : ℝ :=
  (scalarEnergyParameterPartial theta positiveState -
    scalarEnergyParameterPartial theta negativeState) / (2 * beta)

/-- The stationarity residual is exactly the state error multiplied by the
nudge-dependent curvature. -/
theorem state_sub_equilibrium_eq_residual_div
    (theta target beta state : ℝ) (denominator_ne : 1 + beta ≠ 0) :
    state - scalarNudgedEquilibrium theta target beta =
      scalarEPStationarityResidual theta target beta state / (1 + beta) := by
  unfold scalarNudgedEquilibrium scalarEPStationarityResidual
  field_simp [denominator_ne]

/-- Exact decomposition of observed one-sided credit into finite-nudge bias,
free-phase residual, and nudged-phase residual. -/
theorem observedOneSidedEP_error_exact
    (theta target beta freeState nudgedState : ℝ)
    (beta_ne : beta ≠ 0) (denominator_ne : 1 + beta ≠ 0) :
    observedOneSidedEP theta beta freeState nudgedState -
        scalarEPTaskGradient theta target =
      -(beta / (1 + beta)) * scalarEPTaskGradient theta target +
        (scalarEPStationarityResidual theta target 0 freeState -
          scalarEPStationarityResidual theta target beta nudgedState /
            (1 + beta)) / beta := by
  unfold observedOneSidedEP scalarEnergyParameterPartial
    scalarEPTaskGradient scalarEPStationarityResidual
  field_simp [beta_ne, denominator_ne]
  ring

/-- Executable absolute-error certificate for a finite one-sided run. -/
theorem observedOneSidedEP_error_le
    (theta target beta freeState nudgedState : ℝ)
    (beta_ne : beta ≠ 0) (denominator_ne : 1 + beta ≠ 0) :
    |observedOneSidedEP theta beta freeState nudgedState -
        scalarEPTaskGradient theta target| ≤
      |beta| / |1 + beta| * |scalarEPTaskGradient theta target| +
        (|scalarEPStationarityResidual theta target 0 freeState| +
          |scalarEPStationarityResidual theta target beta nudgedState| /
            |1 + beta|) / |beta| := by
  rw [observedOneSidedEP_error_exact theta target beta freeState nudgedState
    beta_ne denominator_ne]
  calc
    |-(beta / (1 + beta)) * scalarEPTaskGradient theta target +
        (scalarEPStationarityResidual theta target 0 freeState -
          scalarEPStationarityResidual theta target beta nudgedState /
            (1 + beta)) / beta| ≤
        |-(beta / (1 + beta)) * scalarEPTaskGradient theta target| +
          |(scalarEPStationarityResidual theta target 0 freeState -
            scalarEPStationarityResidual theta target beta nudgedState /
              (1 + beta)) / beta| :=
      abs_add_le _ _
    _ =
        |beta| / |1 + beta| * |scalarEPTaskGradient theta target| +
          |scalarEPStationarityResidual theta target 0 freeState -
            scalarEPStationarityResidual theta target beta nudgedState /
              (1 + beta)| / |beta| := by
      rw [abs_mul, abs_neg, abs_div, abs_div]
    _ ≤
        |beta| / |1 + beta| * |scalarEPTaskGradient theta target| +
          (|scalarEPStationarityResidual theta target 0 freeState| +
            |scalarEPStationarityResidual theta target beta nudgedState| /
              |1 + beta|) / |beta| := by
      gcongr
      simpa only [abs_div] using
        abs_sub
          (scalarEPStationarityResidual theta target 0 freeState)
          (scalarEPStationarityResidual theta target beta nudgedState /
            (1 + beta))

/-- Exact decomposition of observed symmetric credit into second-order
finite-nudge bias and the two phase residuals. -/
theorem observedSymmetricEP_error_exact
    (theta target beta positiveState negativeState : ℝ)
    (beta_ne : beta ≠ 0)
    (positive_denominator_ne : 1 + beta ≠ 0)
    (negative_denominator_ne : 1 - beta ≠ 0) :
    observedSymmetricEP theta beta positiveState negativeState -
        scalarEPTaskGradient theta target =
      beta ^ 2 / (1 - beta ^ 2) * scalarEPTaskGradient theta target +
        (scalarEPStationarityResidual theta target (-beta) negativeState /
              (1 - beta) -
            scalarEPStationarityResidual theta target beta positiveState /
              (1 + beta)) / (2 * beta) := by
  have square_denominator_ne : 1 - beta ^ 2 ≠ 0 := by
    rw [show 1 - beta ^ 2 = (1 - beta) * (1 + beta) by ring]
    exact mul_ne_zero negative_denominator_ne positive_denominator_ne
  unfold observedSymmetricEP scalarEnergyParameterPartial
    scalarEPTaskGradient scalarEPStationarityResidual
  field_simp [beta_ne, positive_denominator_ne, negative_denominator_ne,
    square_denominator_ne]
  ring

/-- Executable absolute-error certificate for a finite symmetric run. -/
theorem observedSymmetricEP_error_le
    (theta target beta positiveState negativeState : ℝ)
    (beta_ne : beta ≠ 0)
    (positive_denominator_ne : 1 + beta ≠ 0)
    (negative_denominator_ne : 1 - beta ≠ 0) :
    |observedSymmetricEP theta beta positiveState negativeState -
        scalarEPTaskGradient theta target| ≤
      |beta| ^ 2 / |1 - beta ^ 2| *
          |scalarEPTaskGradient theta target| +
        (|scalarEPStationarityResidual theta target (-beta) negativeState| /
              |1 - beta| +
            |scalarEPStationarityResidual theta target beta positiveState| /
              |1 + beta|) / (2 * |beta|) := by
  rw [observedSymmetricEP_error_exact theta target beta positiveState
    negativeState beta_ne positive_denominator_ne negative_denominator_ne]
  calc
    |beta ^ 2 / (1 - beta ^ 2) * scalarEPTaskGradient theta target +
        (scalarEPStationarityResidual theta target (-beta) negativeState /
              (1 - beta) -
            scalarEPStationarityResidual theta target beta positiveState /
              (1 + beta)) / (2 * beta)| ≤
        |beta ^ 2 / (1 - beta ^ 2) * scalarEPTaskGradient theta target| +
          |(scalarEPStationarityResidual theta target (-beta) negativeState /
                (1 - beta) -
              scalarEPStationarityResidual theta target beta positiveState /
                (1 + beta)) / (2 * beta)| :=
      abs_add_le _ _
    _ =
        |beta| ^ 2 / |1 - beta ^ 2| *
            |scalarEPTaskGradient theta target| +
          |scalarEPStationarityResidual theta target (-beta) negativeState /
                (1 - beta) -
              scalarEPStationarityResidual theta target beta positiveState /
                (1 + beta)| / (2 * |beta|) := by
      rw [abs_mul, abs_div, abs_pow, abs_div, abs_mul]
      norm_num
    _ ≤
        |beta| ^ 2 / |1 - beta ^ 2| *
            |scalarEPTaskGradient theta target| +
          (|scalarEPStationarityResidual theta target (-beta) negativeState| /
                |1 - beta| +
              |scalarEPStationarityResidual theta target beta positiveState| /
                |1 + beta|) / (2 * |beta|) := by
      gcongr
      simpa only [abs_div] using
        abs_sub
          (scalarEPStationarityResidual theta target (-beta) negativeState /
            (1 - beta))
          (scalarEPStationarityResidual theta target beta positiveState /
            (1 + beta))

/-! ## Task-cost response to the nudge -/

/-- Task cost evaluated at the exact scalar nudged equilibrium. -/
noncomputable def scalarNudgedTaskCost
    (theta target beta : ℝ) : ℝ :=
  (scalarNudgedEquilibrium theta target beta - target) ^ 2 / 2

/-- Closed form for the task cost along the exact equilibrium branch. -/
theorem scalarNudgedTaskCost_formula
    (theta target beta : ℝ) (denominator_ne : 1 + beta ≠ 0) :
    scalarNudgedTaskCost theta target beta =
      scalarEPTaskGradient theta target ^ 2 / (2 * (1 + beta) ^ 2) := by
  unfold scalarNudgedTaskCost scalarNudgedEquilibrium scalarEPTaskGradient
  field_simp [denominator_ne]
  ring

/-- Every positive nudge strictly lowers this scalar task cost away from an
already optimal free phase.  This is the solved scalar counterpart of the
source's nonpositive cost-response proposition. -/
theorem scalarNudgedTaskCost_lt_free_of_positive
    (theta target beta : ℝ) (beta_pos : 0 < beta)
    (gradient_ne : scalarEPTaskGradient theta target ≠ 0) :
    scalarNudgedTaskCost theta target beta <
      scalarNudgedTaskCost theta target 0 := by
  rw [scalarNudgedTaskCost_formula theta target beta (by positivity)]
  rw [scalarNudgedTaskCost_formula theta target 0 (by norm_num)]
  have gradient_square_pos :
      0 < scalarEPTaskGradient theta target ^ 2 :=
    sq_pos_of_ne_zero gradient_ne
  have denominator_growth : 2 < 2 * (1 + beta) ^ 2 := by
    nlinarith [sq_nonneg beta]
  exact
    (div_lt_div_iff₀ (by positivity) (by positivity)).2 (by
      nlinarith)

/-- A negative nudge can move in the opposite direction and raise task cost. -/
theorem negative_half_nudge_increases_task_cost :
    scalarNudgedTaskCost 2 0 (-1 / 2) = 8 ∧
      scalarNudgedTaskCost 2 0 0 = 2 ∧
      scalarNudgedTaskCost 2 0 0 < scalarNudgedTaskCost 2 0 (-1 / 2) := by
  norm_num [scalarNudgedTaskCost, scalarNudgedEquilibrium]

/-! ## Sharp implementation boundaries -/

/-- A fixed nonzero phase-state error is amplified like `1 / beta`; taking a
smaller nudge without tighter settling can make the estimator arbitrarily
worse. -/
theorem fixed_free_phase_error_is_inverse_nudge
    (beta : ℝ) (beta_ne : beta ≠ 0) :
    observedOneSidedEP 0 beta 1 0 = 1 / beta := by
  unfold observedOneSidedEP scalarEnergyParameterPartial
  field_simp [beta_ne]
  norm_num

theorem tenth_nudge_with_unit_phase_error_has_error_ten :
    observedOneSidedEP 0 (1 / 10) 1 0 = 10 ∧
      scalarEPTaskGradient 0 0 = 0 := by
  norm_num [observedOneSidedEP, scalarEnergyParameterPartial,
    scalarEPTaskGradient]

/-- At the singular nudge `-1`, the declared scalar stationarity equation loses
state identifiability rather than defining a usable equilibrium branch. -/
theorem negative_one_nudge_residual_independent_of_state
    (theta target state : ℝ) :
    scalarEPStationarityResidual theta target (-1) state = target - theta := by
  simp [scalarEPStationarityResidual]
  ring

#print axioms scalarEquilibriumResponse_hasDerivAt
#print axioms scalarOneSidedEP_tendsto_taskGradient
#print axioms scalarOneSidedEP_error_exact
#print axioms scalarSymmetricEP_error_exact
#print axioms scalarSymmetricEP_error_lt_oneSided_of_radius_lt_half
#print axioms observedOneSidedEP_error_exact
#print axioms observedOneSidedEP_error_le
#print axioms observedSymmetricEP_error_exact
#print axioms observedSymmetricEP_error_le
#print axioms scalarNudgedTaskCost_lt_free_of_positive
#print axioms fixed_free_phase_error_is_inverse_nudge
#print axioms negative_one_nudge_residual_independent_of_state

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.EquilibriumPropagationErrorBudget
