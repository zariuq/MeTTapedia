import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.TruncatedNeumannResidual
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedTruncation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.EnergyDecrementStopping

/-!
# Error-coordinate primary solves with cyclic refinement

This module gives a finite linearized model of the two cycle treatments in an
error-coordinate-primary predictive-coding solver.

For a cycle-transfer operator `A`, exact cyclic correction solves

`y - A y = b`.

Unrolling `U` cycle traversals computes the ordinary truncated Neumann series
`(I + A + ... + A^(U-1)) b`.  A damped state-refinement step with fraction
`α` instead has iteration operator

`Bα = (1 - α) I + α A`

and forcing `α b`.  It reaches the same fixed point, but its finite iterate is
the truncated series of `Bα`, not generally the same series as unrolling.
They coincide at `α = 1`; a scalar fixture separates them otherwise.

The exact omitted-power identities yield geometric credit-error bounds and a
pairwise equivalence budget.  Work profiles then show that accuracy alone does
not determine whether refine or unroll is cheaper.  A second pair of fixtures
shows that the best split between a primary solve and refinement depends on
whether the remaining error comes from the DAG solve or from the cyclic
handoff.

Finally, componentwise numerical tolerance and credit geometry are separated.
A positive rescaling can fail a tight raw tolerance, while a non-collinear
perturbation can pass it.  Numerical equivalence and scientific credit
equivalence must therefore be reported as distinct gates.

The results are exact for a declared linearized cycle operator.  Applying them
to a nonlinear graph requires a regional linearization, basin, readout, and
finite-precision certificate; none is inferred here from telemetry.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CyclicEPCRefinement

noncomputable section

open TruncatedNeumannResidual
open WorkNormalizedTruncation
open scoped InnerProductSpace

section Linear

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-! ## One resolvent, two finite solver paths -/

/-- Unroll a linearized cycle for a fixed number of traversals. -/
def unrolledCycleCorrection
    (cycle : State →L[ℝ] State) (traversals : ℕ) (forcing : State) : State :=
  approximation cycle traversals forcing

/-- The truncated Neumann series is exactly fixed-point iteration from zero. -/
theorem approximation_succ_eq_forcing_add_operator
    (operator : State →L[ℝ] State) (terms : ℕ) (forcing : State) :
    approximation operator (terms + 1) forcing =
      forcing + operator (approximation operator terms forcing) := by
  induction terms with
  | zero => simp [approximation, partialSum]
  | succ terms inductionHypothesis =>
      have hsucceeding :
          approximation operator (Nat.succ terms + 1) forcing =
            approximation operator (terms + 1) forcing +
              (operator ^ (terms + 1)) forcing := by
        simp [approximation, partialSum, Finset.sum_range_succ]
      have hprevious :
          approximation operator (Nat.succ terms) forcing =
            approximation operator terms forcing +
              (operator ^ terms) forcing := by
        simp [approximation, partialSum, Finset.sum_range_succ]
      calc
        approximation operator (Nat.succ terms + 1) forcing =
            approximation operator (terms + 1) forcing +
              (operator ^ (terms + 1)) forcing := hsucceeding
        _ = (forcing + operator (approximation operator terms forcing)) +
              operator ((operator ^ terms) forcing) := by
          rw [inductionHypothesis, pow_succ']
          rfl
        _ = forcing + operator
              (approximation operator terms forcing +
                (operator ^ terms) forcing) := by
          rw [map_add]
          abel
        _ = forcing + operator
              (approximation operator (Nat.succ terms) forcing) := by
          rw [hprevious]

/-- Iteration operator of a damped fixed-point refinement. -/
def dampedCycleOperator
    (fraction : ℝ) (cycle : State →L[ℝ] State) : State →L[ℝ] State :=
  (1 - fraction) • ContinuousLinearMap.id ℝ State + fraction • cycle

@[simp] theorem dampedCycleOperator_apply
    (fraction : ℝ) (cycle : State →L[ℝ] State) (state : State) :
    dampedCycleOperator fraction cycle state =
      (1 - fraction) • state + fraction • cycle state := by
  simp [dampedCycleOperator]

/-- `steps` damped refinement iterations from the zero correction. -/
def refinedCycleCorrection
    (fraction : ℝ) (cycle : State →L[ℝ] State)
    (steps : ℕ) (forcing : State) : State :=
  approximation (dampedCycleOperator fraction cycle) steps
    (fraction • forcing)

/-- One explicit damped refinement transition. -/
def dampedCycleStep
    (fraction : ℝ) (cycle : State →L[ℝ] State)
    (forcing state : State) : State :=
  fraction • forcing + dampedCycleOperator fraction cycle state

/-- The finite series definition is extensionally the actual damped iteration
from zero. -/
theorem refinedCycleCorrection_succ
    (fraction : ℝ) (cycle : State →L[ℝ] State)
    (steps : ℕ) (forcing : State) :
    refinedCycleCorrection fraction cycle (steps + 1) forcing =
      dampedCycleStep fraction cycle forcing
        (refinedCycleCorrection fraction cycle steps forcing) := by
  exact approximation_succ_eq_forcing_add_operator
    (dampedCycleOperator fraction cycle) steps (fraction • forcing)

/-- The damped operator has the same exact solution as the original cycle
equation, after scaling the forcing by the damping fraction. -/
theorem dampedCycle_exactSolution
    (fraction : ℝ) (cycle : State →L[ℝ] State)
    (forcing exact : State)
    (hsolution : exact - cycle exact = forcing) :
    exact - dampedCycleOperator fraction cycle exact = fraction • forcing := by
  calc
    exact - dampedCycleOperator fraction cycle exact =
        fraction • (exact - cycle exact) := by
      rw [dampedCycleOperator_apply]
      module
    _ = fraction • forcing := by rw [hsolution]

/-- Exact omitted-power error for finite cycle unrolling. -/
theorem exact_sub_unrolled_eq_power
    (cycle : State →L[ℝ] State) (traversals : ℕ)
    (forcing exact : State)
    (hsolution : exact - cycle exact = forcing) :
    exact - unrolledCycleCorrection cycle traversals forcing =
      (cycle ^ traversals) exact := by
  exact exactSolution_sub_approximation_eq_power_apply
    cycle traversals forcing exact hsolution

/-- Exact omitted-power error for finite damped refinement. -/
theorem exact_sub_refined_eq_power
    (fraction : ℝ) (cycle : State →L[ℝ] State) (steps : ℕ)
    (forcing exact : State)
    (hsolution : exact - cycle exact = forcing) :
    exact - refinedCycleCorrection fraction cycle steps forcing =
      (dampedCycleOperator fraction cycle ^ steps) exact := by
  exact exactSolution_sub_approximation_eq_power_apply
    (dampedCycleOperator fraction cycle) steps (fraction • forcing) exact
    (dampedCycle_exactSolution fraction cycle forcing exact hsolution)

/-- With no damping, refinement and unrolling are the same finite solver. -/
@[simp] theorem refinedCycleCorrection_one_eq_unrolled
    (cycle : State →L[ℝ] State) (steps : ℕ) (forcing : State) :
    refinedCycleCorrection 1 cycle steps forcing =
      unrolledCycleCorrection cycle steps forcing := by
  simp [refinedCycleCorrection, unrolledCycleCorrection, dampedCycleOperator]

/-! ## Contraction and finite credit error -/

/-- The standard convex-combination bound for the damped iteration operator. -/
theorem dampedCycleOperator_contracts
    {cycle : State →L[ℝ] State} {factor fraction : ℝ}
    (hcycle : ContractsBy cycle factor)
    (hfraction : 0 ≤ fraction)
    (hfraction_le_one : fraction ≤ 1) :
    ContractsBy (dampedCycleOperator fraction cycle)
      ((1 - fraction) + fraction * factor) := by
  intro state
  rw [dampedCycleOperator_apply]
  calc
    ‖(1 - fraction) • state + fraction • cycle state‖ ≤
        ‖(1 - fraction) • state‖ + ‖fraction • cycle state‖ :=
      norm_add_le _ _
    _ = (1 - fraction) * ‖state‖ + fraction * ‖cycle state‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hfraction_le_one),
        abs_of_nonneg hfraction]
    _ ≤ (1 - fraction) * ‖state‖ + fraction * (factor * ‖state‖) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (hcycle state) hfraction) _
    _ = ((1 - fraction) + fraction * factor) * ‖state‖ := by ring

theorem dampedContractionFactor_nonneg
    {factor fraction : ℝ} (hfactor : 0 ≤ factor)
    (hfraction : 0 ≤ fraction) (hfraction_le_one : fraction ≤ 1) :
    0 ≤ (1 - fraction) + fraction * factor := by
  positivity

theorem dampedContractionFactor_lt_one
    {factor fraction : ℝ} (hfactor_lt_one : factor < 1)
    (hfraction_pos : 0 < fraction) :
    (1 - fraction) + fraction * factor < 1 := by
  nlinarith

/-- If a declared norm bound for the cycle operator is at least one, then the
triangle-inequality bound derived for the damped operator is also at least one.
This is a statement about this sufficient certificate, not about the exact norm
or spectrum of the damped operator. -/
theorem dampedContractionFactor_one_le_of_one_le
    {factor fraction : ℝ} (hfactor : 1 ≤ factor) (hfraction : 0 ≤ fraction) :
    1 ≤ (1 - fraction) + fraction * factor := by
  nlinarith

/-- Strict form for the same derived upper bound. -/
theorem dampedContractionFactor_one_lt_of_one_lt
    {factor fraction : ℝ} (hfactor : 1 < factor) (hfraction : 0 < fraction) :
    1 < (1 - fraction) + fraction * factor := by
  nlinarith

/-- The triangle bound obtained from factor `2` and damping `1/10` is
`11/10 > 1`; this fixture deliberately makes no claim about the exact damped
operator. -/
theorem triangleBound_above_one_fixture :
    (1 - (1 / 10 : ℝ)) + (1 / 10) * 2 = 11 / 10 ∧ (1 : ℝ) < 11 / 10 := by
  norm_num

/-! ### Signed spectra: certificate failure is not operator failure -/

/-- A cycle operator with norm factor two and negative real spectrum. -/
noncomputable def negativeTwoCycleOperator : ℝ →L[ℝ] ℝ :=
  (-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

@[simp] theorem negativeTwoCycleOperator_apply (state : ℝ) :
    negativeTwoCycleOperator state = -2 * state := by
  simp [negativeTwoCycleOperator]

theorem negativeTwoCycleOperator_contractsBy_two :
    ContractsBy negativeTwoCycleOperator 2 := by
  intro state
  rw [negativeTwoCycleOperator_apply]
  simp [norm_mul]

/-- Damping by one third cancels `-2 I` exactly. -/
theorem negativeTwoCycle_oneThird_damped_eq_zero :
    dampedCycleOperator (1 / 3) negativeTwoCycleOperator = 0 := by
  apply ContinuousLinearMap.ext
  intro state
  change dampedCycleOperator (1 / 3) negativeTwoCycleOperator state = (0 : ℝ)
  rw [dampedCycleOperator_apply, negativeTwoCycleOperator_apply]
  ring

theorem negativeTwoCycle_oneThird_contractsBy_zero :
    ContractsBy (dampedCycleOperator (1 / 3) negativeTwoCycleOperator) 0 := by
  rw [negativeTwoCycle_oneThird_damped_eq_zero]
  intro state
  simp

/-- The norm-derived triangle bound is `4/3 > 1`, while the exact damped map is
zero.  Therefore failure of that sufficient bound does not establish failure
of damping. -/
theorem triangleBound_above_one_does_not_imply_damped_noncontraction :
    ContractsBy negativeTwoCycleOperator 2 ∧
      (1 - (1 / 3 : ℝ)) + (1 / 3) * 2 = 4 / 3 ∧
      ContractsBy
        (dampedCycleOperator (1 / 3) negativeTwoCycleOperator) 0 := by
  exact ⟨negativeTwoCycleOperator_contractsBy_two, by norm_num,
    negativeTwoCycle_oneThird_contractsBy_zero⟩

/-- A declared eigenvector remains an eigenvector after damping, with the
affinely transformed eigenvalue. -/
theorem dampedCycleOperator_apply_eigenvector
    {cycle : State →L[ℝ] State} {eigenvalue fraction : ℝ}
    {eigenvector : State}
    (heigen : cycle eigenvector = eigenvalue • eigenvector) :
    dampedCycleOperator fraction cycle eigenvector =
      ((1 - fraction) + fraction * eigenvalue) • eigenvector := by
  rw [dampedCycleOperator_apply, heigen]
  module

/-- A nonzero positive real mode with eigenvalue at least one is a genuine
no-rescue hypothesis.  Along that mode every nonnegative damping fraction has
multiplier at least one, so the damped map admits no global norm-contraction
factor below one. -/
theorem no_strict_contraction_of_positive_expanding_eigenvector
    {cycle : State →L[ℝ] State} {eigenvalue fraction factor : ℝ}
    {eigenvector : State}
    (heigenvector : eigenvector ≠ 0)
    (heigen : cycle eigenvector = eigenvalue • eigenvector)
    (heigenvalue : 1 ≤ eigenvalue) (hfraction : 0 ≤ fraction)
    (hfactor : factor < 1) :
    ¬ ContractsBy (dampedCycleOperator fraction cycle) factor := by
  intro contracts
  have coefficientOne :
      1 ≤ (1 - fraction) + fraction * eigenvalue :=
    dampedContractionFactor_one_le_of_one_le heigenvalue hfraction
  have coefficientNonneg :
      0 ≤ (1 - fraction) + fraction * eigenvalue :=
    le_trans zero_le_one coefficientOne
  have eigenvectorNormPos : 0 < ‖eigenvector‖ := norm_pos_iff.mpr heigenvector
  have upper := contracts eigenvector
  rw [dampedCycleOperator_apply_eigenvector heigen, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg coefficientNonneg] at upper
  nlinarith

/-- The scalar map `2 I` is an executable positive-spectrum witness for the
genuine no-rescue condition: every nonnegative damping fraction retains a
mode of magnitude at least one. -/
noncomputable def positiveTwoCycleOperator : ℝ →L[ℝ] ℝ :=
  (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

@[simp] theorem positiveTwoCycleOperator_apply (state : ℝ) :
    positiveTwoCycleOperator state = 2 * state := by
  simp [positiveTwoCycleOperator]

theorem positiveTwoCycle_damping_not_strictly_contracting
    {fraction factor : ℝ} (hfraction : 0 ≤ fraction) (hfactor : factor < 1) :
    ¬ ContractsBy (dampedCycleOperator fraction positiveTwoCycleOperator) factor := by
  apply no_strict_contraction_of_positive_expanding_eigenvector
      (eigenvector := (1 : ℝ)) (eigenvalue := (2 : ℝ))
  · norm_num
  · norm_num [positiveTwoCycleOperator]
  · norm_num
  · exact hfraction
  · exact hfactor

/-- Spectral proxy used by the finite crossover certificate. -/
def unrollErrorBudget
    (factor : ℝ) (traversals : ℕ) (exactNorm : ℝ) : ℝ :=
  factor ^ traversals * exactNorm

/-- Damped-refinement proxy used by the finite crossover certificate. -/
def refinementErrorBudget
    (factor fraction : ℝ) (steps : ℕ) (exactNorm : ℝ) : ℝ :=
  ((1 - fraction) + fraction * factor) ^ steps * exactNorm

/-- For nonzero exact correction, the predicted refine-versus-unroll error
crossover is exactly the comparison of their two power factors. -/
theorem refinementErrorBudget_le_unrollErrorBudget_iff
    {factor fraction exactNorm : ℝ} {traversals steps : ℕ}
    (hexactNorm : 0 < exactNorm) :
    refinementErrorBudget factor fraction steps exactNorm ≤
        unrollErrorBudget factor traversals exactNorm ↔
      ((1 - fraction) + fraction * factor) ^ steps ≤
        factor ^ traversals := by
  simp only [refinementErrorBudget, unrollErrorBudget]
  constructor
  · intro comparison
    exact le_of_mul_le_mul_right comparison hexactNorm
  · intro comparison
    exact mul_le_mul_of_nonneg_right comparison (le_of_lt hexactNorm)

/-- When the declared cycle norm bound is at least one, its derived
triangle-inequality refinement budget cannot certify shrinkage: that upper
budget is no smaller than the starting norm.  The actual damped operator may
still contract, as `negativeTwoCycle_oneThird_contractsBy_zero` shows. -/
theorem refinementErrorBudget_not_below_exact_of_one_le
    {factor fraction exactNorm : ℝ} (steps : ℕ)
    (hfactor : 1 ≤ factor) (hfraction : 0 ≤ fraction)
    (hexactNorm : 0 ≤ exactNorm) :
    exactNorm ≤ refinementErrorBudget factor fraction steps exactNorm := by
  have hdamped : 1 ≤ (1 - fraction) + fraction * factor :=
    dampedContractionFactor_one_le_of_one_le hfactor hfraction
  have hpow : 1 ≤ ((1 - fraction) + fraction * factor) ^ steps :=
    one_le_pow₀ hdamped
  calc
    exactNorm = 1 * exactNorm := (one_mul exactNorm).symm
    _ ≤ ((1 - fraction) + fraction * factor) ^ steps * exactNorm :=
      mul_le_mul_of_nonneg_right hpow hexactNorm

/-- Geometric finite error for cycle unrolling. -/
theorem unrolledCycle_error_le
    {cycle : State →L[ℝ] State} {factor : ℝ}
    (hcycle : ContractsBy cycle factor) (hfactor : 0 ≤ factor)
    (traversals : ℕ) (forcing exact : State)
    (hsolution : exact - cycle exact = forcing) :
    ‖unrolledCycleCorrection cycle traversals forcing - exact‖ ≤
      factor ^ traversals * ‖exact‖ := by
  exact approximation_sub_exactSolution_norm_le
    hcycle hfactor traversals forcing exact hsolution

/-- Geometric finite error for damped refinement. -/
theorem refinedCycle_error_le
    {cycle : State →L[ℝ] State} {factor fraction : ℝ}
    (hcycle : ContractsBy cycle factor)
    (hfactor : 0 ≤ factor) (hfraction : 0 ≤ fraction)
    (hfraction_le_one : fraction ≤ 1)
    (steps : ℕ) (forcing exact : State)
    (hsolution : exact - cycle exact = forcing) :
    ‖refinedCycleCorrection fraction cycle steps forcing - exact‖ ≤
      ((1 - fraction) + fraction * factor) ^ steps * ‖exact‖ := by
  exact approximation_sub_exactSolution_norm_le
    (dampedCycleOperator_contracts hcycle hfraction hfraction_le_one)
    (dampedContractionFactor_nonneg hfactor hfraction hfraction_le_one)
    steps (fraction • forcing) exact
    (dampedCycle_exactSolution fraction cycle forcing exact hsolution)

/-- If both finite paths are certified against the same exact correction,
their pairwise discrepancy is bounded by the sum of the two omitted-power
budgets. -/
theorem unrolled_sub_refined_norm_le
    {cycle : State →L[ℝ] State} {factor fraction : ℝ}
    (hcycle : ContractsBy cycle factor)
    (hfactor : 0 ≤ factor) (hfraction : 0 ≤ fraction)
    (hfraction_le_one : fraction ≤ 1)
    (traversals steps : ℕ) (forcing exact : State)
    (hsolution : exact - cycle exact = forcing) :
    ‖unrolledCycleCorrection cycle traversals forcing -
        refinedCycleCorrection fraction cycle steps forcing‖ ≤
      (factor ^ traversals +
        ((1 - fraction) + fraction * factor) ^ steps) * ‖exact‖ := by
  calc
    ‖unrolledCycleCorrection cycle traversals forcing -
        refinedCycleCorrection fraction cycle steps forcing‖ =
        ‖(unrolledCycleCorrection cycle traversals forcing - exact) +
          (exact - refinedCycleCorrection fraction cycle steps forcing)‖ := by
      congr 1
      abel
    _ ≤ ‖unrolledCycleCorrection cycle traversals forcing - exact‖ +
          ‖exact - refinedCycleCorrection fraction cycle steps forcing‖ :=
      norm_add_le _ _
    _ ≤ factor ^ traversals * ‖exact‖ +
          ((1 - fraction) + fraction * factor) ^ steps * ‖exact‖ := by
      exact add_le_add
        (unrolledCycle_error_le hcycle hfactor traversals forcing exact hsolution)
        (by
          rw [norm_sub_rev]
          exact refinedCycle_error_le hcycle hfactor hfraction
            hfraction_le_one steps forcing exact hsolution)
    _ = (factor ^ traversals +
          ((1 - fraction) + fraction * factor) ^ steps) * ‖exact‖ := by
      ring

end Linear

section Hilbert

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- A damped refinement error budget below the observed finite-credit norm is
a positive-alignment certificate, not merely an energy certificate. -/
theorem refinedCycle_positiveAlignment
    {cycle : State →L[ℝ] State} {factor fraction : ℝ}
    (hcycle : ContractsBy cycle factor)
    (hfactor : 0 ≤ factor) (hfraction : 0 ≤ fraction)
    (hfraction_le_one : fraction ≤ 1)
    (steps : ℕ) (forcing exact : State)
    (hsolution : exact - cycle exact = forcing)
    (hrelative :
      ((1 - fraction) + fraction * factor) ^ steps * ‖exact‖ <
        ‖refinedCycleCorrection fraction cycle steps forcing‖) :
    0 < ⟪exact, refinedCycleCorrection fraction cycle steps forcing⟫_ℝ := by
  apply finiteCredit_positiveAlignment exact
    (refinedCycleCorrection fraction cycle steps forcing)
    (((1 - fraction) + fraction * factor) ^ steps * ‖exact‖)
  · exact refinedCycle_error_le hcycle hfactor hfraction hfraction_le_one
      steps forcing exact hsolution
  · exact hrelative

end Hilbert

/-! ## What an energy-decrement stop must certify -/

section EnergyStopping

open AmortizedInitialization
open AmortizedCreditReadout
open EnergyDecrementStopping

variable {SolverState Credit : Type*}
  [NormedAddCommGroup SolverState] [NormedAddCommGroup Credit]

/-- Energy decrement controls credit only after paying four explicit bridges:
a residual-decrease coefficient, contraction margin, readout Lipschitz
constant, and equilibrium-credit mismatch. -/
theorem energyDecrement_creditError_le
    {energy : SolverState → ℝ} {solver : SolverState → SolverState}
    {target state : SolverState} {coefficient tolerance : ℝ}
    (contraction : ContractionCertificate solver)
    (targetFixed : IsFixedPoint solver target)
    (decrease : ResidualDecreaseCertificate energy solver state coefficient)
    (decrementLe : energy state - energy (solver state) ≤ tolerance)
    (readout : SolverState → Credit) (exactCredit : Credit)
    (K : ℝ) (hK : 0 ≤ K)
    (hreadout : CreditReadoutLipschitzAt readout target K) :
    ‖readout state - exactCredit‖ ≤
      K *
          (Real.sqrt (tolerance / coefficient) /
            (1 - contraction.factor)) +
        ‖readout target - exactCredit‖ := by
  have decrementNonneg : 0 ≤ energy state - energy (solver state) := by
    exact le_trans
      (mul_nonneg decrease.coefficient_pos.le (sq_nonneg _))
      decrease.residual_sq_le_decrease
  have toleranceNonneg : 0 ≤ tolerance := decrementNonneg.trans decrementLe
  have quotientNonneg : 0 ≤ tolerance / coefficient :=
    div_nonneg toleranceNonneg decrease.coefficient_pos.le
  have residualSq := residual_sq_le_tolerance_div decrease decrementLe
  have residualLeSqrt :
      ‖state - solver state‖ ≤ Real.sqrt (tolerance / coefficient) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa [Real.sq_sqrt quotientNonneg] using residualSq
  have rawBound := creditError_le_residual_plus_equilibriumMismatch
    contraction target state targetFixed readout exactCredit K hK hreadout
  calc
    ‖readout state - exactCredit‖ ≤
        K * (‖state - solver state‖ / (1 - contraction.factor)) +
          ‖readout target - exactCredit‖ := rawBound
    _ ≤ K *
          (Real.sqrt (tolerance / coefficient) /
            (1 - contraction.factor)) +
          ‖readout target - exactCredit‖ := by
      have marginPos : 0 < 1 - contraction.factor := by
        linarith [contraction.factor_lt_one]
      gcongr

end EnergyStopping

/-! ## Work and allocation -/

/-- Charged work for comparing a compiled unroll with an adaptive refinement
path. `certificateWork` includes stopping and admission overhead. -/
structure CycleWorkProfile where
  baseWork : ℕ
  unrollTraversalWork : ℕ
  certificateWork : ℕ
  refinementTickWork : ℕ

def CycleWorkProfile.unrollWork
    (profile : CycleWorkProfile) (traversals : ℕ) : ℕ :=
  profile.baseWork + profile.unrollTraversalWork * traversals

def CycleWorkProfile.refineWork
    (profile : CycleWorkProfile) (steps : ℕ) : ℕ :=
  profile.baseWork + profile.certificateWork +
    profile.refinementTickWork * steps

/-- A generic matmul ledger: primary-solver work plus two matmuls for every
active layer and refinement tick. -/
def composedRefinementMatmulWork
    (primaryWork refinementSteps activeDepth : ℕ) : ℕ :=
  primaryWork + 2 * refinementSteps * activeDepth

/-- Minimal ledger separating analytic matmul work from all other charged
execution cost. It intentionally does not identify either field with wall
time. -/
def chargedExecutionCost (matmulWork otherWork : ℕ) : ℕ :=
  matmulWork + otherWork

/-- Matmul ordering alone places no order on total charged cost: the same
analytic pair can be reversed by measured non-matmul work in either arm. -/
theorem matmul_order_does_not_determine_chargedCost :
    (3 : ℕ) < 17 ∧
      chargedExecutionCost 17 0 < chargedExecutionCost 3 100 ∧
      chargedExecutionCost 3 0 < chargedExecutionCost 17 100 := by
  norm_num [chargedExecutionCost]

theorem composedRefinementMatmulWork_le_dense
    {primaryWork refinementSteps activeDepth totalDepth : ℕ}
    (hactive : activeDepth ≤ totalDepth) :
    composedRefinementMatmulWork primaryWork refinementSteps activeDepth ≤
      composedRefinementMatmulWork primaryWork refinementSteps totalDepth := by
  unfold composedRefinementMatmulWork
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left (2 * refinementSteps) hactive) primaryWork

/-- A reusable finite error ledger for a primary solve followed by refinement.
The primary residual reaches the handoff after `primarySteps`; the cycle adds
`cycleError`, and refinement contracts their sum. -/
def composedErrorBudget
    (primaryFactor refinementFactor initialError cycleError : ℝ)
    (primarySteps refinementSteps : ℕ) : ℝ :=
  refinementFactor ^ refinementSteps *
    (primaryFactor ^ primarySteps * initialError + cycleError)

/-- When only primary-solver error remains, spending a fixed toy work budget
on the faster primary contraction is better than spending it on refinement. -/
theorem initialError_prefers_primary_fixture :
    composedErrorBudget (1 / 2) (3 / 4) 1 0 2 0 <
      composedErrorBudget (1 / 2) (3 / 4) 1 0 0 4 := by
  norm_num [composedErrorBudget]

/-- When only the cyclic handoff error remains, primary steps do nothing and
the same fixed toy work budget is better spent on refinement. -/
theorem cycleError_prefers_refinement_fixture :
    composedErrorBudget (1 / 2) (3 / 4) 0 1 0 4 <
      composedErrorBudget (1 / 2) (3 / 4) 0 1 2 0 := by
  norm_num [composedErrorBudget]

/-! ## Exact half-cycle crossover fixtures -/

noncomputable def halfCycleOperator : ℝ →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

theorem halfCycleOperator_contracts :
    ContractsBy halfCycleOperator (1 / 2) := by
  intro state
  simp [halfCycleOperator, Real.norm_eq_abs]

theorem halfCycle_exactSolution :
    (1 : ℝ) - halfCycleOperator 1 = 1 / 2 := by
  norm_num [halfCycleOperator]

/-- Damping changes the finite path: one undamped unroll returns `1/2`, while
one half-damped refinement returns `1/4`. -/
theorem halfDamping_oneStep_ne_unroll :
    refinedCycleCorrection (1 / 2) halfCycleOperator 1 (1 / 2) ≠
      unrolledCycleCorrection halfCycleOperator 1 (1 / 2) := by
  norm_num [refinedCycleCorrection, unrolledCycleCorrection,
    approximation, partialSum, dampedCycleOperator, halfCycleOperator]

/-- Two undamped traversals leave exact error `1/4`. -/
theorem halfCycle_twoUnroll_error :
    |unrolledCycleCorrection halfCycleOperator 2 (1 / 2) - 1| = 1 / 4 := by
  norm_num [unrolledCycleCorrection, approximation, partialSum,
    halfCycleOperator, Finset.sum_range_succ]

/-- Five half-damped refinements leave exact error `(3/4)^5`. -/
theorem halfCycle_fiveRefine_error :
    |refinedCycleCorrection (1 / 2) halfCycleOperator 5 (1 / 2) - 1| =
      (3 / 4 : ℝ) ^ 5 := by
  norm_num [refinedCycleCorrection, approximation, partialSum,
    dampedCycleOperator, halfCycleOperator, Finset.sum_range_succ]

theorem fiveRefinements_more_accurate_than_twoUnrolls :
    |refinedCycleCorrection (1 / 2) halfCycleOperator 5 (1 / 2) - 1| <
      |unrolledCycleCorrection halfCycleOperator 2 (1 / 2) - 1| := by
  rw [halfCycle_fiveRefine_error, halfCycle_twoUnroll_error]
  norm_num

def localRefinementProfile : CycleWorkProfile where
  baseWork := 0
  unrollTraversalWork := 10
  certificateWork := 2
  refinementTickWork := 3

def denseRefinementProfile : CycleWorkProfile where
  baseWork := 0
  unrollTraversalWork := 10
  certificateWork := 2
  refinementTickWork := 5

/-- With a small active frontier, the more accurate five-step refinement is
also cheaper than two unrolled traversals. -/
theorem localRefinement_wins_work_fixture :
    localRefinementProfile.refineWork 5 <
      localRefinementProfile.unrollWork 2 := by
  norm_num [CycleWorkProfile.refineWork, CycleWorkProfile.unrollWork,
    localRefinementProfile]

/-- If the active frontier becomes dense, the same accuracy comparison no
longer implies a work win. -/
theorem denseRefinement_loses_work_fixture :
    denseRefinementProfile.unrollWork 2 <
      denseRefinementProfile.refineWork 5 := by
  norm_num [CycleWorkProfile.refineWork, CycleWorkProfile.unrollWork,
    denseRefinementProfile]

/-! ## Numerical tolerance is not credit-geometry equivalence -/

abbrev Credit2 := Fin 2 → ℝ

/-- Standard componentwise absolute-plus-relative tolerance. -/
def ComponentwiseClose
    (absoluteTolerance relativeTolerance : ℝ)
    (reference candidate : Credit2) : Prop :=
  ∀ index,
    |candidate index - reference index| ≤
      absoluteTolerance + relativeTolerance * |reference index|

/-- Same nonzero ray, retaining direction while allowing positive scale. -/
def PositiveCollinear (reference candidate : Credit2) : Prop :=
  ∃ scale : ℝ, 0 < scale ∧ candidate = scale • reference

def referenceCredit : Credit2 := ![1, 0]

def doubledReferenceCredit : Credit2 := ![2, 0]

def tinyRotatedCredit : Credit2 := ![1, 1 / 20000]

/-- A directionally identical positive rescaling fails a tight numerical
tolerance. Raw tolerance is not necessary for direction equivalence. -/
theorem positiveScale_fails_tightTolerance :
    PositiveCollinear referenceCredit doubledReferenceCredit ∧
      ¬ ComponentwiseClose 0 (1 / 10000)
        referenceCredit doubledReferenceCredit := by
  constructor
  · refine ⟨2, by norm_num, ?_⟩
    funext index
    fin_cases index <;>
      norm_num [referenceCredit, doubledReferenceCredit]
  · intro close
    have coordinate := close 0
    norm_num [ComponentwiseClose, referenceCredit, doubledReferenceCredit] at coordinate

/-- A non-collinear perturbation passes the same order of componentwise
tolerance. Raw tolerance is not sufficient for direction equivalence. -/
theorem tinyRotation_passes_tolerance_not_collinear :
    ComponentwiseClose (1 / 10000) 0 referenceCredit tinyRotatedCredit ∧
      ¬ PositiveCollinear referenceCredit tinyRotatedCredit := by
  constructor
  · intro index
    fin_cases index <;>
      norm_num [ComponentwiseClose, referenceCredit, tinyRotatedCredit]
  · rintro ⟨scale, hscale, equality⟩
    have first := congrFun equality 0
    have second := congrFun equality 1
    norm_num [referenceCredit, tinyRotatedCredit] at first second

#print axioms dampedCycle_exactSolution
#print axioms approximation_succ_eq_forcing_add_operator
#print axioms refinedCycleCorrection_succ
#print axioms exact_sub_unrolled_eq_power
#print axioms exact_sub_refined_eq_power
#print axioms refinedCycleCorrection_one_eq_unrolled
#print axioms dampedCycleOperator_contracts
#print axioms triangleBound_above_one_does_not_imply_damped_noncontraction
#print axioms no_strict_contraction_of_positive_expanding_eigenvector
#print axioms positiveTwoCycle_damping_not_strictly_contracting
#print axioms refinementErrorBudget_le_unrollErrorBudget_iff
#print axioms unrolledCycle_error_le
#print axioms refinedCycle_error_le
#print axioms unrolled_sub_refined_norm_le
#print axioms refinedCycle_positiveAlignment
#print axioms energyDecrement_creditError_le
#print axioms composedRefinementMatmulWork_le_dense
#print axioms matmul_order_does_not_determine_chargedCost
#print axioms initialError_prefers_primary_fixture
#print axioms cycleError_prefers_refinement_fixture
#print axioms halfDamping_oneStep_ne_unroll
#print axioms fiveRefinements_more_accurate_than_twoUnrolls
#print axioms localRefinement_wins_work_fixture
#print axioms denseRefinement_loses_work_fixture
#print axioms positiveScale_fails_tightTolerance
#print axioms tinyRotation_passes_tolerance_not_collinear

end

end CyclicEPCRefinement

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
