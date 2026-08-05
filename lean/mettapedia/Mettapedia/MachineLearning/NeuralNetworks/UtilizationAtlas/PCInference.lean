import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.BeliefFrontier
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.OperatorStability
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.SharedLatentDAG

/-!
# Predictive-coding inference licenses

This file separates three questions that are often conflated: whether an
equilibrium is the right answer, whether a finite inference budget reaches the
required tolerance, and what serial work and synchronized parallel latency the
run costs.  Exact linear-Gaussian equilibrium correctness is transported from
the operator model.  A scalar half-relaxation supplies exact finite-residual,
risk, and minimal-sweep results.  The pre-existing nonlinear bandwidth theorem
then rules out a strict exact digital-latency advantage for a unit-bandwidth
chain.  A scalar expansive relaxation supplies the negative divergence case.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Filter
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Exact equilibrium correctness -/

/-- An exact operator-level PC license carries both the equilibrium premise
and its Bayesian conclusion. -/
structure ExactOperatorPCInferenceLicense
    {Latent Residual : Type*}
    [Fintype Latent] [DecidableEq Latent]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Latent Residual)
    (state : LinearGaussianOperatorSpace Latent) : Prop where
  equilibrium : model.Equilibrium state
  posteriorCorrect : state = model.posteriorMean

/-- Every declared linear-Gaussian equilibrium receives an exact posterior
license. -/
theorem ExactOperatorPCInferenceLicense.ofEquilibrium
    {Latent Residual : Type*}
    [Fintype Latent] [DecidableEq Latent]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Latent Residual)
    (state : LinearGaussianOperatorSpace Latent)
    (hequilibrium : model.Equilibrium state) :
    ExactOperatorPCInferenceLicense model state := by
  exact ⟨hequilibrium,
    (model.equilibrium_iff_eq_posteriorMean state).mp hequilibrium⟩

/-- The posterior mean itself has an exact PC inference license. -/
theorem posteriorMean_exactPCInferenceLicense
    {Latent Residual : Type*}
    [Fintype Latent] [DecidableEq Latent]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Latent Residual) :
    ExactOperatorPCInferenceLicense model model.posteriorMean := by
  apply ExactOperatorPCInferenceLicense.ofEquilibrium
  exact (model.equilibrium_iff_eq_posteriorMean model.posteriorMean).2 rfl

/-! ## A fully quantified finite-sweep model -/

/-- One contractive scalar inference sweep, retaining half of the current
error about the target equilibrium. -/
noncomputable def halfRelaxationStep (target state : ℝ) : ℝ :=
  target + (1 / 2) * (state - target)

theorem halfRelaxationStep_iterate_exact
    (target initial : ℝ) (sweeps : ℕ) :
    (halfRelaxationStep target)^[sweeps] initial =
      target + (1 / 2 : ℝ) ^ sweeps * (initial - target) := by
  induction sweeps with
  | zero => simp
  | succ sweeps ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      unfold halfRelaxationStep
      ring

/-- Absolute equilibrium residual after a fixed sweep budget. -/
noncomputable def halfRelaxationResidual
    (target initial : ℝ) (sweeps : ℕ) : ℝ :=
  |(halfRelaxationStep target)^[sweeps] initial - target|

/-- Squared estimation risk induced by the residual. -/
noncomputable def halfRelaxationRisk
    (target initial : ℝ) (sweeps : ℕ) : ℝ :=
  halfRelaxationResidual target initial sweeps ^ 2

theorem halfRelaxationResidual_exact
    (target initial : ℝ) (sweeps : ℕ) :
    halfRelaxationResidual target initial sweeps =
      (1 / 2 : ℝ) ^ sweeps * |initial - target| := by
  rw [halfRelaxationResidual, halfRelaxationStep_iterate_exact]
  calc
    |target + (1 / 2 : ℝ) ^ sweeps * (initial - target) - target| =
        |(1 / 2 : ℝ) ^ sweeps * (initial - target)| := by ring_nf
    _ = (1 / 2 : ℝ) ^ sweeps * |initial - target| := by
      rw [abs_mul, abs_pow]
      norm_num

/-- Every positive tolerance is reached after finitely many half-relaxation
sweeps. -/
theorem halfRelaxation_exists_finite_tolerance
    (target initial tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∃ sweeps : ℕ,
      halfRelaxationResidual target initial sweeps < tolerance := by
  by_cases hequal : initial = target
  · refine ⟨0, ?_⟩
    simpa [halfRelaxationResidual, hequal] using htolerance
  · have hdistance : 0 < |initial - target| :=
      abs_pos.mpr (sub_ne_zero.mpr hequal)
    obtain ⟨sweeps, hsweeps⟩ :=
      exists_pow_lt_of_lt_one (div_pos htolerance hdistance)
        (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨sweeps, ?_⟩
    rw [halfRelaxationResidual_exact]
    exact (lt_div_iff₀ hdistance).mp hsweeps

/-- The same finite count controls squared estimation risk. -/
theorem halfRelaxation_exists_finite_residual_and_risk
    (target initial tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∃ sweeps : ℕ,
      halfRelaxationResidual target initial sweeps < tolerance ∧
        halfRelaxationRisk target initial sweeps < tolerance ^ 2 := by
  obtain ⟨sweeps, hresidual⟩ :=
    halfRelaxation_exists_finite_tolerance target initial tolerance htolerance
  refine ⟨sweeps, hresidual, ?_⟩
  unfold halfRelaxationRisk
  exact (sq_lt_sq₀ (abs_nonneg _) htolerance.le).2 hresidual

/-- Least sweep count meeting a declared positive residual tolerance. -/
noncomputable def minimalHalfRelaxationSweeps
    (target initial tolerance : ℝ) (htolerance : 0 < tolerance) : ℕ :=
  Nat.find
    (halfRelaxation_exists_finite_tolerance
      target initial tolerance htolerance)

theorem minimalHalfRelaxationSweeps_sufficient
    (target initial tolerance : ℝ) (htolerance : 0 < tolerance) :
    halfRelaxationResidual target initial
        (minimalHalfRelaxationSweeps target initial tolerance htolerance) <
      tolerance := by
  exact Nat.find_spec
    (halfRelaxation_exists_finite_tolerance
      target initial tolerance htolerance)

theorem minimalHalfRelaxationSweeps_le_of_sufficient
    (target initial tolerance : ℝ) (htolerance : 0 < tolerance)
    (sweeps : ℕ)
    (hsufficient : halfRelaxationResidual target initial sweeps < tolerance) :
    minimalHalfRelaxationSweeps target initial tolerance htolerance ≤ sweeps := by
  exact Nat.find_min'
    (halfRelaxation_exists_finite_tolerance
      target initial tolerance htolerance) hsufficient

theorem below_minimalHalfRelaxationSweeps_insufficient
    (target initial tolerance : ℝ) (htolerance : 0 < tolerance)
    (sweeps : ℕ)
    (hbelow : sweeps <
      minimalHalfRelaxationSweeps target initial tolerance htolerance) :
    ¬ halfRelaxationResidual target initial sweeps < tolerance := by
  exact Nat.find_min
    (halfRelaxation_exists_finite_tolerance
      target initial tolerance htolerance) hbelow

/-! ## Correctness, budget, and cost are separate obligations -/

/-- A sweep count fits a separately declared inference budget. -/
structure InferenceBudgetCertificate (sweeps budget : ℕ) : Prop where
  withinBudget : sweeps ≤ budget

/-- Exact digital cost accounting for a synchronized local relaxation. -/
structure DigitalInferenceCost where
  serialWork : ℕ
  parallelLatency : ℕ
  deriving DecidableEq, Repr

/-- Cost of `sweeps` synchronized rounds over `activeNodes` local workers,
with one unit of parallel phase latency per sweep. -/
def synchronizedLocalCost (sweeps activeNodes : ℕ) : DigitalInferenceCost where
  serialWork := sweeps * activeNodes
  parallelLatency := sweeps

/-- A combined license deliberately keeps outcome correctness, budget, and
cost in distinct fields. -/
structure PCInferenceLicense
    (correctness : Prop) (sweeps budget activeNodes : ℕ) : Prop where
  correctnessProof : correctness
  budgetProof : InferenceBudgetCertificate sweeps budget
  serialWorkExact :
    (synchronizedLocalCost sweeps activeNodes).serialWork =
      sweeps * activeNodes
  parallelLatencyExact :
    (synchronizedLocalCost sweeps activeNodes).parallelLatency = sweeps

/-- A finite-sweep approximate license checks the actual residual and budget;
it does not upgrade approximation to equilibrium equality. -/
structure ApproximatePCInferenceLicense
    (target initial tolerance : ℝ) (sweeps budget : ℕ) : Prop where
  tolerancePositive : 0 < tolerance
  residualWithinTolerance :
    halfRelaxationResidual target initial sweeps < tolerance
  budget : InferenceBudgetCertificate sweeps budget

theorem minimalHalfRelaxation_approximateLicense
    (target initial tolerance : ℝ) (htolerance : 0 < tolerance)
    (budget : ℕ)
    (hbudget :
      minimalHalfRelaxationSweeps target initial tolerance htolerance ≤ budget) :
    ApproximatePCInferenceLicense target initial tolerance
      (minimalHalfRelaxationSweeps target initial tolerance htolerance) budget := by
  exact ⟨htolerance,
    minimalHalfRelaxationSweeps_sufficient target initial tolerance htolerance,
    ⟨hbudget⟩⟩

/-! ## Finite propagation speed and exact digital latency -/

/-- Finite-speed license: after `sweeps`, a bandwidth-`w` rule depends on at
most radius `sweeps * w`. -/
theorem pcFiniteSpeed_distance_le_sweeps_mul_bandwidth
    (distance bandwidth sweeps : ℕ)
    (step : PCState (distance + 1) → PCState (distance + 1))
    (hbandwidth : HasChainBandwidth step bandwidth)
    (hsettleZero :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 0) =
        pcStateOfInterior distance 0 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 0 0))
    (hsettleOne :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 1) =
        pcStateOfInterior distance 1 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 1 0)) :
    distance ≤ sweeps * bandwidth :=
  bandwidth_rule_exact_unitChainPosterior_requires_reach
    distance bandwidth sweeps step hbandwidth hsettleZero hsettleOne

/-- Reference latency of a layerwise exact digital dependency path. -/
def layerwiseDigitalLatency (distance : ℕ) : ℕ := distance

/-- Exact unit-bandwidth settling cannot have strictly lower synchronized
digital latency than the dependency-path depth. -/
theorem exactUnitBandwidthPC_no_strictDigitalLatencyAdvantage
    (distance sweeps : ℕ)
    (step : PCState (distance + 1) → PCState (distance + 1))
    (hbandwidth : HasChainBandwidth step 1)
    (hsettleZero :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 0) =
        pcStateOfInterior distance 0 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 0 0))
    (hsettleOne :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 1) =
        pcStateOfInterior distance 1 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 1 0)) :
    ¬ (synchronizedLocalCost sweeps (distance + 2)).parallelLatency <
        layerwiseDigitalLatency distance := by
  have hreach := pcFiniteSpeed_distance_le_sweeps_mul_bandwidth
    distance 1 sweeps step hbandwidth hsettleZero hsettleOne
  simp [synchronizedLocalCost, layerwiseDigitalLatency] at hreach ⊢
  omega

theorem synchronizedLocalCost_serial_parallel_exact
    (sweeps activeNodes : ℕ) :
    (synchronizedLocalCost sweeps activeNodes).serialWork =
        sweeps * activeNodes ∧
      (synchronizedLocalCost sweeps activeNodes).parallelLatency = sweeps := by
  exact ⟨rfl, rfl⟩

/-! ## DAG topology license -/

/-- A DAG topology license carries an equilibrium and the complete
parent-occurrence aggregation law at every free latent. -/
structure DAGPCInferenceLicense
    {Node Edge : Type*} [Fintype Node] [Fintype Edge] [DecidableEq Node]
    (graph : SharedLatentDAG Node Edge)
    (boundary state : Node → ℝ) : Prop where
  equilibrium : dagEquilibrium graph boundary state
  parentAggregation : ∀ node, node ∉ graph.clamped →
    dagResidualForce graph state node =
      dagParentErrorAggregate graph state node

theorem DAGPCInferenceLicense.ofEquilibrium
    {Node Edge : Type*} [Fintype Node] [Fintype Edge] [DecidableEq Node]
    (graph : SharedLatentDAG Node Edge)
    (boundary state : Node → ℝ)
    (hequilibrium : dagEquilibrium graph boundary state) :
    DAGPCInferenceLicense graph boundary state := by
  exact ⟨hequilibrium, fun node hfree =>
    sharedDAGEquilibriumError_satisfies_parentAggregationRecursion
      graph boundary state node hfree hequilibrium⟩

theorem multiParentDAG_pcInferenceLicense :
    DAGPCInferenceLicense dagMultiParentGraph dagMultiParentBoundary
      dagMultiParentEquilibriumState :=
  DAGPCInferenceLicense.ofEquilibrium _ _ _
    dagMultiParentEquilibriumState_is_equilibrium

/-! ## Explicit inference divergence -/

/-- Expansive relaxation retaining twice the current equilibrium error. -/
noncomputable def expansiveRelaxationStep (target state : ℝ) : ℝ :=
  target + 2 * (state - target)

theorem expansiveRelaxationStep_iterate_exact
    (target initial : ℝ) (sweeps : ℕ) :
    (expansiveRelaxationStep target)^[sweeps] initial =
      target + (2 : ℝ) ^ sweeps * (initial - target) := by
  induction sweeps with
  | zero => simp
  | succ sweeps ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      unfold expansiveRelaxationStep
      ring

/-- Negative fixture: from unit residual, the unstable inference residual
diverges to infinity instead of converging to the zero equilibrium. -/
theorem expansiveRelaxation_divergent :
    Tendsto
      (fun sweeps : ℕ =>
        |(expansiveRelaxationStep 0)^[sweeps] 1 - 0|)
      atTop atTop := by
  have hpowers : Tendsto (fun sweeps : ℕ => (2 : ℝ) ^ sweeps) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa [expansiveRelaxationStep_iterate_exact] using hpowers

/-! ## T3 crown -/

/-- T3 packages exact equilibrium correctness, finite approximate convergence,
minimality, distinct budget/cost accounting, finite propagation, DAG topology,
and a divergent negative fixture without identifying these obligations. -/
theorem pcInference_frontier_crown :
    (∀ target initial tolerance : ℝ, 0 < tolerance →
      ∃ sweeps : ℕ,
        halfRelaxationResidual target initial sweeps < tolerance ∧
          halfRelaxationRisk target initial sweeps < tolerance ^ 2) ∧
    (∀ target initial tolerance : ℝ, ∀ htolerance : 0 < tolerance,
      halfRelaxationResidual target initial
          (minimalHalfRelaxationSweeps target initial tolerance htolerance) <
        tolerance) ∧
    Tendsto
      (fun sweeps : ℕ =>
        |(expansiveRelaxationStep 0)^[sweeps] 1 - 0|)
      atTop atTop := by
  exact ⟨halfRelaxation_exists_finite_residual_and_risk,
    minimalHalfRelaxationSweeps_sufficient,
    expansiveRelaxation_divergent⟩

#print axioms posteriorMean_exactPCInferenceLicense
#print axioms halfRelaxation_exists_finite_residual_and_risk
#print axioms below_minimalHalfRelaxationSweeps_insufficient
#print axioms exactUnitBandwidthPC_no_strictDigitalLatencyAdvantage
#print axioms multiParentDAG_pcInferenceLicense
#print axioms expansiveRelaxation_divergent
#print axioms pcInference_frontier_crown

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
