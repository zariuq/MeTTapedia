import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.BPSubsumptionPartition
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FiniteSettlingGradientGap
import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.AdapterReachability

/-!
# Certified online adaptation for frozen-network adapters

This license joins the finite-PC, constrained-BP, online-regret, and
Jacobian-reachability results without widening their scope.  The certified
models are:

* strongly-convex smooth latent settling on a real Hilbert space with a
  Lipschitz adapter-gradient readout;
* beta-smooth retention plus metric-projected linearized constraints;
* general convex-smooth projected online adapter losses; and
* a finite-dimensional Jacobian local model of a frozen nonlinear parent.

Scalar quadratics remain below as exact positive/negative fixtures and as
closed-form witnesses for BP+, GEM, metric choice, stationary optima, and
abrupt drift.  They are not the scope of the main licenses.

No theorem below promotes a Jacobian-local certificate to a global claim about
a trained nonlinear Transformer.  Such a promotion requires an independently
verified remainder bound or an empirical evaluation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
open scoped InnerProductSpace

/-- Proof-bearing synthesis of the online-adaptation boundary.  Each field is
an actual theorem from its native layer, not a restated assumption. -/
structure CertifiedOnlineAdaptationLicense : Prop where
  hilbertContractionRate :
    ∀ mu L rate : ℝ,
      0 < rate → rate * L ^ 2 < 2 * mu →
      0 ≤ hilbertSettlingContractionSq mu L rate →
        hilbertSettlingContraction mu L rate < 1
  hilbertFiniteSettlingGap :
    ∀ {Latent Adapter : Type*}
      [NormedAddCommGroup Latent] [InnerProductSpace ℝ Latent]
      [NormedAddCommGroup Adapter]
      {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L),
      0 ≤ L → 0 ≤ rate →
      0 ≤ hilbertSettlingContractionSq mu L rate →
      ∀ (target initial : Latent), model.gradient target = 0 →
      ∀ (gradientReadout : Latent → Adapter) (bpGradient : Adapter),
      0 ≤ K →
      HilbertGradientReadoutLipschitzAt gradientReadout target K →
      ∀ sweeps : ℕ,
      ‖gradientReadout
          ((hilbertSettlingStep model rate)^[sweeps] initial) - bpGradient‖ ≤
        K * hilbertSettlingContraction mu L rate ^ sweeps *
            ‖initial - target‖ +
          hilbertEquilibriumGradientMismatch gradientReadout target bpGradient
  hilbertZeroMismatch :
    ∀ {Latent Adapter : Type*}
      [NormedAddCommGroup Latent] [InnerProductSpace ℝ Latent]
      [NormedAddCommGroup Adapter]
      {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L),
      0 ≤ L → 0 ≤ rate →
      0 ≤ hilbertSettlingContractionSq mu L rate →
      ∀ (target initial : Latent), model.gradient target = 0 →
      ∀ (gradientReadout : Latent → Adapter) (bpGradient : Adapter),
      0 ≤ K →
      HilbertGradientReadoutLipschitzAt gradientReadout target K →
      gradientReadout target = bpGradient →
      ∀ sweeps : ℕ,
      ‖gradientReadout
          ((hilbertSettlingStep model rate)^[sweeps] initial) - bpGradient‖ ≤
        K * hilbertSettlingContraction mu L rate ^ sweeps *
          ‖initial - target‖
  minimumHilbertDepth :
    ∀ {Latent : Type*} [NormedAddCommGroup Latent]
      (mu L rate K tolerance : ℝ) (initial target : Latent)
      (hK : 0 ≤ K) (hrate : 0 < rate)
      (hstable : rate * L ^ 2 < 2 * mu)
      (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
      (htolerance : 0 < tolerance),
      hilbertFiniteSettlingRemainder mu L rate K initial target
          (minimumHilbertSettlingDepth mu L rate K tolerance initial target
            hK hrate hstable hcoefficient htolerance) < tolerance
  minimumHilbertDepthActualGap :
    ∀ {Latent Adapter : Type*}
      [NormedAddCommGroup Latent] [InnerProductSpace ℝ Latent]
      [NormedAddCommGroup Adapter]
      {mu L rate K : ℝ} (model : StrongSmoothLatentEnergy Latent mu L),
      0 ≤ L →
      ∀ (hrate : 0 < rate) (hstable : rate * L ^ 2 < 2 * mu),
      ∀ (hcoefficient : 0 ≤ hilbertSettlingContractionSq mu L rate)
        (target initial : Latent), model.gradient target = 0 →
      ∀ (gradientReadout : Latent → Adapter) (bpGradient : Adapter),
      ∀ (hK : 0 ≤ K),
      HilbertGradientReadoutLipschitzAt gradientReadout target K →
      gradientReadout target = bpGradient →
      ∀ (tolerance : ℝ) (htolerance : 0 < tolerance),
      let depth := minimumHilbertSettlingDepth mu L rate K tolerance
        initial target hK hrate hstable hcoefficient htolerance
      ‖gradientReadout
          ((hilbertSettlingStep model rate)^[depth] initial) - bpGradient‖ <
        tolerance
  smoothRetentionDescent :
    ∀ {Adapter : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter] [CompleteSpace Adapter]
      {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
      (parameter update : Adapter),
      model.loss (parameter + update) ≤ model.loss parameter +
        ⟪model.gradient parameter, update⟫_ℝ + beta / 2 * ‖update‖ ^ 2
  smoothRetentionSafety :
    ∀ {Adapter : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter] [CompleteSpace Adapter]
      {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
      (parameter update : Adapter),
      RetentionTrustRegionSafeVector (model.gradient parameter) beta update →
        model.loss (parameter + update) ≤ model.loss parameter
  smoothRetentionBacktracking :
    ∀ {Adapter : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter] [CompleteSpace Adapter]
      {beta : ℝ} (model : SmoothRetentionLoss Adapter beta)
      (parameter direction : Adapter) (initial shrink : ℝ),
      0 < beta → ⟪model.gradient parameter, direction⟫_ℝ < 0 →
      0 < initial → 0 < shrink → shrink < 1 →
      ∃ sweeps : ℕ,
        model.loss
            (parameter + (initial * shrink ^ sweeps) • direction) ≤
          model.loss parameter
  metricProjectionCharacterization :
    ∀ {Adapter Task : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter]
      (metric : AdapterMetric Adapter)
      (retentionGradients : Task → Adapter)
      (radius : ℝ) (proposed chosen : Adapter),
      MetricProjectionCertificate metric retentionGradients radius proposed chosen ↔
        IsMetricProjectionMinimum metric retentionGradients radius proposed chosen
  metricProjectionMinimum :
    ∀ {Adapter Task : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter]
      (metric : AdapterMetric Adapter)
      (retentionGradients : Task → Adapter)
      (radius : ℝ) (proposed chosen : Adapter),
      MetricProjectionCertificate metric retentionGradients radius proposed chosen →
      ∀ candidate, MetricUpdateFeasible retentionGradients radius candidate →
        metric.deviationSq chosen proposed ≤
          metric.deviationSq candidate proposed
  ogdMinimumChange :
    ∀ {Index : Type*} [Fintype Index]
      (retentionGradient proposed candidate : Index → ℝ),
      retentionGradient ⬝ᵥ retentionGradient ≠ 0 →
      retentionGradient ⬝ᵥ candidate = 0 →
      euclideanDeviationSq
          (ogdSingleGradientUpdate retentionGradient proposed) proposed ≤
        euclideanDeviationSq candidate proposed
  spanningRetentionKillsPlasticity :
    ∀ {Index : Type*} [Fintype Index]
      {Task : Type*} (retentionGradients : Task → Index → ℝ)
      (currentGradient : Index → ℝ),
      currentGradient ∈ Submodule.span ℝ (Set.range retentionGradients) →
      ¬ ∃ update,
        PreservesAllLinearizedTasks retentionGradients update ∧
          currentGradient ⬝ᵥ update < 0
  generalProjectedDynamicRegret :
    ∀ {Adapter : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter]
      (beta : ℕ → ℝ)
      (model : ∀ t, ConvexSmoothAdapterLoss Adapter (beta t))
      {feasible : Adapter → Prop} (projection : OnlineProjection Adapter feasible)
      (parameter comparator direction : ℕ → Adapter)
      (epsilon : ℕ → ℝ) (rate diameter bound : ℝ) (horizon : ℕ),
      0 < rate → 0 ≤ bound →
      (∀ t ≤ horizon, feasible (comparator t)) →
      (∀ t < horizon,
        parameter (t + 1) =
          projectedOnlineStep projection rate (parameter t) (direction t)) →
      (∀ t < horizon,
        ApproximateDirectionCertificate
          ((model t).gradient (parameter t)) (direction t)
          (parameter t - comparator t) bound (epsilon t)) →
      (∀ t < horizon,
        ‖parameter (t + 1) - comparator t‖ ≤ diameter ∧
        ‖parameter (t + 1) - comparator (t + 1)‖ ≤ diameter) →
      projectedDynamicRegret (fun t => (model t).loss)
          parameter comparator horizon ≤
        ‖parameter 0 - comparator 0‖ ^ 2 / (2 * rate) +
          diameter / rate * adapterOptimumPathLength comparator horizon +
          horizon * (rate * bound ^ 2 / 2) +
          ∑ t ∈ Finset.range horizon, epsilon t
  exactDirectionMatchesBP :
    ∀ {Adapter : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter]
      (gradient displacement : Adapter) (bound : ℝ),
      ‖gradient‖ ≤ bound →
        ApproximateDirectionCertificate gradient gradient displacement bound 0
  gradientGapProjectedDynamicRegret :
    ∀ {Adapter : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter]
      (beta : ℕ → ℝ)
      (model : ∀ t, ConvexSmoothAdapterLoss Adapter (beta t))
      {feasible : Adapter → Prop} (projection : OnlineProjection Adapter feasible)
      (parameter comparator direction : ℕ → Adapter)
      (gradientError : ℕ → ℝ) (rate diameter bound : ℝ) (horizon : ℕ),
      0 < rate → 0 ≤ bound →
      (∀ t ≤ horizon, feasible (comparator t)) →
      (∀ t < horizon,
        parameter (t + 1) =
          projectedOnlineStep projection rate (parameter t) (direction t)) →
      (∀ t < horizon, ‖direction t‖ ≤ bound) →
      (∀ t < horizon, 0 ≤ gradientError t) →
      (∀ t < horizon,
        ‖(model t).gradient (parameter t) - direction t‖ ≤ gradientError t) →
      (∀ t < horizon, ‖parameter t - comparator t‖ ≤ diameter) →
      (∀ t < horizon,
        ‖parameter (t + 1) - comparator t‖ ≤ diameter ∧
        ‖parameter (t + 1) - comparator (t + 1)‖ ≤ diameter) →
      projectedDynamicRegret (fun t => (model t).loss)
          parameter comparator horizon ≤
        ‖parameter 0 - comparator 0‖ ^ 2 / (2 * rate) +
          diameter / rate * adapterOptimumPathLength comparator horizon +
          horizon * (rate * bound ^ 2 / 2) +
          ∑ t ∈ Finset.range horizon, gradientError t * diameter
  finiteSettlingGap :
    ∀ (rate curvature target initial K bpGradient : ℝ)
      (gradientReadout : ℝ → ℝ) (sweeps : ℕ),
      GradientReadoutLipschitzAt gradientReadout target K →
      |gradientReadout
          ((quadraticSettlingStep rate curvature target)^[sweeps] initial) -
          bpGradient| ≤
        K * settlingContraction rate curvature ^ sweeps * |initial - target| +
          equilibriumGradientMismatch gradientReadout target bpGradient
  finiteSettlingTolerance :
    ∀ (rate curvature initial target K tolerance : ℝ),
      0 ≤ K → 0 < rate * curvature → rate * curvature < 2 → 0 < tolerance →
        ∃ sweeps : ℕ,
          finiteSettlingRemainder rate curvature initial target K sweeps <
            tolerance
  minimumSettlingDepthSufficient :
    ∀ (rate curvature initial target K tolerance : ℝ)
      (hK : 0 ≤ K)
      (hpositive : 0 < rate * curvature)
      (hbelow : rate * curvature < 2)
      (htolerance : 0 < tolerance),
      finiteSettlingRemainder rate curvature initial target K
          (minimumSettlingDepth rate curvature initial target K tolerance
            hK hpositive hbelow htolerance) < tolerance
  unstableSettlingBoundary : ∀ sweeps : ℕ,
    ¬ |(quadraticSettlingStep 3 1 0)^[sweeps] 1 - 0| < 1 / 2
  exactRetentionExpansion : ∀ beta center parameter update : ℝ,
    quadraticRetention beta center (parameter + update) =
      quadraticRetention beta center parameter +
        quadraticRetentionGradient beta center parameter * update +
        beta / 2 * update ^ 2
  finiteRetentionSafety : ∀ beta center parameter update : ℝ,
    RetentionTrustRegionSafe
        (quadraticRetentionGradient beta center parameter) beta update →
      quadraticRetention beta center (parameter + update) ≤
        quadraticRetention beta center parameter
  retentionBacktracking :
    ∀ (beta center parameter direction initial shrink : ℝ),
      0 < beta →
      quadraticRetentionGradient beta center parameter * direction < 0 →
      0 < initial → 0 < shrink → shrink < 1 →
        ∃ sweeps : ℕ,
          quadraticRetention beta center
              (parameter + (initial * shrink ^ sweeps) * direction) ≤
            quadraticRetention beta center parameter
  firstOrderRetentionInsufficient :
    quadraticRetentionGradient 1 0 0 * (1 : ℝ) ≤ 0 ∧
      quadraticRetention 1 0 (0 + 1) > quadraticRetention 1 0 0
  scalarMinimumChange :
    ∀ metric retentionGradient proposed radius : ℝ,
      0 ≤ metric → 0 ≤ radius → |proposed| ≤ radius →
        ScalarMinimumChangeCertificate metric retentionGradient proposed radius
          (bpPlusScalarUpdate retentionGradient proposed)
  bpPlusGemIdentification : ∀ retentionGradient proposed : ℝ,
    bpPlusScalarUpdate retentionGradient proposed =
      gemSingleConstraintScalarUpdate retentionGradient proposed
  ogdNullspaceRecovery :
    ∀ {Index : Type*} [Fintype Index]
      (retentionGradient proposed : Index → ℝ),
      retentionGradient ⬝ᵥ retentionGradient ≠ 0 →
        retentionGradient ⬝ᵥ
          ogdSingleGradientUpdate retentionGradient proposed = 0
  fullRetentionKillsPlasticity :
    ∀ {Index : Type*} [Fintype Index] [DecidableEq Index]
      (currentGradient : Index → ℝ),
      ¬ ∃ update,
        PreservesAllLinearizedTasks
            (fun coordinate : Index => coordinateRetentionGradient coordinate)
            update ∧
          currentGradient ⬝ᵥ update < 0
  dynamicRegret :
    ∀ (initial : ℝ) (center error : ℕ → ℝ) (horizon : ℕ),
      onlineQuadraticRegret initial center error horizon ≤
        onlineQuadraticLoss (center 0) initial +
          optimumPathEnergy center horizon + approximationCost error horizon
  pathLengthDynamicRegret :
    ∀ (initial : ℝ) (center error : ℕ → ℝ) (horizon : ℕ),
      onlineQuadraticRegret initial center error horizon ≤
        onlineQuadraticLoss (center 0) initial +
          optimumPathLength center horizon ^ 2 + approximationCost error horizon
  certifiedApproximationRegret :
    ∀ (initial : ℝ) (center error epsilon : ℕ → ℝ) (horizon : ℕ),
      (∀ t < horizon, error t ^ 2 ≤ epsilon t) →
      onlineQuadraticRegret initial center error horizon ≤
        onlineQuadraticLoss (center 0) initial +
          optimumPathEnergy center horizon +
            ∑ t ∈ Finset.range horizon, epsilon t
  zeroErrorMatchesBP : ∀ (initial : ℝ) (center : ℕ → ℝ) (horizon : ℕ),
    onlineQuadraticRegret initial center (fun _ => 0) horizon =
      exactBPOnlineRegret initial center horizon
  zeroErrorExtraSettlingWasted :
    ∀ (initial : ℝ) (center : ℕ → ℝ) (horizon settlingSweeps : ℕ),
      0 < horizon → 0 < settlingSweeps →
        onlineQuadraticRegret initial center (fun _ => 0) horizon =
            exactBPOnlineRegret initial center horizon ∧
          onlineUpdateWork horizon 0 < onlineUpdateWork horizon settlingSweeps
  unitMetricOptimality :
    ∀ (preconditioner center parameter : ℝ),
      parameter ≠ center → preconditioner ≠ 1 →
        onlineQuadraticLoss center
            (preconditionedOnlineUpdate 1 center parameter) <
          onlineQuadraticLoss center
            (preconditionedOnlineUpdate preconditioner center parameter)
  jacobianKernelCriterion :
    ∀ {OldOutput Adapter : Type*} [Fintype Adapter]
      (model : FrozenAdapterJacobianModel OldOutput Adapter),
      (∃ update : Adapter → ℝ,
        PreservesOldOutputs model update ∧
          StrictlyImprovesCurrentLoss model update) ↔
        HasUsefulOldOutputKernelDirection model
  exhaustedJacobianBoundary : ∀ currentGradient : Fin 2 → ℝ,
    ¬ ∃ update : Fin 2 → ℝ,
      PreservesOldOutputs (identityOldOutputFixture currentGradient) update ∧
        StrictlyImprovesCurrentLoss
          (identityOldOutputFixture currentGradient) update
  adapterRankCriterion :
    ∀ {Row Column : Type*} [Fintype Row] [Fintype Column]
      [DecidableEq Column] (rankBudget : ℕ)
      (requiredEffect : Matrix Row Column ℝ),
      RankBudgetReachable rankBudget requiredEffect ↔
        requiredEffect.rank ≤ rankBudget
  bpSubsumptionPartition : BPSubsumptionPartitionLicense.{0, 0}

theorem certified_online_adaptation :
    CertifiedOnlineAdaptationLicense where
  hilbertContractionRate := hilbertSettlingContraction_lt_one
  hilbertFiniteSettlingGap := hilbertFiniteSettlingGradientGap_le
  hilbertZeroMismatch := hilbertFiniteSettlingGradientGap_zeroMismatch
  minimumHilbertDepth := minimumHilbertSettlingDepth_sufficient
  minimumHilbertDepthActualGap :=
    minimumHilbertSettlingDepth_zeroMismatch_gap_lt
  smoothRetentionDescent := smoothRetention_descentLemma
  smoothRetentionSafety := smoothRetention_nonincrease_of_trustRegion
  smoothRetentionBacktracking := smoothRetention_backtracking_terminates
  metricProjectionCharacterization := metricProjectionCertificate_iff_minimum
  metricProjectionMinimum := fun metric retentionGradients radius proposed chosen certificate =>
    certificate.minimumChange metric retentionGradients radius proposed chosen
  ogdMinimumChange := ogdSingleGradientUpdate_minimumChange
  spanningRetentionKillsPlasticity := retentionGradientSpan_no_strictPlasticity
  generalProjectedDynamicRegret :=
    projectedOnlineDynamicRegret_le_path_add_approximation
  exactDirectionMatchesBP := exactDirection_zeroApproximationCertificate
  gradientGapProjectedDynamicRegret :=
    projectedOnlineDynamicRegret_of_gradientGap
  finiteSettlingGap := finiteSettlingGradientGap_le
  finiteSettlingTolerance := finiteSettling_exists_tolerance
  minimumSettlingDepthSufficient := minimumSettlingDepth_sufficient
  unstableSettlingBoundary := unitQuadratic_rateThree_never_reaches_halfTolerance
  exactRetentionExpansion := quadraticRetention_update_exact
  finiteRetentionSafety := quadraticRetention_nonincrease_of_trustRegion
  retentionBacktracking := quadraticRetention_backtracking_terminates
  firstOrderRetentionInsufficient :=
    directionalSafe_finiteStepIncrease_negative_example
  scalarMinimumChange := bpPlus_onlineRetention_minimumChange
  bpPlusGemIdentification := bpPlus_eq_singleConstraintGEM
  ogdNullspaceRecovery := ogdSingleGradientUpdate_exactRetention
  fullRetentionKillsPlasticity :=
    fullCoordinateRetention_no_strictPlasticity_negative_example
  dynamicRegret :=
    onlineQuadraticRegret_le_pathEnergy_add_approximationCost
  pathLengthDynamicRegret :=
    onlineQuadraticRegret_le_pathLength_sq_add_approximationCost
  certifiedApproximationRegret :=
    onlineQuadraticRegret_le_pathEnergy_add_errorCertificates
  zeroErrorMatchesBP := zeroApproximation_matches_exactBP
  zeroErrorExtraSettlingWasted := zeroError_extraSettling_is_wasted
  unitMetricOptimality := unitPreconditioner_strictlyImproves_over_wrongMetric
  jacobianKernelCriterion :=
    exists_preserving_strictImprovement_iff_usefulKernelDirection
  exhaustedJacobianBoundary :=
    identityOldOutputFixture_no_strictPlasticity_negative_example
  adapterRankCriterion := frozenAdapterEffect_reachable_iff_rank_le
  bpSubsumptionPartition := bp_subsumption_partition

#print axioms certified_online_adaptation

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
