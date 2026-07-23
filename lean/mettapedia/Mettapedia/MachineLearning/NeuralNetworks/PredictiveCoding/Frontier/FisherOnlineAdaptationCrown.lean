import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.NaturalGradientErrorBudget
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FrozenAdapterFisher
import Mettapedia.MachineLearning.ContinualLearning.FisherRetentionBridge

/-!
# Certified Fisher geometry for online neural adaptation

This crown packages the exact Gaussian identity, approximation bound, explicit
PC-to-natural error budget, Fisher diagnostic, local continual-learning bridge,
and frozen-adapter pullback.  The negative fixtures remain part of the license:
scalar precision is not a general Fisher inverse, nonlinear KL is not its local
quadratic, projection order can matter, and a noninjective frozen parent gives
a degenerate pullback.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped InnerProductSpace
open Mettapedia.MachineLearning.ContinualLearning

structure FisherOnlineAdaptationLicense : Prop where
  gaussianFactorization :
    ∀ {Sample Input Output : Type*} [Fintype Sample]
      (weight : Sample → ℝ) (activation : Sample → Input → ℝ)
      (precision : Matrix Output Output ℝ),
      gaussianWeightFisher weight activation precision =
        precision.kronecker (activationSecondMoment weight activation)
  scalarPrecisionBoundary :
    ∀ scale : ℝ, scalarPrecisionOnlyStep scale ≠ correlatedNaturalStep
  approximationLadder :
    FisherApproximationLevel.full.StrictlyRefines .layerBlock ∧
      FisherApproximationLevel.layerBlock.StrictlyRefines .kronecker ∧
      FisherApproximationLevel.kronecker.StrictlyRefines .activationOnly ∧
      FisherApproximationLevel.activationOnly.StrictlyRefines .diagonal ∧
      FisherApproximationLevel.diagonal.StrictlyRefines .scalarPrecision
  relativeMetricBound :
    ∀ {Parameter : Type*} [NormedAddCommGroup Parameter]
      [InnerProductSpace ℝ Parameter]
      (exact : InvertibleSPDMetric Parameter)
      (approximate : Parameter →L[ℝ] Parameter)
      (epsilon : ℝ) (exactDirection approximateDirection gradient : Parameter),
      0 ≤ epsilon → epsilon < 1 →
      exact.RelativeError approximate epsilon →
      exact.operator exactDirection = gradient →
      approximate approximateDirection = gradient →
      ‖approximateDirection - exactDirection‖ ≤
        epsilon / (1 - epsilon) * ‖exactDirection‖
  pcNaturalErrorBudget :
    ∀ {Parameter : Type*} [NormedAddCommGroup Parameter]
      (observed settled equilibrium approximate natural : Parameter)
      (optimizerError settlingError covarianceError dampingError : ℝ),
      PCNaturalErrorCertificate observed settled equilibrium approximate natural
          optimizerError settlingError covarianceError dampingError →
        ‖observed - natural‖ ≤
          optimizerError + settlingError + covarianceError + dampingError
  fisherDiagnostic :
    ∀ {Parameter : Type*} [NormedAddCommGroup Parameter]
      [InnerProductSpace ℝ Parameter]
      (metric : AdapterMetric Parameter) (update natural : Parameter),
      metric.PositiveDefinite → natural ≠ 0 →
      metric.pair update update =
        fisherProjectionCoefficient metric update natural ^ 2 *
            metric.pair natural natural +
          metric.pair (fisherOrthogonalResidual metric update natural)
            (fisherOrthogonalResidual metric update natural)
  localRetentionBridge :
    ∀ {Parameter : Type*} [NormedAddCommGroup Parameter]
      [InnerProductSpace ℝ Parameter]
      (metric : AdapterMetric Parameter) (oldParameter : Parameter)
      (feasible : Parameter → Prop) (chosen : Parameter),
      IsLocalPenaltyMinimum
          (fun update => vclLaplaceMeanShiftLocal metric oldParameter
            (oldParameter + update)) feasible chosen ↔
        IsLocalPenaltyMinimum
            (fun update => ewcFisherPenaltyLocal metric update) feasible chosen ∧
        IsLocalPenaltyMinimum
            (fun update => curvatureReplayKLLocal metric update) feasible chosen
  frozenAdapterPullback :
    ∀ {Parameter Output : Type*}
      [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
      [CompleteSpace Parameter]
      [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
      [CompleteSpace Output]
      (outputMetric : AdapterMetric Output)
      (parentJacobian : Parameter →L[ℝ] Output) (x y : Parameter),
      (frozenAdapterPullbackMetric outputMetric parentJacobian).pair x y =
        outputMetric.pair (parentJacobian x) (parentJacobian y)
  nonlinearScopeBoundary :
    nonlinearPredictiveKLFixture 1 ≠ scalarFisherQuadraticFixture 1
  projectionOrderBoundary :
    diagonalRetentionProjection
        (curvaturePreconditioner2D retentionAxis0) ≠
      curvaturePreconditioner2D
        (diagonalRetentionProjection retentionAxis0)
  pullbackInjectivityBoundary :
    fisherDiagnosticAxis1 ≠ 0 ∧
      (frozenAdapterPullbackMetric
        (identityAdapterMetric : AdapterMetric ℝ) frozenCoordinateReadout).pair
          fisherDiagnosticAxis1 fisherDiagnosticAxis1 = 0

theorem fisher_online_adaptation_crown : FisherOnlineAdaptationLicense where
  gaussianFactorization := by
    intro Sample Input Output _ weight activation precision
    exact gaussianWeightFisher_eq_kronecker weight activation precision
  scalarPrecisionBoundary :=
    scalarPrecision_cannot_recover_correlatedNaturalStep
  approximationLadder := fisherApproximation_strict_ladder
  relativeMetricBound := by
    intro Parameter _ _ exact approximate epsilon exactDirection
      approximateDirection gradient hepsilon0 hepsilon1 hrelative hexact
      happroximate
    exact exact.direction_error_le_ratio approximate epsilon exactDirection
      approximateDirection gradient hepsilon0 hepsilon1 hrelative hexact
      happroximate
  pcNaturalErrorBudget := by
    intro Parameter _ observed settled equilibrium approximate natural
      optimizerError settlingError covarianceError dampingError certificate
    exact certificate.total observed settled equilibrium approximate natural
      optimizerError settlingError covarianceError dampingError
  fisherDiagnostic := by
    intro Parameter _ _ metric update natural hpositive hnatural
    exact fisherOrthogonalResidual_pythagoras metric update natural
      hpositive hnatural
  localRetentionBridge := by
    intro Parameter _ _ metric oldParameter feasible chosen
    exact vcl_ewc_curvatureReplay_same_local_minimum metric oldParameter
      feasible chosen
  frozenAdapterPullback := by
    intro Parameter Output _ _ _ _ _ _ outputMetric parentJacobian x y
    exact frozenAdapterPullbackMetric_pair outputMetric parentJacobian x y
  nonlinearScopeBoundary := nonlinearKL_not_equal_localQuadratic_fixture
  projectionOrderBoundary :=
    curvature_then_projection_ne_projection_then_curvature
  pullbackInjectivityBoundary :=
    noninjectiveFrozenParent_pullback_degenerate

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
