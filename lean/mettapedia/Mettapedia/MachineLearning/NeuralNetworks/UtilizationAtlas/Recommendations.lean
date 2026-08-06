import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.WorkspaceFrontier

/-!
# Proof-bearing utilization recommendations

Recommendations are selected from a finite modeled regime family before their
guarantees are defined.  The guarantees then refer to actual risk, convergence,
interference, Hessian, routing, and safety-boundary theorems from the preceding
frontiers.  Thus the recommender is not defined by asking whether its own
output is best.

The finite family is complete in the precise sense that every declared regime
receives a licensed recommendation.  It does not assert completeness for all
possible neural systems.  No single recommendation covers the modeled family,
while list-valued hybrids are closed under union of their licensed regimes.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Requested recommendation vocabulary -/

/-- Architecture/policy recommendations returned by the utilization atlas. -/
inductive Recommendation where
  | useBackprop
  | usePCInference
  | usePCPlasticity
  | useAdditiveBelief
  | useFadingBelief
  | useCalibratedBelief
  | useMixtureBelief (width : ℕ)
  | useTypedWorkspace
  | useSelectiveWorkspace
  | useRoutedWorkspace
  deriving DecidableEq, Repr

/-- Finite family for which completeness is proved. -/
inductive ModeledUtilizationRegime where
  | wellSpecifiedScalarQuadratic
  | contractivePCInference
  | prospectivePCPlasticity
  | stationaryIndependentGaussian
  | positiveProcessDrift
  | knownObservationOverlap
  | fixedLinearDistortion
  | finiteBimodalDecision
  | separableTypedHoles
  | varyingObservationNoise
  | contextDependentRouting
  deriving DecidableEq, Fintype, Repr

/-- The recommender is a direct regime decision table. -/
def recommendationFor : ModeledUtilizationRegime → Recommendation
  | .wellSpecifiedScalarQuadratic => .useBackprop
  | .contractivePCInference => .usePCInference
  | .prospectivePCPlasticity => .usePCPlasticity
  | .stationaryIndependentGaussian => .useAdditiveBelief
  | .positiveProcessDrift => .useFadingBelief
  | .knownObservationOverlap => .useCalibratedBelief
  | .fixedLinearDistortion => .useCalibratedBelief
  | .finiteBimodalDecision => .useMixtureBelief 2
  | .separableTypedHoles => .useTypedWorkspace
  | .varyingObservationNoise => .useSelectiveWorkspace
  | .contextDependentRouting => .useRoutedWorkspace

/-! ## Substantive guarantees -/

/-- In the nondegenerate scalar quadratic, the curvature-normalized BP step
reaches zero loss and identity is the unique scalar preconditioner that does. -/
def BackpropRecommendationGuarantee : Prop :=
  ∀ sourceActivation downstreamGain target weight : ℝ,
    downstreamGain * sourceActivation ≠ 0 →
    chainLinkResidual sourceActivation downstreamGain target weight ≠ 0 →
      chainLinkHalfSquaredLoss sourceActivation downstreamGain target
          (chainLinkPreconditionedPCUpdate 1 sourceActivation downstreamGain
            target weight) = 0 ∧
        ∀ preconditioner,
          (chainLinkHalfSquaredLoss sourceActivation downstreamGain target
              (chainLinkPreconditionedPCUpdate preconditioner sourceActivation
                downstreamGain target weight) = 0 ↔
            preconditioner = 1)

/-- Contractive-PC guarantee used by the inference recommendation. -/
def PCInferenceRecommendationGuarantee : Prop :=
  (∀ target initial tolerance : ℝ, 0 < tolerance →
    ∃ sweeps : ℕ,
      halfRelaxationResidual target initial sweeps < tolerance ∧
        halfRelaxationRisk target initial sweeps < tolerance ^ 2) ∧
  (∀ target initial tolerance : ℝ, ∀ htolerance : 0 < tolerance,
    halfRelaxationResidual target initial
        (minimalHalfRelaxationSweeps target initial tolerance htolerance) <
      tolerance)

/-- Exact typed-hole separation guarantee. -/
def TypedWorkspaceRecommendationGuarantee : Prop :=
  ∀ firstCurvature secondCurvature coupling firstForce secondForce : ℝ,
    SlotwiseIndependentSettling firstCurvature secondCurvature coupling
        firstForce secondForce ↔
      crossSlotHessianBlock firstCurvature secondCurvature coupling = 0

/-- Exact selective-gain separation guarantee. -/
def SelectiveWorkspaceRecommendationGuarantee : Prop :=
  ∀ priorVariance firstNoise secondNoise gate : ℝ,
    0 < priorVariance → 0 < firstNoise → 0 < secondNoise →
      firstNoise ≠ secondNoise →
        twoRegimeSelectiveRisk priorVariance firstNoise secondNoise <
          twoRegimeConstantGateRisk priorVariance firstNoise secondNoise gate

/-- A recommendation is licensed only by the actual theorem appropriate to
its regime.  Every nonmatching pair is unlicensed. -/
def RecommendationGuarantee :
    ModeledUtilizationRegime → Recommendation → Prop
  | .wellSpecifiedScalarQuadratic, .useBackprop =>
      BackpropRecommendationGuarantee
  | .contractivePCInference, .usePCInference =>
      PCInferenceRecommendationGuarantee
  | .prospectivePCPlasticity, .usePCPlasticity =>
      PCPlasticityLicense
  | .stationaryIndependentGaussian, .useAdditiveBelief =>
      BeliefPolicyGuarantee .stationaryIndependentGaussian .additiveNatural
  | .positiveProcessDrift, .useFadingBelief =>
      BeliefPolicyGuarantee .positiveProcessDrift .fadingNatural
  | .knownObservationOverlap, .useCalibratedBelief =>
      BeliefPolicyGuarantee .knownObservationOverlap .discountedNatural
  | .fixedLinearDistortion, .useCalibratedBelief =>
      BeliefPolicyGuarantee .fixedLinearDistortion .calibratedMeasurement
  | .finiteBimodalDecision, .useMixtureBelief 2 =>
      BeliefPolicyGuarantee .finiteBimodalDecision (.finiteMixture 2)
  | .separableTypedHoles, .useTypedWorkspace =>
      TypedWorkspaceRecommendationGuarantee
  | .varyingObservationNoise, .useSelectiveWorkspace =>
      SelectiveWorkspaceRecommendationGuarantee
  | .contextDependentRouting, .useRoutedWorkspace =>
      WorkspaceFrontierLicense
  | _, _ => False

/-- A recommendation paired with its substantive regime theorem. -/
structure LicensedRecommendation
    (regime : ModeledUtilizationRegime) where
  recommendation : Recommendation
  guarantee : RecommendationGuarantee regime recommendation

/-! ## Soundness and finite-family completeness -/

/-- Every table entry has its declared theorem. -/
theorem recommendationFor_guaranteed
    (regime : ModeledUtilizationRegime) :
    RecommendationGuarantee regime (recommendationFor regime) := by
  cases regime with
  | wellSpecifiedScalarQuadratic =>
      intro sourceActivation downstreamGain target weight
        heffective hresidual
      exact ⟨chainLink_identityPreconditioner_reaches_zeroLoss
          sourceActivation downstreamGain target weight heffective,
        fun preconditioner =>
          chainLink_zeroLoss_afterUpdate_iff_identity
            preconditioner sourceActivation downstreamGain target weight
            heffective hresidual⟩
  | contractivePCInference =>
      exact ⟨halfRelaxation_exists_finite_residual_and_risk,
        minimalHalfRelaxationSweeps_sufficient⟩
  | prospectivePCPlasticity =>
      exact pcPlasticity_frontier
  | stationaryIndependentGaussian =>
      exact beliefPolicy_frontier .stationaryIndependentGaussian
  | positiveProcessDrift =>
      exact beliefPolicy_frontier .positiveProcessDrift
  | knownObservationOverlap =>
      exact beliefPolicy_frontier .knownObservationOverlap
  | fixedLinearDistortion =>
      exact beliefPolicy_frontier .fixedLinearDistortion
  | finiteBimodalDecision =>
      exact beliefPolicy_frontier .finiteBimodalDecision
  | separableTypedHoles =>
      exact slotwiseIndependentSettling_iff_crossSlotHessianBlock_zero
  | varyingObservationNoise =>
      exact fun priorVariance firstNoise secondNoise gate hprior hfirst
        hsecond hnoise =>
          everyConstantGate_strictlySuboptimal priorVariance firstNoise
            secondNoise gate hprior hfirst hsecond hnoise
  | contextDependentRouting =>
      exact workspace_frontier

/-- Total licensed recommender for the finite modeled family. -/
def licensedRecommendationFor
    (regime : ModeledUtilizationRegime) : LicensedRecommendation regime where
  recommendation := recommendationFor regime
  guarantee := recommendationFor_guaranteed regime

/-- Soundness is projection of the substantive theorem, not equality to a
policy label. -/
theorem recommendation_sound
    {regime : ModeledUtilizationRegime}
    (licensed : LicensedRecommendation regime) :
    RecommendationGuarantee regime licensed.recommendation :=
  licensed.guarantee

/-- Completeness for exactly the declared finite regime family. -/
theorem recommendation_complete_for_modeledFamily
    (regime : ModeledUtilizationRegime) :
    ∃ recommendation,
      RecommendationGuarantee regime recommendation :=
  ⟨recommendationFor regime, recommendationFor_guaranteed regime⟩

/-! ## No universal single winner -/

/-- No one policy constructor is licensed across every modeled regime. -/
theorem no_singleRecommendation_covers_modeledFamily :
    ¬ ∃ recommendation,
      ∀ regime, RecommendationGuarantee regime recommendation := by
  rintro ⟨recommendation, hall⟩
  cases recommendation with
  | useBackprop =>
      simpa [RecommendationGuarantee] using
        hall .contractivePCInference
  | usePCInference =>
      simpa [RecommendationGuarantee] using
        hall .wellSpecifiedScalarQuadratic
  | usePCPlasticity =>
      simpa [RecommendationGuarantee] using
        hall .wellSpecifiedScalarQuadratic
  | useAdditiveBelief =>
      simpa [RecommendationGuarantee] using
        hall .positiveProcessDrift
  | useFadingBelief =>
      simpa [RecommendationGuarantee] using
        hall .stationaryIndependentGaussian
  | useCalibratedBelief =>
      simpa [RecommendationGuarantee] using
        hall .stationaryIndependentGaussian
  | useMixtureBelief width =>
      simpa [RecommendationGuarantee] using
        hall .stationaryIndependentGaussian
  | useTypedWorkspace =>
      simpa [RecommendationGuarantee] using
        hall .stationaryIndependentGaussian
  | useSelectiveWorkspace =>
      simpa [RecommendationGuarantee] using
        hall .stationaryIndependentGaussian
  | useRoutedWorkspace =>
      simpa [RecommendationGuarantee] using
        hall .stationaryIndependentGaussian

/-! ## Hybrid closure -/

/-- A hybrid architecture is a finite list of licensed policy components. -/
structure HybridRecommendation where
  components : List Recommendation
  deriving Repr

/-- A hybrid licenses a regime when at least one of its components carries the
regime theorem. -/
def HybridRecommendation.Licenses
    (hybrid : HybridRecommendation)
    (regime : ModeledUtilizationRegime) : Prop :=
  ∃ recommendation ∈ hybrid.components,
    RecommendationGuarantee regime recommendation

/-- Combine two hybrids without erasing either component list. -/
def HybridRecommendation.combine
    (first second : HybridRecommendation) : HybridRecommendation where
  components := first.components ++ second.components

theorem HybridRecommendation.combine_licenses_left
    {first second : HybridRecommendation}
    {regime : ModeledUtilizationRegime}
    (hlicensed : first.Licenses regime) :
    (first.combine second).Licenses regime := by
  rcases hlicensed with ⟨recommendation, hmem, hguarantee⟩
  exact ⟨recommendation, List.mem_append_left _ hmem, hguarantee⟩

theorem HybridRecommendation.combine_licenses_right
    {first second : HybridRecommendation}
    {regime : ModeledUtilizationRegime}
    (hlicensed : second.Licenses regime) :
    (first.combine second).Licenses regime := by
  rcases hlicensed with ⟨recommendation, hmem, hguarantee⟩
  exact ⟨recommendation, List.mem_append_right _ hmem, hguarantee⟩

/-- Hybrid closure: combining two licensed architectures preserves the union
of the regimes they license. -/
theorem hybridRecommendation_closure
    (first second : HybridRecommendation)
    (regime : ModeledUtilizationRegime) :
    first.Licenses regime ∨ second.Licenses regime →
      (first.combine second).Licenses regime := by
  rintro (hfirst | hsecond)
  · exact HybridRecommendation.combine_licenses_left hfirst
  · exact HybridRecommendation.combine_licenses_right hsecond

/-- Singleton hybrid produced by the total licensed recommender. -/
def licensedSingletonHybrid
    (regime : ModeledUtilizationRegime) : HybridRecommendation where
  components := [recommendationFor regime]

theorem licensedSingletonHybrid_licenses
    (regime : ModeledUtilizationRegime) :
    (licensedSingletonHybrid regime).Licenses regime := by
  exact ⟨recommendationFor regime, by simp [licensedSingletonHybrid],
    recommendationFor_guaranteed regime⟩

/-! ## T6 crown -/

/-- Soundness, finite-family completeness, absence of a universal single
winner, and hybrid closure. -/
theorem recommendations_frontier :
    (∀ regime, RecommendationGuarantee regime (recommendationFor regime)) ∧
    (¬ ∃ recommendation,
      ∀ regime, RecommendationGuarantee regime recommendation) ∧
    (∀ first second : HybridRecommendation, ∀ regime,
      first.Licenses regime ∨ second.Licenses regime →
        (first.combine second).Licenses regime) := by
  exact ⟨recommendationFor_guaranteed,
    no_singleRecommendation_covers_modeledFamily,
    hybridRecommendation_closure⟩

#print axioms recommendationFor_guaranteed
#print axioms recommendation_sound
#print axioms recommendation_complete_for_modeledFamily
#print axioms no_singleRecommendation_covers_modeledFamily
#print axioms hybridRecommendation_closure
#print axioms recommendations_frontier

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
