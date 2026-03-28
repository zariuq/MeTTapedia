import Mettapedia.Logic.MarkovLogicSyntheticCognitiveDevelopment
import Mettapedia.Logic.MarkovLogicCoupledCommunitiesExample

/-!
# Synthetic Cognitive Development Example

This example instantiates `MarkovLogicSyntheticCognitiveDevelopment` on the
coupled-communities topology.

- The original identity query is the protected joint community query on
  agents `{0,3}`.
- The developmental coordination query is broader: it couples agent `0` in the
  protected community with tail agent `5`, which lies outside the original
  protected cores.

The theorem says: if that broader coordination score increases stepwise along a
two-step rewrite path, then end-to-end coordination improves while the
original joint community identity still drifts by at most the cumulative shell
budget.
-/

namespace Mettapedia.Logic.MarkovLogicSyntheticCognitiveDevelopmentExample

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicCoupledCommunitiesExample
open Mettapedia.Logic.MarkovLogicDynamicCoupledSubsystems
open Mettapedia.Logic.MarkovLogicSyntheticCognitiveDevelopment
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

/-- Boundary condition used for DLR existence witnesses. -/
def falseBoundary : BoundaryCondition Nat := fun _ => false

/-- Fixed protected-community weight. -/
noncomputable def communityCoreWt : ℝ := 1 / 8

/-- Three tail weights along the development path. -/
noncomputable def communityTailWt₀ : ℝ := 1 / 10
noncomputable def communityTailWt₁ : ℝ := 1 / 5
noncomputable def communityTailWt₂ : ℝ := 3 / 10

theorem communityCoreWt_small : |communityCoreWt| < 1 / 4 := by
  norm_num [communityCoreWt]

theorem communityTailWt₀_small : |communityTailWt₀| < 1 / 2 := by
  norm_num [communityTailWt₀]

theorem communityTailWt₁_small : |communityTailWt₁| < 1 / 2 := by
  norm_num [communityTailWt₁]

theorem communityTailWt₂_small : |communityTailWt₂| < 1 / 2 := by
  norm_num [communityTailWt₂]

/-- A broader developmental coordination query reaching from the protected left
community into the tail. -/
def communityCoordinationQuery : ConstraintQuery Nat :=
  [⟨0, true⟩, ⟨5, true⟩]

/-- First dynamic coupled rewrite step. -/
noncomputable def coupledCommunitiesDevelopmentStep₀₁ :
    DynamicCoupledSubsystemStep
      (coupledCommunitiesSpec communityCoreWt communityTailWt₀)
      (coupledCommunitiesSpec communityCoreWt communityTailWt₁) where
  coupled := coupledCommunitiesSubsystem communityCoreWt communityTailWt₀
  shellDepth := 0
  shell_agreement := by
    simpa [ClassicalInfiniteGroundMLNSpec.iterExpandRegion]
      using specs_agree_on_carrier communityCoreWt communityTailWt₀ communityTailWt₁
  budget₁ :=
    coupledCommunitiesSpec_budget
      communityCoreWt communityTailWt₀ communityCoreWt_small communityTailWt₀_small
  budget₂ :=
    coupledCommunitiesSpec_budget
      communityCoreWt communityTailWt₁ communityCoreWt_small communityTailWt₁_small

/-- Second dynamic coupled rewrite step. -/
noncomputable def coupledCommunitiesDevelopmentStep₁₂ :
    DynamicCoupledSubsystemStep
      (coupledCommunitiesSpec communityCoreWt communityTailWt₁)
      (coupledCommunitiesSpec communityCoreWt communityTailWt₂) where
  coupled := coupledCommunitiesSubsystem communityCoreWt communityTailWt₁
  shellDepth := 0
  shell_agreement := by
    simpa [ClassicalInfiniteGroundMLNSpec.iterExpandRegion]
      using specs_agree_on_carrier communityCoreWt communityTailWt₁ communityTailWt₂
  budget₁ :=
    coupledCommunitiesSpec_budget
      communityCoreWt communityTailWt₁ communityCoreWt_small communityTailWt₁_small
  budget₂ :=
    coupledCommunitiesSpec_budget
      communityCoreWt communityTailWt₂ communityCoreWt_small communityTailWt₂_small

/-- Two-step development path on the coupled-communities topology. -/
noncomputable def coupledCommunitiesDevelopmentPath :
    DynamicCoupledSubsystemPath
      (coupledCommunitiesSpec communityCoreWt communityTailWt₀)
      (coupledCommunitiesSpec communityCoreWt communityTailWt₂) :=
  .step (.single coupledCommunitiesDevelopmentStep₀₁)
    coupledCommunitiesDevelopmentStep₁₂

theorem coupledCommunitiesDevelopmentPath_coherent :
    coupledCommunitiesDevelopmentPath.Coherent := by
  simp [coupledCommunitiesDevelopmentPath, DynamicCoupledSubsystemPath.Coherent,
    DynamicCoupledSubsystemPath.originalCarrier,
    DynamicCoupledSubsystemPath.originalLeftCore,
    DynamicCoupledSubsystemPath.originalRightCore,
    coupledCommunitiesDevelopmentStep₀₁, coupledCommunitiesDevelopmentStep₁₂,
    coupledCommunitiesSubsystem]

private theorem carrierRegion_card : carrierRegion.card = 5 := by
  simp [carrierRegion]

private theorem coupledCommunitiesSubsystem_carrier_card (wt : ℝ) :
    (coupledCommunitiesSubsystem communityCoreWt wt).carrier.core.card = 5 := by
  simp [coupledCommunitiesSubsystem, carrierRegion]

theorem coupledCommunitiesDevelopmentStep₀₁_errorBound :
    coupledCommunitiesDevelopmentStep₀₁.errorBound = 10 := by
  have hcard : coupledCommunitiesDevelopmentStep₀₁.coupled.carrier.core.card = 5 := by
    simpa [coupledCommunitiesDevelopmentStep₀₁, coupledCommunitiesSubsystem] using
      coupledCommunitiesSubsystem_carrier_card communityTailWt₀
  rw [DynamicCoupledSubsystemStep.errorBound, hcard]
  simp [coupledCommunitiesDevelopmentStep₀₁]
  norm_num

theorem coupledCommunitiesDevelopmentStep₁₂_errorBound :
    coupledCommunitiesDevelopmentStep₁₂.errorBound = 10 := by
  have hcard : coupledCommunitiesDevelopmentStep₁₂.coupled.carrier.core.card = 5 := by
    simpa [coupledCommunitiesDevelopmentStep₁₂, coupledCommunitiesSubsystem] using
      coupledCommunitiesSubsystem_carrier_card communityTailWt₁
  rw [DynamicCoupledSubsystemStep.errorBound, hcard]
  simp [coupledCommunitiesDevelopmentStep₁₂]
  norm_num

theorem coupledCommunitiesDevelopmentPath_totalErrorBound :
    coupledCommunitiesDevelopmentPath.totalErrorBound = 20 := by
  simp [coupledCommunitiesDevelopmentPath, DynamicCoupledSubsystemPath.totalErrorBound,
    coupledCommunitiesDevelopmentStep₀₁_errorBound,
    coupledCommunitiesDevelopmentStep₁₂_errorBound]
  norm_num

private theorem exists_coupledCommunities_dlr (wt : ℝ) :
    ∃ μ : Measure (InfiniteWorld Nat),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (coupledCommunitiesSpec communityCoreWt wt).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa [coupledCommunitiesSpec] using
    exists_varNeighborhood_fixedRegionCylinderDLR
      coupledCommunitiesNbrs coupledCommunitiesNbrs coupledCommunitiesNbrs_symm
      (coupledCommunitiesTrust communityCoreWt wt) coupledCommunitiesPrior falseBoundary

/-- Concrete development example:

- broader coordination on `[0,5]` improves stepwise,
- the original joint identity query on `[0,3]` stays within the cumulative
  shell budget `20`. -/
theorem coupledCommunities_syntheticDevelopment_example
    (μ₀ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₁ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ₀ : FixedRegionCylinderDLR
      (coupledCommunitiesSpec communityCoreWt communityTailWt₀).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₀ : Measure (InfiniteWorld Nat)))
    (hμ₁ : FixedRegionCylinderDLR
      (coupledCommunitiesSpec communityCoreWt communityTailWt₁).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Nat)))
    (hμ₂ : FixedRegionCylinderDLR
      (coupledCommunitiesSpec communityCoreWt communityTailWt₂).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Nat)))
    (hgrow₀₁ :
      coordinationScore μ₀ hμ₀ communityCoordinationQuery <
        coordinationScore μ₁ hμ₁ communityCoordinationQuery)
    (hgrow₁₂ :
      coordinationScore μ₁ hμ₁ communityCoordinationQuery <
        coordinationScore μ₂ hμ₂ communityCoordinationQuery) :
    ∃ _dev :
        SyntheticCognitiveDevelopmentPath
          (M₀ := coupledCommunitiesSpec communityCoreWt communityTailWt₀)
          (M_final := coupledCommunitiesSpec communityCoreWt communityTailWt₂),
      coordinationScore μ₀ hμ₀ communityCoordinationQuery <
          coordinationScore μ₂ hμ₂ communityCoordinationQuery ∧
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics
                (coupledCommunitiesSpec communityCoreWt communityTailWt₀) μ₀ hμ₀} :
              MassState (ConstraintQuery Nat)) jointQuery).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics
                (coupledCommunitiesSpec communityCoreWt communityTailWt₂) μ₂ hμ₂} :
              MassState (ConstraintQuery Nat)) jointQuery).toReal| ≤
            20 := by
  let measures :
      DynamicCoupledSubsystemPathDLR coupledCommunitiesDevelopmentPath :=
    .step (.single coupledCommunitiesDevelopmentStep₀₁ μ₀ μ₁ hμ₀ hμ₁) μ₂ hμ₂
  let dev :
      SyntheticCognitiveDevelopmentPath
        (M₀ := coupledCommunitiesSpec communityCoreWt communityTailWt₀)
        (M_final := coupledCommunitiesSpec communityCoreWt communityTailWt₂) :=
    { path := coupledCommunitiesDevelopmentPath
      measures := measures
      coherent := coupledCommunitiesDevelopmentPath_coherent
      coordination := { query := communityCoordinationQuery }
      stepwise_gain := by
        exact ⟨hgrow₀₁, hgrow₁₂⟩ }
  have hjoint :
      ∀ p ∈ jointQuery,
        (p : Sigma fun _ : Nat => Bool).1 ∈
          dev.path.originalLeftCore ∪ dev.path.originalRightCore := by
    simpa [dev, coupledCommunitiesDevelopmentPath,
      DynamicCoupledSubsystemPath.originalLeftCore,
      DynamicCoupledSubsystemPath.originalRightCore] using jointQuery_supported
  refine ⟨dev, ?_⟩
  have hmain :=
    dev.coordination_improves_while_joint_identity_drift_bounded
      jointQuery hjoint
  refine ⟨?_, ?_⟩
  · simpa [dev, measures, coordinationScore] using hmain.1
  · have hbound :
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics
                (coupledCommunitiesSpec communityCoreWt communityTailWt₀) μ₀ hμ₀} :
              MassState (ConstraintQuery Nat)) jointQuery).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics
                (coupledCommunitiesSpec communityCoreWt communityTailWt₂) μ₂ hμ₂} :
              MassState (ConstraintQuery Nat)) jointQuery).toReal| ≤
            dev.path.totalErrorBound := by
      simpa [dev, measures] using hmain.2
    simpa [dev, coupledCommunitiesDevelopmentPath_totalErrorBound] using hbound

/-- Existential DLR witness package for the concrete development example. -/
theorem exists_coupledCommunities_development_dlr :
    ∃ μ₀ μ₁ μ₂ : ProbabilityMeasure (InfiniteWorld Nat),
      FixedRegionCylinderDLR
        (coupledCommunitiesSpec communityCoreWt communityTailWt₀).toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₀ : Measure (InfiniteWorld Nat)) ∧
      FixedRegionCylinderDLR
        (coupledCommunitiesSpec communityCoreWt communityTailWt₁).toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₁ : Measure (InfiniteWorld Nat)) ∧
      FixedRegionCylinderDLR
        (coupledCommunitiesSpec communityCoreWt communityTailWt₂).toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₂ : Measure (InfiniteWorld Nat)) := by
  rcases exists_coupledCommunities_dlr communityTailWt₀ with ⟨μ₀m, hμ₀prob, hμ₀⟩
  rcases exists_coupledCommunities_dlr communityTailWt₁ with ⟨μ₁m, hμ₁prob, hμ₁⟩
  rcases exists_coupledCommunities_dlr communityTailWt₂ with ⟨μ₂m, hμ₂prob, hμ₂⟩
  refine ⟨⟨μ₀m, hμ₀prob⟩, ⟨μ₁m, hμ₁prob⟩, ⟨μ₂m, hμ₂prob⟩, hμ₀, hμ₁, hμ₂⟩

end Mettapedia.Logic.MarkovLogicSyntheticCognitiveDevelopmentExample
