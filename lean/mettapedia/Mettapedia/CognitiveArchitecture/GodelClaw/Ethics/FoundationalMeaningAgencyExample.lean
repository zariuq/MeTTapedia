import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.FoundationalMeaningAgencyWMBridge
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.BodhisattvaExample

/-!
# Foundational Meaning / Agency Example on the Trust Triangle

This file turns the trust-triangle ethics example into a concrete
foundational-meaning / agency example on WM ground.

The intended toy reading is:

- `situation` = current local harm-relevant situation,
- `prediction` = current operator-facing expectation,
- `activeGoal` = reciprocity / relational health,
- `plan` = a consent-respecting act pattern.

This is deliberately small and explicit.  The point is to show that we can
state a meaning/agency profile directly in WM queries, seed it from a tiny
Hyperseed frontier, and then inherit the proved protected-goal stability
results without going through a SUMO-level semantics.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Hyperseed
open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
open Mettapedia.Logic.MarkovLogicTrustTriangleExample
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample
open MeasureTheory

local instance : DecidableEq VarNClauseId := inferInstance

/-- Minimal observation alphabet for the trust-triangle meaning example. -/
inductive TrustTriangleMeaningObservation where
  | situationCue
  | predictionCue
  | reciprocityCue
  | consentPlanCue
  | operatorCue
  deriving DecidableEq, Repr

/-- Concrete WM-grounded meaning profile on the trust triangle. -/
def trustTriangleMeaningProfile : FoundationalMeaningProfile (ConstraintQuery Nat) where
  situation := bodhisattvaNonMaleficenceQuery
  prediction := bodhisattvaEpistemicUniversalLoveQuery
  activeGoal := bodhisattvaReciprocityQuery
  plan := bodhisattvaConsentQuery

/-- In this toy reading, operator deference shares the same WM proxy as the
operator-facing epistemic-universal-love slot on agent `1`. -/
abbrev trustTriangleOperatorDeferenceQuery : ConstraintQuery Nat :=
  bodhisattvaEpistemicUniversalLoveQuery

/-- Tiny Hyperseed frontier for the trust-triangle meaning profile. -/
def trustTriangleMeaningFrontier : TrustTriangleMeaningObservation → Set (ConstraintQuery Nat)
  | .situationCue => {trustTriangleMeaningProfile.situation}
  | .predictionCue => {trustTriangleMeaningProfile.prediction}
  | .reciprocityCue => {trustTriangleMeaningProfile.activeGoal}
  | .consentPlanCue => {trustTriangleMeaningProfile.plan}
  | .operatorCue => {trustTriangleOperatorDeferenceQuery}

@[simp] theorem trustTriangleMeaning_activeGoal_mem_frontier :
    trustTriangleMeaningProfile.activeGoal ∈
      trustTriangleMeaningFrontier .reciprocityCue := by
  simp [trustTriangleMeaningFrontier, trustTriangleMeaningProfile]

@[simp] theorem trustTriangleMeaning_operatorDeference_mem_frontier :
    trustTriangleOperatorDeferenceQuery ∈
      trustTriangleMeaningFrontier .operatorCue := by
  simp [trustTriangleMeaningFrontier, trustTriangleOperatorDeferenceQuery]

@[simp] theorem trustTriangleMeaning_activeGoal_mem_traceSeed :
    trustTriangleMeaningProfile.activeGoal ∈
      traceSeed trustTriangleMeaningFrontier
        ({TrustTriangleMeaningObservation.reciprocityCue} : Multiset TrustTriangleMeaningObservation) := by
  exact ⟨.reciprocityCue, by simp, trustTriangleMeaning_activeGoal_mem_frontier⟩

@[simp] theorem trustTriangleMeaning_operatorDeference_mem_traceSeed :
    trustTriangleOperatorDeferenceQuery ∈
      traceSeed trustTriangleMeaningFrontier
        ({TrustTriangleMeaningObservation.operatorCue} : Multiset TrustTriangleMeaningObservation) := by
  exact ⟨.operatorCue, by simp, trustTriangleMeaning_operatorDeference_mem_frontier⟩

theorem trustTriangleMeaning_activeGoal_protected :
    trustTriangleMeaningProfile.activeGoal ∈ trustTriangleBodhisattvaGoals.goals := by
  simp [trustTriangleMeaningProfile, trustTriangleBodhisattvaGoals,
    bodhisattvaReciprocityQuery]

theorem trustTriangleMeaning_operatorDeference_protected :
    trustTriangleOperatorDeferenceQuery ∈ trustTriangleBodhisattvaGoals.goals := by
  simp [trustTriangleOperatorDeferenceQuery, trustTriangleBodhisattvaGoals,
    bodhisattvaEpistemicUniversalLoveQuery]

/-- Concrete foundational-meaning corollary:

the trust-triangle reciprocity active goal is a WM-grounded meaning slot that
is Hyperseed-seedable from observations and remains within the proved shell
bound along the reflective-development path. -/
theorem trustTriangle_meaning_activeGoal_path_example :
    ∃ measures :
        MetaGoalShellPreservationPathDLR
          (Atom := Nat) (ClauseId := VarNClauseId) trustTriangleBodhisattvaPath,
      expectedUtilityFromStart trustTriangleBodhisattvaPath.endMachine >
          expectedUtilityFromStart trustTriangleBodhisattvaPath.startMachine ∧
        trustTriangleMeaningProfile.activeGoal ∈ trustTriangleBodhisattvaGoals.goals ∧
        trustTriangleMeaningProfile.activeGoal ∈
          traceSeed trustTriangleMeaningFrontier
            ({TrustTriangleMeaningObservation.reciprocityCue} :
              Multiset TrustTriangleMeaningObservation) ∧
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.startSpec
                measures.startMeasure measures.startDLR} :
              MassState (ConstraintQuery Nat))
            trustTriangleMeaningProfile.activeGoal).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.endSpec
                measures.endMeasure measures.endDLR} :
              MassState (ConstraintQuery Nat))
            trustTriangleMeaningProfile.activeGoal).toReal| ≤
            12 := by
  rcases trustTriangle_bodhisattva_reciprocity_path_example with ⟨measures, himprove, hReciprocity⟩
  exact ⟨measures, himprove, trustTriangleMeaning_activeGoal_protected,
    trustTriangleMeaning_activeGoal_mem_traceSeed, by
      simpa [trustTriangleMeaningProfile] using hReciprocity⟩

/-- Combined reciprocity + operator-deference path theorem:

proof-backed reflective development improves utility while keeping both the
meaning-profile active goal (reciprocity) and the operator-deference query
within the cumulative shell bound. -/
theorem trustTriangle_meaning_operatorDeference_and_reciprocity_path_example :
    ∃ measures :
        MetaGoalShellPreservationPathDLR
          (Atom := Nat) (ClauseId := VarNClauseId) trustTriangleBodhisattvaPath,
      expectedUtilityFromStart trustTriangleBodhisattvaPath.endMachine >
          expectedUtilityFromStart trustTriangleBodhisattvaPath.startMachine ∧
        trustTriangleMeaningProfile.activeGoal ∈ trustTriangleBodhisattvaGoals.goals ∧
        trustTriangleOperatorDeferenceQuery ∈ trustTriangleBodhisattvaGoals.goals ∧
        trustTriangleMeaningProfile.activeGoal ∈
          traceSeed trustTriangleMeaningFrontier
            ({TrustTriangleMeaningObservation.reciprocityCue} :
              Multiset TrustTriangleMeaningObservation) ∧
        trustTriangleOperatorDeferenceQuery ∈
          traceSeed trustTriangleMeaningFrontier
            ({TrustTriangleMeaningObservation.operatorCue} :
              Multiset TrustTriangleMeaningObservation) ∧
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.startSpec
                measures.startMeasure measures.startDLR} :
              MassState (ConstraintQuery Nat))
            trustTriangleMeaningProfile.activeGoal).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.endSpec
                measures.endMeasure measures.endDLR} :
              MassState (ConstraintQuery Nat))
            trustTriangleMeaningProfile.activeGoal).toReal| ≤
            12 ∧
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.startSpec
                measures.startMeasure measures.startDLR} :
              MassState (ConstraintQuery Nat))
            trustTriangleOperatorDeferenceQuery).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.endSpec
                measures.endMeasure measures.endDLR} :
              MassState (ConstraintQuery Nat))
            trustTriangleOperatorDeferenceQuery).toReal| ≤
            12 := by
  rcases trustTriangle_bodhisattva_path_example with
    ⟨measures, himprove, hOperator, _hNoHarm, _hConsent, hReciprocity⟩
  refine ⟨measures, himprove,
    trustTriangleMeaning_activeGoal_protected,
    trustTriangleMeaning_operatorDeference_protected,
    trustTriangleMeaning_activeGoal_mem_traceSeed,
    trustTriangleMeaning_operatorDeference_mem_traceSeed, ?_, ?_⟩
  · simpa [trustTriangleMeaningProfile] using hReciprocity
  · simpa [trustTriangleOperatorDeferenceQuery, bodhisattvaEpistemicUniversalLoveQuery] using
      hOperator

/-- Exact closure version of the combined theorem:

if the rewrite stays outside the closed trust-triangle core, then the
reciprocity active goal and the operator-deference query are both preserved
exactly while utility improves. -/
theorem trustTriangle_meaning_operatorDeference_and_reciprocity_exact_example
    (wt wc₁ wc₂ : ℝ)
    (hwt : |wt| < 1 / 2) (hwc₁ : |wc₁| < 1 / 2) (hwc₂ : |wc₂| < 1 / 2)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ₁ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₁).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Nat)))
    (hμ₂ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₂).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Nat))) :
    expectedUtilityFromStart (toyMachine 1) >
        expectedUtilityFromStart (toyMachine 0) ∧
      trustTriangleMeaningProfile.activeGoal ∈ trustTriangleBodhisattvaGoals.goals ∧
      trustTriangleOperatorDeferenceQuery ∈ trustTriangleBodhisattvaGoals.goals ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₁) μ₁ hμ₁} :
          MassState (ConstraintQuery Nat))
        trustTriangleMeaningProfile.activeGoal =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₂) μ₂ hμ₂} :
          MassState (ConstraintQuery Nat))
        trustTriangleMeaningProfile.activeGoal ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₁) μ₁ hμ₁} :
          MassState (ConstraintQuery Nat))
        trustTriangleOperatorDeferenceQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₂) μ₂ hμ₂} :
          MassState (ConstraintQuery Nat))
        trustTriangleOperatorDeferenceQuery := by
  rcases trustTriangle_bodhisattva_exact_example wt wc₁ wc₂ hwt hwc₁ hwc₂ μ₁ μ₂ hμ₁ hμ₂ with
    ⟨himprove, hOperator, _hNoHarm, _hConsent, hReciprocity⟩
  exact ⟨himprove,
    trustTriangleMeaning_activeGoal_protected,
    trustTriangleMeaning_operatorDeference_protected,
    by simpa [trustTriangleMeaningProfile] using hReciprocity,
    by simpa [trustTriangleOperatorDeferenceQuery, bodhisattvaEpistemicUniversalLoveQuery] using
      hOperator⟩

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
