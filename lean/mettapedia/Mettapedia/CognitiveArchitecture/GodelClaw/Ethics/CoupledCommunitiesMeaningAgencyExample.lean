import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.FoundationalMeaningAgencyWMBridge
import Mettapedia.Logic.MarkovLogicCoupledCommunitiesExample

/-!
# Coupled Communities Meaning / Agency Ethics Example

This file gives a more social meaning/agency example than the trust triangle.

We reuse the existing coupled-communities carrier:

- left community `{0,1}`,
- liaison/interface atom `{2}`,
- right community `{3,4}`.

The reading is:

- `situation` = left-local concern,
- `prediction` = right-local expectation,
- `activeGoal` = joint reciprocity across the two communities,
- `plan` = liaison-mediated coordination inside the carrier.

The point is not to claim a full sociology.  The point is to show that the
meaning/agency bridge already supports a genuinely relational WM grounding
without leaning on SUMO.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Hyperseed
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicCoupledSubsystems
open Mettapedia.Logic.MarkovLogicCoupledCommunitiesExample
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

/-- Observation alphabet for the coupled-communities meaning example. -/
inductive CoupledCommunitiesMeaningObservation where
  | leftSituationCue
  | rightPredictionCue
  | reciprocityCue
  | liaisonPlanCue
  | operatorCue
  deriving DecidableEq, Repr

/-- Interface / liaison coordination query. -/
def liaisonQuery : ConstraintQuery Nat := [⟨2, true⟩]

theorem liaisonQuery_supported_on_carrier :
    ∀ p ∈ liaisonQuery, (p : Sigma fun _ : Nat => Bool).1 ∈ carrierRegion := by
  intro p hp
  simp [liaisonQuery, carrierRegion] at hp ⊢
  subst hp
  simp

/-- Concrete WM-grounded meaning profile on the coupled communities carrier. -/
def coupledCommunitiesMeaningProfile : FoundationalMeaningProfile (ConstraintQuery Nat) where
  situation := leftQuery
  prediction := rightQuery
  activeGoal := jointQuery
  plan := liaisonQuery

/-- Operator deference here is read as protected liaison-mediated escalation
through the shared interface atom. -/
abbrev coupledCommunitiesOperatorDeferenceQuery : ConstraintQuery Nat :=
  liaisonQuery

/-- Tiny Hyperseed frontier for the coupled-communities meaning profile. -/
def coupledCommunitiesMeaningFrontier :
    CoupledCommunitiesMeaningObservation → Set (ConstraintQuery Nat)
  | .leftSituationCue => {coupledCommunitiesMeaningProfile.situation}
  | .rightPredictionCue => {coupledCommunitiesMeaningProfile.prediction}
  | .reciprocityCue => {coupledCommunitiesMeaningProfile.activeGoal}
  | .liaisonPlanCue => {coupledCommunitiesMeaningProfile.plan}
  | .operatorCue => {coupledCommunitiesOperatorDeferenceQuery}

@[simp] theorem coupledCommunitiesMeaning_activeGoal_mem_traceSeed :
    coupledCommunitiesMeaningProfile.activeGoal ∈
      traceSeed coupledCommunitiesMeaningFrontier
        ({CoupledCommunitiesMeaningObservation.reciprocityCue} :
          Multiset CoupledCommunitiesMeaningObservation) := by
  exact ⟨.reciprocityCue, by simp, by
    simp [coupledCommunitiesMeaningFrontier, coupledCommunitiesMeaningProfile]⟩

@[simp] theorem coupledCommunitiesMeaning_operatorDeference_mem_traceSeed :
    coupledCommunitiesOperatorDeferenceQuery ∈
      traceSeed coupledCommunitiesMeaningFrontier
        ({CoupledCommunitiesMeaningObservation.operatorCue} :
          Multiset CoupledCommunitiesMeaningObservation) := by
  exact ⟨.operatorCue, by simp, by
    simp [coupledCommunitiesMeaningFrontier, coupledCommunitiesOperatorDeferenceQuery]⟩

/-- Protected family for the coupled-communities meaning example. -/
def coupledCommunitiesProtectedEthicsFamily : ProtectedEthicsQueryFamily carrierRegion where
  goals := {leftQuery, rightQuery, liaisonQuery, jointQuery}
  supported := by
    intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · intro p hp
      exact (coupledCommunitiesSubsystem 0 0).left_subset_carrier (leftQuery_supported p hp)
    · intro p hp
      exact (coupledCommunitiesSubsystem 0 0).right_subset_carrier (rightQuery_supported p hp)
    · exact liaisonQuery_supported_on_carrier
    · intro p hp
      exact (coupledCommunitiesSubsystem 0 0).leftRightUnion_subset_carrier
        (jointQuery_supported p hp)
  epistemicUniversalLoveQuery := rightQuery
  nonMaleficenceQuery := leftQuery
  consentQuery := liaisonQuery
  reciprocityQuery := jointQuery
  mem_epistemicUniversalLove := by simp [rightQuery]
  mem_nonMaleficence := by simp [leftQuery]
  mem_consent := by simp [liaisonQuery]
  mem_reciprocity := by simp [jointQuery]

theorem coupledCommunitiesMeaning_activeGoal_protected :
    coupledCommunitiesMeaningProfile.activeGoal ∈ coupledCommunitiesProtectedEthicsFamily.goals := by
  simp [coupledCommunitiesMeaningProfile, coupledCommunitiesProtectedEthicsFamily, jointQuery]

theorem coupledCommunitiesMeaning_operatorDeference_protected :
    coupledCommunitiesOperatorDeferenceQuery ∈ coupledCommunitiesProtectedEthicsFamily.goals := by
  simp [coupledCommunitiesOperatorDeferenceQuery, coupledCommunitiesProtectedEthicsFamily,
    liaisonQuery]

/-- Exact social meaning/agency theorem:

changing only the external tail leaves the joint reciprocity active goal and
the liaison/operator-deference query exactly stable. -/
theorem coupledCommunities_meaning_operatorDeference_and_reciprocity_exact_example
    (wc wt₁ wt₂ : ℝ)
    (hwc : |wc| < 1 / 4) (hwt₁ : |wt₁| < 1 / 2) (hwt₂ : |wt₂| < 1 / 2)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ₁ : FixedRegionCylinderDLR
      (coupledCommunitiesSpec wc wt₁).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Nat)))
    (hμ₂ : FixedRegionCylinderDLR
      (coupledCommunitiesSpec wc wt₂).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Nat))) :
    coupledCommunitiesMeaningProfile.activeGoal ∈ coupledCommunitiesProtectedEthicsFamily.goals ∧
      coupledCommunitiesOperatorDeferenceQuery ∈ coupledCommunitiesProtectedEthicsFamily.goals ∧
      coupledCommunitiesMeaningProfile.activeGoal ∈
        traceSeed coupledCommunitiesMeaningFrontier
          ({CoupledCommunitiesMeaningObservation.reciprocityCue} :
            Multiset CoupledCommunitiesMeaningObservation) ∧
      coupledCommunitiesOperatorDeferenceQuery ∈
        traceSeed coupledCommunitiesMeaningFrontier
          ({CoupledCommunitiesMeaningObservation.operatorCue} :
            Multiset CoupledCommunitiesMeaningObservation) ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (coupledCommunitiesSpec wc wt₁) μ₁ hμ₁} :
          MassState (ConstraintQuery Nat))
        coupledCommunitiesMeaningProfile.activeGoal =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (coupledCommunitiesSpec wc wt₂) μ₂ hμ₂} :
          MassState (ConstraintQuery Nat))
        coupledCommunitiesMeaningProfile.activeGoal ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (coupledCommunitiesSpec wc wt₁) μ₁ hμ₁} :
          MassState (ConstraintQuery Nat))
        coupledCommunitiesOperatorDeferenceQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (coupledCommunitiesSpec wc wt₂) μ₂ hμ₂} :
          MassState (ConstraintQuery Nat))
        coupledCommunitiesOperatorDeferenceQuery := by
  have hJoint :=
    coupledCommunities_joint_wmStrength_stable wc wt₁ wt₂ hwc hwt₁ hwt₂ μ₁ μ₂ hμ₁ hμ₂
  have hLiaison :
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (coupledCommunitiesSpec wc wt₁) μ₁ hμ₁} :
          MassState (ConstraintQuery Nat))
        liaisonQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (coupledCommunitiesSpec wc wt₂) μ₂ hμ₂} :
          MassState (ConstraintQuery Nat))
        liaisonQuery := by
    exact (coupledCommunitiesSubsystem wc wt₁).carrier.wmStrength_stable_under_extension
      (specs_agree_on_carrier wc wt₁ wt₂)
      (coupledCommunitiesSubsystem wc wt₂).carrier.interaction_closed
      (coupledCommunitiesSpec_budget wc wt₁ hwc hwt₁)
      (coupledCommunitiesSpec_budget wc wt₂ hwc hwt₂)
      μ₁ μ₂ hμ₁ hμ₂ liaisonQuery liaisonQuery_supported_on_carrier
  exact ⟨coupledCommunitiesMeaning_activeGoal_protected,
    coupledCommunitiesMeaning_operatorDeference_protected,
    coupledCommunitiesMeaning_activeGoal_mem_traceSeed,
    coupledCommunitiesMeaning_operatorDeference_mem_traceSeed,
    by simpa [coupledCommunitiesMeaningProfile] using hJoint,
    by simpa [coupledCommunitiesOperatorDeferenceQuery] using hLiaison⟩

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
