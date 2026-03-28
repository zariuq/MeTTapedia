import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.UpperShard
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.FoundationalMeaningAgencyWMBridge
import Mettapedia.Hyperseed.Basic

set_option autoImplicit false

/-!
# Upper-Shard Ontology to Hyperseed / WM Bridge

This module compiles structured upper-shard ethics claims into the existing
Hyperseed and WM machinery.

The flow is:

`upper-shard ontology claims → WM singleton queries → Hyperseed trace seeds →
foundational-meaning active goals → protected WM meta-stability`.

This keeps the deeper ontological structure visible until the final WM
boundary.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology

open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
open Mettapedia.Hyperseed
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open MeasureTheory

universe u w x

/-- Observation frontier extracted directly from four-axis structured claims. -/
def structuredClaimFrontier
    {Obs : Type x} {World : Type u} {Agent : Type u} {Atom : Type*}
    (extract : Obs → Set (StructuredEthicalClaim World Agent))
    (enc : StructuredEthicsQueryEncoder World Agent Atom) :
    Obs → Set (ConstraintQuery Atom) :=
  fun o => { q | ∃ claim ∈ extract o, q = claim.toQuery enc }

@[simp] theorem mem_structuredClaimFrontier
    {Obs : Type x} {World : Type u} {Agent : Type u} {Atom : Type*}
    (extract : Obs → Set (StructuredEthicalClaim World Agent))
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (o : Obs) (q : ConstraintQuery Atom) :
    q ∈ structuredClaimFrontier extract enc o ↔
      ∃ claim ∈ extract o, q = claim.toQuery enc := by
  rfl

/-- Observation frontier extracted from structured upper-shard ethics claims. -/
def upperShardFrontier
    {Obs : Type x} {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (extract : Obs → Set (UpperShardEthicalClaim World Agent Label))
    (enc : EthicsQueryEncoder Agent Label Atom) :
    Obs → Set (ConstraintQuery Atom) :=
  fun o => { q | ∃ claim ∈ extract o, q = claim.toQuery enc }

@[simp] theorem mem_upperShardFrontier
    {Obs : Type x} {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (extract : Obs → Set (UpperShardEthicalClaim World Agent Label))
    (enc : EthicsQueryEncoder Agent Label Atom)
    (o : Obs) (q : ConstraintQuery Atom) :
    q ∈ upperShardFrontier extract enc o ↔
      ∃ claim ∈ extract o, q = claim.toQuery enc := by
  rfl

/-- A foundational-meaning profile whose active goal is already represented at
the four-axis kernel level. -/
structure StructuredFoundationalMeaningProfile
    (World : Type u) (Agent : Type u) (Atom : Type*) where
  situation : ConstraintQuery Atom
  prediction : ConstraintQuery Atom
  activeGoalClaim : StructuredEthicalClaim World Agent
  plan : ConstraintQuery Atom

/-- The active-goal WM query of a four-axis structured meaning profile. -/
def StructuredFoundationalMeaningProfile.activeGoalQuery
    {World : Type u} {Agent : Type u} {Atom : Type*}
    (profile : StructuredFoundationalMeaningProfile World Agent Atom)
    (enc : StructuredEthicsQueryEncoder World Agent Atom) : ConstraintQuery Atom :=
  profile.activeGoalClaim.toQuery enc

/-- Forget the richer active-goal structure and recover the raw
foundational-meaning profile. -/
def StructuredFoundationalMeaningProfile.toMeaningProfile
    {World : Type u} {Agent : Type u} {Atom : Type*}
    (profile : StructuredFoundationalMeaningProfile World Agent Atom)
    (enc : StructuredEthicsQueryEncoder World Agent Atom) :
    Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.FoundationalMeaningProfile
      (ConstraintQuery Atom) where
  situation := profile.situation
  prediction := profile.prediction
  activeGoal := profile.activeGoalQuery enc
  plan := profile.plan

theorem StructuredFoundationalMeaningProfile.activeGoal_mem_frontier
    {Obs : Type x} {World : Type u} {Agent : Type u} {Atom : Type*}
    (extract : Obs → Set (StructuredEthicalClaim World Agent))
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (profile : StructuredFoundationalMeaningProfile World Agent Atom)
    (o : Obs)
    (hmem : profile.activeGoalClaim ∈ extract o) :
    profile.activeGoalQuery enc ∈ structuredClaimFrontier extract enc o := by
  exact ⟨profile.activeGoalClaim, hmem, rfl⟩

theorem StructuredFoundationalMeaningProfile.activeGoal_mem_traceSeed
    {Obs : Type x} {World : Type u} {Agent : Type u} {Atom : Type*}
    (extract : Obs → Set (StructuredEthicalClaim World Agent))
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (σ : Multiset Obs)
    (o : Obs)
    (profile : StructuredFoundationalMeaningProfile World Agent Atom)
    (ho : o ∈ σ)
    (hmem : profile.activeGoalClaim ∈ extract o) :
    profile.activeGoalQuery enc ∈
      Mettapedia.Hyperseed.traceSeed (structuredClaimFrontier extract enc) σ := by
  exact ⟨o, ho, profile.activeGoal_mem_frontier extract enc o hmem⟩

/-- A foundational-meaning profile whose active goal is still represented as a
structured upper-shard claim. -/
structure UpperShardFoundationalMeaningProfile
    (World : Type u) (Agent : Type u) (Label : Type w) (Atom : Type*) where
  situation : ConstraintQuery Atom
  prediction : ConstraintQuery Atom
  activeGoalClaim : UpperShardEthicalClaim World Agent Label
  plan : ConstraintQuery Atom

/-- The active-goal WM query corresponding to the structured upper-shard claim. -/
def UpperShardFoundationalMeaningProfile.activeGoalQuery
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom) : ConstraintQuery Atom :=
  profile.activeGoalClaim.toQuery enc

/-- Forget the richer active-goal structure and reuse the already-proved
foundational-meaning bridge. -/
def UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom) :
    Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalFoundationalMeaningProfile
      Agent Label Atom where
  situation := profile.situation
  prediction := profile.prediction
  activeGoalAnchor := profile.activeGoalClaim.toAnchor
  plan := profile.plan

/-- Structured active goals from observations become frontier members. -/
theorem UpperShardFoundationalMeaningProfile.activeGoal_mem_frontier
    {Obs : Type x} {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (extract : Obs → Set (UpperShardEthicalClaim World Agent Label))
    (enc : EthicsQueryEncoder Agent Label Atom)
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom)
    (o : Obs)
    (hmem : profile.activeGoalClaim ∈ extract o) :
    profile.activeGoalQuery enc ∈ upperShardFrontier extract enc o := by
  exact ⟨profile.activeGoalClaim, hmem, rfl⟩

/-- Structured active goals from observations become Hyperseed seeds on the WM
side. -/
theorem UpperShardFoundationalMeaningProfile.activeGoal_mem_traceSeed
    {Obs : Type x} {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (extract : Obs → Set (UpperShardEthicalClaim World Agent Label))
    (enc : EthicsQueryEncoder Agent Label Atom)
    (σ : Multiset Obs)
    (o : Obs)
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom)
    (ho : o ∈ σ)
    (hmem : profile.activeGoalClaim ∈ extract o) :
    profile.activeGoalQuery enc ∈
      Mettapedia.Hyperseed.traceSeed (upperShardFrontier extract enc) σ := by
  exact ⟨o, ho, profile.activeGoal_mem_frontier extract enc o hmem⟩

/-- The active goal of a structured meaning profile is protected when it equals
one of the distinguished protected upper-shard claims. -/
def UpperShardFoundationalMeaningProfile.ActiveGoalProtectedBy
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom)
    (claims : ProtectedUpperShardClaims World Agent Label) : Prop :=
  profile.activeGoalClaim = claims.epistemicUniversalLove ∨
    profile.activeGoalClaim = claims.nonMaleficence ∨
    profile.activeGoalClaim = claims.consent ∨
    profile.activeGoalClaim = claims.reciprocity

theorem UpperShardFoundationalMeaningProfile.toEthical_activeGoalProtectedBy
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom)
    (claims : ProtectedUpperShardClaims World Agent Label)
    (hProtected : profile.ActiveGoalProtectedBy claims) :
    (profile.toEthicalFoundationalMeaningProfile).ActiveGoalProtectedBy
      claims.toProtectedEthicsAnchors := by
  rcases hProtected with h | hProtected
  · left
    simpa [UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      ProtectedUpperShardClaims.toProtectedEthicsAnchors] using
      congrArg UpperShardEthicalClaim.toAnchor h
  rcases hProtected with h | hProtected
  · right
    left
    simpa [UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      ProtectedUpperShardClaims.toProtectedEthicsAnchors] using
      congrArg UpperShardEthicalClaim.toAnchor h
  rcases hProtected with h | h
  · right
    right
    left
    simpa [UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      ProtectedUpperShardClaims.toProtectedEthicsAnchors] using
      congrArg UpperShardEthicalClaim.toAnchor h
  · right
    right
    right
    simpa [UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      ProtectedUpperShardClaims.toProtectedEthicsAnchors] using
      congrArg UpperShardEthicalClaim.toAnchor h

theorem UpperShardFoundationalMeaningProfile.activeGoal_mem_protectedFamily
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*} [DecidableEq Atom]
    {Γ : Region Atom}
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (claims : ProtectedUpperShardClaims World Agent Label)
    (hEUL : claims.epistemicUniversalLove.supportedOn enc Γ)
    (hNoHarm : claims.nonMaleficence.supportedOn enc Γ)
    (hConsent : claims.consent.supportedOn enc Γ)
    (hReciprocity : claims.reciprocity.supportedOn enc Γ)
    (hProtected : profile.ActiveGoalProtectedBy claims) :
    profile.activeGoalQuery enc ∈
      (claims.toProtectedEthicsQueryFamily enc hEUL hNoHarm hConsent hReciprocity).goals := by
  simpa [UpperShardFoundationalMeaningProfile.activeGoalQuery,
      UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      ProtectedUpperShardClaims.toProtectedEthicsQueryFamily,
      ProtectedUpperShardClaims.toProtectedEthicsAnchors,
      EthicalFoundationalMeaningProfile.activeGoalQuery]
    using
      EthicalFoundationalMeaningProfile.activeGoal_mem_protectedFamily
        (profile := profile.toEthicalFoundationalMeaningProfile)
        (enc := enc)
        (anchors := claims.toProtectedEthicsAnchors)
        (hEUL := hEUL)
        (hNoHarm := hNoHarm)
        (hConsent := hConsent)
        (hReciprocity := hReciprocity)
        (hProtected := profile.toEthical_activeGoalProtectedBy claims hProtected)

/-- Exact meta-stability wrapper for a structured upper-shard active goal. -/
theorem validModification_preserves_protectedUpperShardActiveGoal_of_dynamicIndividuationClosure
    {World : Type u}
    {Agent : Type u}
    {Label : Type w}
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {oldSpec newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (oldMachine newMachine : GodelMachineState)
    (proofBacked : validModification oldMachine newMachine)
    (closure : DynamicIndividuationClosure oldSpec)
    (hagree : SpecAgreesOnRegion oldSpec newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hclosed₂ : InteractionClosed newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hbudget₁ : oldSpec.PaperUniformSmallTotalInfluence)
    (hbudget₂ : newSpec.PaperUniformSmallTotalInfluence)
    (family : ProtectedEthicsQueryFamily (Atom := Atom) closure.proto.seed)
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (measures : CrossSpecDLR oldSpec newSpec)
    (hgoal : profile.activeGoalQuery enc ∈ family.goals) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) (profile.activeGoalQuery enc) =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) (profile.activeGoalQuery enc) := by
  have hgoal' :
      (profile.toEthicalFoundationalMeaningProfile).activeGoalQuery enc ∈ family.goals := by
    simpa [UpperShardFoundationalMeaningProfile.activeGoalQuery,
      UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalFoundationalMeaningProfile.activeGoalQuery]
      using hgoal
  simpa [UpperShardFoundationalMeaningProfile.activeGoalQuery,
      UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalFoundationalMeaningProfile.activeGoalQuery]
    using
      validModification_preserves_protectedEthicalActiveGoal_of_dynamicIndividuationClosure
          (oldMachine := oldMachine) (newMachine := newMachine)
          (proofBacked := proofBacked)
          (closure := closure)
          (hagree := hagree)
          (hclosed₂ := hclosed₂)
          (hbudget₁ := hbudget₁)
          (hbudget₂ := hbudget₂)
          (family := family)
          (profile := profile.toEthicalFoundationalMeaningProfile)
          (enc := enc)
          (measures := measures)
          hgoal'

/-- Path-level meta-stability wrapper for a structured upper-shard active
goal. -/
theorem MetaGoalShellPreservationPathDLR.utility_improves_and_protectedUpperShardActiveGoal_drift_bounded
    {World : Type u}
    {Agent : Type u}
    {Label : Type w}
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {Γ : Region Atom}
    (family : ProtectedEthicsQueryFamily (Atom := Atom) Γ)
    {path : MetaGoalShellPreservationPath
      (Atom := Atom) (ClauseId := ClauseId) family.goals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    (profile : UpperShardFoundationalMeaningProfile World Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (hgoal : profile.activeGoalQuery enc ∈ family.goals) :
    expectedUtilityFromStart path.endMachine >
        expectedUtilityFromStart path.startMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) (profile.activeGoalQuery enc)).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) (profile.activeGoalQuery enc)).toReal| ≤
          path.totalErrorBound := by
  have hgoal' :
      (profile.toEthicalFoundationalMeaningProfile).activeGoalQuery enc ∈ family.goals := by
    simpa [UpperShardFoundationalMeaningProfile.activeGoalQuery,
      UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalFoundationalMeaningProfile.activeGoalQuery]
      using hgoal
  simpa [UpperShardFoundationalMeaningProfile.activeGoalQuery,
      UpperShardFoundationalMeaningProfile.toEthicalFoundationalMeaningProfile,
      Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalFoundationalMeaningProfile.activeGoalQuery]
    using
      MetaGoalShellPreservationPathDLR.utility_improves_and_protectedEthicalActiveGoal_drift_bounded
          (family := family) measures hcoh
          (profile := profile.toEthicalFoundationalMeaningProfile)
          (enc := enc)
          hgoal'

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
