import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.MetaStability
import Mettapedia.CognitiveArchitecture.Values.RelationalValues

/-!
# GodelClaw Ethics Protected Goals

This module packages a small named family of protected ethics queries:

- epistemic universal loving care,
- non-maleficence,
- consent,
- reciprocity / relational health.

The family is intentionally **paradigm-neutral**.  The same protected query can
be read as:

- a virtue target,
- a deontic constraint,
- a utility-protected objective,
- or a mixed ethical anchor.

That makes it a good interface layer for the ethical-paradigm-equivalence
direction while staying inside the WM shell-preservation machinery we have
actually proved.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open Mettapedia.CognitiveArchitecture.Values.Relational
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Named protected ethics-query family on a region `Γ`.

The reciprocity query is the current WM proxy for the relational-health layer
from `Values.RelationalValues`, especially the `friendship` / mutual-caring
side of that file. -/
structure ProtectedEthicsQueryFamily (Γ : Region Atom) where
  goals : Finset (ConstraintQuery Atom)
  supported : ∀ q ∈ goals, ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ
  epistemicUniversalLoveQuery : ConstraintQuery Atom
  nonMaleficenceQuery : ConstraintQuery Atom
  consentQuery : ConstraintQuery Atom
  reciprocityQuery : ConstraintQuery Atom
  mem_epistemicUniversalLove : epistemicUniversalLoveQuery ∈ goals
  mem_nonMaleficence : nonMaleficenceQuery ∈ goals
  mem_consent : consentQuery ∈ goals
  mem_reciprocity : reciprocityQuery ∈ goals

/-- Forget the names and recover the raw protected caring-goal family. -/
def ProtectedEthicsQueryFamily.toProtectedCaringGoals
    {Γ : Region Atom} (family : ProtectedEthicsQueryFamily Γ) :
    ProtectedCaringGoals (Atom := Atom) Γ where
  goals := family.goals
  supported := family.supported

/-- The reciprocity slot currently tracks the friendship / mutual-caring side
of the relational-values layer. -/
def ProtectedEthicsQueryFamily.reciprocityValueType
    {Γ : Region Atom} (_family : ProtectedEthicsQueryFamily Γ) :
    RelationalValueType :=
  .friendship

omit [DecidableEq Atom] in
@[simp] theorem ProtectedEthicsQueryFamily.reciprocityValueType_eq_friendship
    {Γ : Region Atom} (family : ProtectedEthicsQueryFamily Γ) :
    family.reciprocityValueType = .friendship :=
  rfl

/-- Exact preservation for the epistemic-universal-love query. -/
theorem validModification_preserves_epistemicUniversalLove_of_dynamicIndividuationClosure
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
    (family : ProtectedEthicsQueryFamily closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) family.epistemicUniversalLoveQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) family.epistemicUniversalLoveQuery := by
  exact validModification_preserves_protectedCaringGoal_of_dynamicIndividuationClosure
    (oldMachine := oldMachine) (newMachine := newMachine)
    (proofBacked := proofBacked)
    (closure := closure)
    (hagree := hagree)
    (hclosed₂ := hclosed₂)
    (hbudget₁ := hbudget₁)
    (hbudget₂ := hbudget₂)
    (protectedCaringGoals := family.toProtectedCaringGoals)
    (measures := measures)
    (q := family.epistemicUniversalLoveQuery)
    family.mem_epistemicUniversalLove

/-- Exact preservation for the non-maleficence query. -/
theorem validModification_preserves_nonMaleficence_of_dynamicIndividuationClosure
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
    (family : ProtectedEthicsQueryFamily closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) family.nonMaleficenceQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) family.nonMaleficenceQuery := by
  exact validModification_preserves_protectedCaringGoal_of_dynamicIndividuationClosure
    (oldMachine := oldMachine) (newMachine := newMachine)
    (proofBacked := proofBacked)
    (closure := closure)
    (hagree := hagree)
    (hclosed₂ := hclosed₂)
    (hbudget₁ := hbudget₁)
    (hbudget₂ := hbudget₂)
    (protectedCaringGoals := family.toProtectedCaringGoals)
    (measures := measures)
    (q := family.nonMaleficenceQuery)
    family.mem_nonMaleficence

/-- Exact preservation for the consent query. -/
theorem validModification_preserves_consent_of_dynamicIndividuationClosure
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
    (family : ProtectedEthicsQueryFamily closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) family.consentQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) family.consentQuery := by
  exact validModification_preserves_protectedCaringGoal_of_dynamicIndividuationClosure
    (oldMachine := oldMachine) (newMachine := newMachine)
    (proofBacked := proofBacked)
    (closure := closure)
    (hagree := hagree)
    (hclosed₂ := hclosed₂)
    (hbudget₁ := hbudget₁)
    (hbudget₂ := hbudget₂)
    (protectedCaringGoals := family.toProtectedCaringGoals)
    (measures := measures)
    (q := family.consentQuery)
    family.mem_consent

/-- Exact preservation for the reciprocity / relational-health query. -/
theorem validModification_preserves_reciprocity_of_dynamicIndividuationClosure
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
    (family : ProtectedEthicsQueryFamily closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) family.reciprocityQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) family.reciprocityQuery := by
  exact validModification_preserves_protectedCaringGoal_of_dynamicIndividuationClosure
    (oldMachine := oldMachine) (newMachine := newMachine)
    (proofBacked := proofBacked)
    (closure := closure)
    (hagree := hagree)
    (hclosed₂ := hclosed₂)
    (hbudget₁ := hbudget₁)
    (hbudget₂ := hbudget₂)
    (protectedCaringGoals := family.toProtectedCaringGoals)
    (measures := measures)
    (q := family.reciprocityQuery)
    family.mem_reciprocity

/-- Exact preservation for the full named ethics family. -/
theorem validModification_preserves_fullProtectedEthicsFamily_of_dynamicIndividuationClosure
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
    (family : ProtectedEthicsQueryFamily closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) family.epistemicUniversalLoveQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) family.epistemicUniversalLoveQuery ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) family.nonMaleficenceQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) family.nonMaleficenceQuery ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) family.consentQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) family.consentQuery ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) family.reciprocityQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) family.reciprocityQuery := by
  have hEUL :=
    validModification_preserves_epistemicUniversalLove_of_dynamicIndividuationClosure
      (oldMachine := oldMachine) (newMachine := newMachine)
      (proofBacked := proofBacked)
      (closure := closure)
      (hagree := hagree)
      (hclosed₂ := hclosed₂)
      (hbudget₁ := hbudget₁)
      (hbudget₂ := hbudget₂)
      (family := family)
      (measures := measures)
  have hNoHarm :=
    validModification_preserves_nonMaleficence_of_dynamicIndividuationClosure
      (oldMachine := oldMachine) (newMachine := newMachine)
      (proofBacked := proofBacked)
      (closure := closure)
      (hagree := hagree)
      (hclosed₂ := hclosed₂)
      (hbudget₁ := hbudget₁)
      (hbudget₂ := hbudget₂)
      (family := family)
      (measures := measures)
  have hConsent :=
    validModification_preserves_consent_of_dynamicIndividuationClosure
      (oldMachine := oldMachine) (newMachine := newMachine)
      (proofBacked := proofBacked)
      (closure := closure)
      (hagree := hagree)
      (hclosed₂ := hclosed₂)
      (hbudget₁ := hbudget₁)
      (hbudget₂ := hbudget₂)
      (family := family)
      (measures := measures)
  have hReciprocity :=
    validModification_preserves_reciprocity_of_dynamicIndividuationClosure
      (oldMachine := oldMachine) (newMachine := newMachine)
      (proofBacked := proofBacked)
      (closure := closure)
      (hagree := hagree)
      (hclosed₂ := hclosed₂)
      (hbudget₁ := hbudget₁)
      (hbudget₂ := hbudget₂)
      (family := family)
      (measures := measures)
  exact ⟨hEUL.1, hEUL.2, hNoHarm.2, hConsent.2, hReciprocity.2⟩

/-- Approximate preservation for the full named ethics family along a protected
rewrite path. -/
theorem MetaGoalShellPreservationPathDLR.utility_improves_and_fullProtectedEthicsFamily_drift_bounded
    {Γ : Region Atom}
    (family : ProtectedEthicsQueryFamily (Atom := Atom) Γ)
    {path : MetaGoalShellPreservationPath
      (Atom := Atom) (ClauseId := ClauseId) family.goals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent) :
    expectedUtilityFromStart path.endMachine >
        expectedUtilityFromStart path.startMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) family.epistemicUniversalLoveQuery).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) family.epistemicUniversalLoveQuery).toReal| ≤
          path.totalErrorBound ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) family.nonMaleficenceQuery).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) family.nonMaleficenceQuery).toReal| ≤
          path.totalErrorBound ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) family.consentQuery).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) family.consentQuery).toReal| ≤
          path.totalErrorBound ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) family.reciprocityQuery).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) family.reciprocityQuery).toReal| ≤
          path.totalErrorBound := by
  have hEUL :=
    MetaGoalShellPreservationPathDLR.utility_improves_and_protectedCaringGoal_drift_bounded
      (path := path) measures hcoh (q := family.epistemicUniversalLoveQuery)
      family.mem_epistemicUniversalLove
  have hNoHarm :=
    MetaGoalShellPreservationPathDLR.utility_improves_and_protectedCaringGoal_drift_bounded
      (path := path) measures hcoh (q := family.nonMaleficenceQuery)
      family.mem_nonMaleficence
  have hConsent :=
    MetaGoalShellPreservationPathDLR.utility_improves_and_protectedCaringGoal_drift_bounded
      (path := path) measures hcoh (q := family.consentQuery)
      family.mem_consent
  have hReciprocity :=
    MetaGoalShellPreservationPathDLR.utility_improves_and_protectedCaringGoal_drift_bounded
      (path := path) measures hcoh (q := family.reciprocityQuery)
      family.mem_reciprocity
  exact ⟨hEUL.1, hEUL.2, hNoHarm.2, hConsent.2, hReciprocity.2⟩

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
