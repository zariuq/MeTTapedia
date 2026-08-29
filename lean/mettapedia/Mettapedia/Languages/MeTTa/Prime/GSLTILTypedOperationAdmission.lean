import Mettapedia.GSLT.LanguageDef.GSLTILUniversalStructure
import Mettapedia.Languages.MeTTa.Prime.GSLTILLayeredCrown
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge

/-!
# Typed Prime operations through GSLT-IL elaboration and NIK admission

A recognized Prime language operation carries three identities that must not
be conflated:

* its authored `PureTm` spelling;
* its independently decoded endpoint-indexed operation path; and
* the revision-current realization admitted for execution.

This module connects those identities.  The authored spelling becomes the
occurrence of a singleton GSLT-IL route declaration.  The independently
checked operation supplies an exact typed elaboration profile for that
occurrence.  The decoded path supplies the represented Data execution and the
observed NIK refinement.  A single joined object proves that the active direct
map is the operational route selected by the decoder.

The construction does not globalize exact elaboration.  Raw GSLT-IL commands
may retain several elaboration worlds, and distinct Prime spellings remain
distinct occurrences even when the spelling quotient gives them the same
decoded execution.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILTypedOperationAdmission

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.ElaborationSelection
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationFactorization
open Mettapedia.Languages.MeTTa.Prime.LanguageOperationNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.IndexedLanguageChange
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Source-faithful singleton authored profiles -/

def operationRouteName : String := "prime-operation"

/-- The command payload retains the exact authored Prime spelling. -/
def operationState (operation : RecognizedOperation) : Pattern :=
  .apply "prime-operation-term" [quoteClosedTm operation.term]

/-- The declaration occurrence is the authored term, while its endpoint
spaces are obtained from the independently decoded intrinsic indices. -/
def operationRoute (operation : RecognizedOperation) : RouteDecl where
  occurrence := .apply "prime-operation-occurrence"
    [quoteClosedTm operation.term]
  name := operationRouteName
  sourceSpace := quoteClosedTm
    (languageTerm operation.decoded.source)
  targetSpace := quoteClosedTm
    (languageTerm operation.decoded.target)

/-- The smallest authored GSLT-IL program exposing one recognized Prime
operation.  Operational rows are supplied later by the decoded route rather
than duplicated as a finite lookup table here. -/
def authoredProgram (operation : RecognizedOperation) :
    Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.Program :=
  { spaceRules := []
    routes := [operationRoute operation]
    routeRules := [] }

def surfaceCommand (operation : RecognizedOperation) : Pattern :=
  routeCall operationRouteName (operationState operation)

def internalCommand (operation : RecognizedOperation) : Pattern :=
  viaPattern forwardKind (routeIdentity (operationRoute operation))
    (operationRoute operation).sourceSpace
    (operationRoute operation).targetSpace
    (operationState operation)

/-- The source-faithful command is a genuine elaboration of its authored
singleton program. -/
theorem operation_elaborates (operation : RecognizedOperation) :
    Elaborates (authoredProgram operation) (surfaceCommand operation)
      (internalCommand operation) := by
  simpa [authoredProgram, surfaceCommand, internalCommand, operationRoute] using
    (Elaborates.route
      (program := authoredProgram operation)
      (route := operationRoute operation)
      (by simp [authoredProgram]) (operationState operation))

/-- Typed operation evidence designates the exact accepted world without
asserting that all raw commands in the surrounding language are exact. -/
def typedProfile (operation : RecognizedOperation) :
    Profile (authoredProgram operation) where
  Command := Unit
  surface := fun _ => surfaceCommand operation
  Accepts := fun _ internal => internal = internalCommand operation
  sound := by
    intro command internal same
    cases same
    exact operation_elaborates operation

def exactSelection (operation : RecognizedOperation) :
    ExactSelection (typedProfile operation) where
  select := fun _ => internalCommand operation
  selected := fun _ => rfl
  reflects := fun _ {_} accepted => accepted.symm

/-- The same exact profile viewed through the proof-relevant elaboration-world
interface.  The conservative bridge retains the accepted evidence and proves
that this particular typed island has no hidden derivation multiplicity. -/
def typedEvidenceProfile (operation : RecognizedOperation) :=
  Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.PropositionalBridge.ofPropositional
    (typedProfile operation)

/-- The typed operation's accepted world fibre is contractible and therefore
earns exact companion representation. -/
theorem typed_world_fibre_contractible (operation : RecognizedOperation) :
    Nonempty (ExactSelection (typedProfile operation)) ∧
      Nonempty (Mettapedia.GSLT.LooseRelationEquipment.Representation
        (typedProfile operation).related) :=
  ⟨⟨exactSelection operation⟩,
    ⟨(exactSelection operation).toRepresentation⟩⟩

/-- Prime's exact selected operation also satisfies the stronger
proof-history criterion.  Its native elaborator represents the complete
outcome/evidence relation, not merely the visible internal command. -/
theorem typed_evidence_profile_represented (operation : RecognizedOperation) :
    Nonempty
        (Mettapedia.GSLT.LooseRelationEquipment.Representation
          (typedEvidenceProfile operation).related) ∧
      (typedEvidenceProfile operation).HistoryThin := by
  constructor
  · exact
      (Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.PropositionalBridge.representable_iff_exactSelection
        (typedProfile operation)).2 ⟨exactSelection operation⟩
  · exact
      Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.PropositionalBridge.historyThin
        (typedProfile operation)

/-- The elaboration profile retains the exact authored term as its route
occurrence rather than replacing it by the decoded quotient. -/
@[simp] theorem selected_occurrence (operation : RecognizedOperation) :
    (operationRoute operation).occurrence =
      .apply "prime-operation-occurrence" [quoteClosedTm operation.term] :=
  rfl

/-- The term retained in the occurrence is independently well typed at the
endpoints used by the selected route. -/
theorem selected_term_wellTyped (operation : RecognizedOperation) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationSemantics.HasTypeDecl
      operationDeclEnv .nil operation.term
      (routeType (languageTerm operation.decoded.source)
        (languageTerm operation.decoded.target)) :=
  operation.wellTyped

/-! ## Exact elaboration joined to represented, admitted execution -/

/-- One Prime operation after all three independently meaningful boundaries
have been joined: authored elaboration, represented execution, and
revision-indexed NIK admission. -/
structure SelectedAdmittedOperation
    (dependencies : DependencySystem)
    (revision : dependencies.Revision)
    (model : PrimeModel)
    (operation : RecognizedOperation)
    (sourceMeaning : StateAt model operation.decoded.source → Prop) where
  elaboration : ExactSelection (typedProfile operation)
  evidenceElaboration :
    Mettapedia.GSLT.LooseRelationEquipment.Representation
      (typedEvidenceProfile operation).related
  evidenceElaborationMap :
    evidenceElaboration.map = elaboration.select
  realization :
    GSLTILLayeredCrown.SelectedRouteRealization model operation.decoded
  admission : ObservedAdmittedAt dependencies revision
    (sourceObserved model operation.decoded.program sourceMeaning)
    (targetImageObserved model operation.decoded.program sourceMeaning)
  admittedRouteAgreement :
    admission.refinement.refinement.realization.mapTerm =
      transportTerm (diagram model)
        (CurrentExecution.actionOfDecoded operation.decoded).operationalRoute

/-- Construct the joined object from recognition and the selected dependency
revision.  No checker or selection policy occurs in its active runner. -/
def selectAndAdmit (dependencies : DependencySystem)
    (revision : dependencies.Revision) (model : PrimeModel)
    (operation : RecognizedOperation)
    (sourceMeaning : StateAt model operation.decoded.source → Prop) :
    SelectedAdmittedOperation dependencies revision model operation
      sourceMeaning where
  elaboration := exactSelection operation
  evidenceElaboration :=
    (exactSelection operation).toRepresentation
  evidenceElaborationMap := rfl
  realization := GSLTILLayeredCrown.realize model operation.decoded
  admission := admitProgram dependencies revision model
    operation.decoded.program sourceMeaning
  admittedRouteAgreement :=
    decoded_refinement_uses_compiled_route model operation.decoded
      sourceMeaning

/-- Activation requires current dependency evidence and then exposes only the
retained direct map. -/
def SelectedAdmittedOperation.activate
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {model : PrimeModel} {operation : RecognizedOperation}
    {sourceMeaning : StateAt model operation.decoded.source → Prop}
    (selected : SelectedAdmittedOperation dependencies revision model
      operation sourceMeaning)
    (current : dependencies.SameDependencies revision currentRevision) :
    selected.admission.Active currentRevision :=
  selected.admission.activate current

/-- Current execution is exactly the operational route selected by the
independent decoder. -/
theorem active_run_uses_selected_route
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {model : PrimeModel} {operation : RecognizedOperation}
    {sourceMeaning : StateAt model operation.decoded.source → Prop}
    (selected : SelectedAdmittedOperation dependencies revision model
      operation sourceMeaning)
    (current : dependencies.SameDependencies revision currentRevision) :
    (selected.activate current).run =
      transportTerm (diagram model)
        (CurrentExecution.actionOfDecoded operation.decoded).operationalRoute :=
  selected.admittedRouteAgreement

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.LanguageOperationFactorization.CurrentCanary

/-- A constructor-name-independent discriminator for the application spine
retained by contextual quotation. -/
private def binaryLeftDepth : Pattern → Nat
  | .apply _ [function, _] => binaryLeftDepth function + 1
  | _ => 0

private def occurrenceTermDepth : Pattern → Nat
  | .apply _ [term] => binaryLeftDepth term
  | _ => 0

/-- Distinct authored spellings remain distinct GSLT-IL declaration
occurrences. -/
theorem identity_spelling_occurrences_distinct :
    (operationRoute canonicalIdentityOperation).occurrence ≠
      (operationRoute expandedIdentityOperation).occurrence := by
  intro same
  have canonicalDepth :
      occurrenceTermDepth
          (operationRoute canonicalIdentityOperation).occurrence = 1 := by
    rfl
  have expandedDepth :
      occurrenceTermDepth
          (operationRoute expandedIdentityOperation).occurrence = 5 := by
    rfl
  have sameDepth := congrArg occurrenceTermDepth same
  rw [canonicalDepth, expandedDepth] at sameDepth
  contradiction

/-- The same two spellings select the same decoded operational action.  The
semantic quotient therefore coexists with, rather than erases, occurrence
identity. -/
theorem identity_spelling_actions_agree :
    CurrentExecution.actionOfRecognized canonicalIdentityOperation =
      CurrentExecution.actionOfRecognized expandedIdentityOperation :=
  CurrentExecution.action_respects _ _ rfl

/-- A term rejected by the independent operation decoder cannot acquire a
typed elaboration profile by assertion. -/
theorem route_type_has_no_recognized_operation :
    ¬ ∃ operation : RecognizedOperation,
      operation.term = .const routeTypeName := by
  rintro ⟨operation, sameTerm⟩
  have normalized :=
    LanguageOperationFactorization.Signature.normalize_of_decode
      currentOperationSignature operation.term operation.decoded
      operation.recognized
  rw [sameTerm, routeType_is_not_normalized] at normalized
  contradiction

/-- Naturally ambiguous raw authored commands still have multiple worlds;
the Prime exact profile does not globalize its selection discipline. -/
theorem raw_ambiguity_remains :
    ∃ program : Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.Program,
      ¬ Nonempty (ExactSelection (Profile.raw program)) :=
  exists_program_without_global_exact_selection

/-- Relevant revision change still prevents activation of the selected
realization. -/
theorem relevant_revision_change_prevents_activation :
    ¬ ∃ currentRevision,
      Mettapedia.Languages.MeTTa.Prime.LanguageOperationNIKAdmission.Canary.dependencies.SameDependencies
        (false, false) currentRevision ∧
      Mettapedia.Languages.MeTTa.Prime.LanguageOperationNIKAdmission.Canary.dependencies.SameDependencies
        (true, false) currentRevision := by
  rintro ⟨currentRevision, first, second⟩
  exact
    Mettapedia.Languages.MeTTa.Prime.LanguageOperationNIKAdmission.Canary.relevant_change_has_no_alignment
      ⟨currentRevision, first, second⟩

end Canary

#print axioms typed_world_fibre_contractible
#print axioms typed_evidence_profile_represented
#print axioms selected_term_wellTyped
#print axioms active_run_uses_selected_route
#print axioms Canary.identity_spelling_occurrences_distinct
#print axioms Canary.identity_spelling_actions_agree
#print axioms Canary.route_type_has_no_recognized_operation
#print axioms Canary.raw_ambiguity_remains
#print axioms Canary.relevant_revision_change_prevents_activation

end Mettapedia.Languages.MeTTa.Prime.GSLTILTypedOperationAdmission
