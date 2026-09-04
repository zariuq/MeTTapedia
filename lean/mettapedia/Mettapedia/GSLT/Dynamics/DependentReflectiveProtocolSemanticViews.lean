import Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolEquipment
import Mettapedia.GSLT.LanguageDef.GSLTILSemanticPredicateInstitution
import Mettapedia.TypeTheory.ResponseIndexedResultFamily
import Mettapedia.TypeTheory.SetFamilyTypeOverEssentialImage

/-!
# Semantic views of a response-indexed reflective protocol

One response-indexed protocol can be viewed through several independently
meaningful mathematical structures:

* its endpoint transitions form an operational GSLT;
* exact command coding is a bounded modal translation in both directions;
* its successor-indexed results form a displayed family in the set-families
  CwF;
* fibre inhabitation and completion are extensional state predicates in the
  semantic predicate institution;
* enabled events retain proof-relevant route occurrences and carry an
  independent work/span valuation.

This module proves the comparison maps between those views.  It also records
the non-collapse boundaries: semantic consequence does not manufacture
completion without premises, completion does not determine the dependent
result family or work/span, and the enabled-event route is not functional.

No language syntax, type theory, scheduler, equality discipline, or cost
semantics is selected here.  The protocol is an inhabited comparison object
for structures that a future integration may choose to combine.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolSemanticViews

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolEquipment.Comparison
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticPredicateInstitution
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.TypeTheory.ResponseIndexedResultFamily
open Mettapedia.TypeTheory.SetFamilyComprehensionMap
open Mettapedia.TypeTheory.SetFamilyTypeOverEssentialImage

/-! ## Exact code as modal operational equivalence -/

/-- Exact command encoding covers and reflects both outgoing and incoming
endpoint transitions.  The carrier map is the identity because coding changes
the material command edge rather than the protocol phase. -/
def encodingModalTranslation :
    ModalTranslation (lts query) (lts codedQuery) where
  toCoveredTranslation :=
    { mapTerm := id
      mapEquiv := fun equal => equal
      cover :=
        { mapStep := fun step => endpoint_step_iff.mpr step
          liftStep := by
            intro source target step
            exact ⟨target, endpoint_step_iff.mp step, rfl⟩ } }
  liftIncoming := by
    intro source target step
    exact ⟨target, endpoint_step_iff.mp step, rfl⟩

/-- Exact command decoding is bounded in the reverse direction. -/
def decodingModalTranslation :
    ModalTranslation (lts codedQuery) (lts query) where
  toCoveredTranslation :=
    { mapTerm := id
      mapEquiv := fun equal => equal
      cover :=
        { mapStep := fun step => endpoint_step_iff.mp step
          liftStep := by
            intro source target step
            exact ⟨target, endpoint_step_iff.mpr step, rfl⟩ } }
  liftIncoming := by
    intro source target step
    exact ⟨target, endpoint_step_iff.mpr step, rfl⟩

theorem encoding_then_decoding_modal :
    encodingModalTranslation.comp decodingModalTranslation =
      ModalTranslation.id (lts query) :=
  ModalTranslation.ext rfl

theorem decoding_then_encoding_modal :
    decodingModalTranslation.comp encodingModalTranslation =
      ModalTranslation.id (lts codedQuery) :=
  ModalTranslation.ext rfl

/-! ## Dependent fibres and extensional predicates -/

/-- The extensional predicate saying that the result fibre at a phase is
inhabited. -/
def inhabitedResult : Set Phase :=
  { phase | Nonempty (Result phase) }

/-- The coarse extensional predicate saying that interaction has completed. -/
def completedPhase : Set Phase :=
  { phase | completion phase = true }

/-- In this protocol, completion detects whether a result exists.  It does
not determine which result type exists. -/
theorem inhabitedResult_eq_completedPhase :
    inhabitedResult = completedPhase := by
  ext phase
  change Nonempty (Result phase) ↔ completion phase = true
  cases phase with
  | start =>
      constructor
      · rintro ⟨value⟩
        exact PEmpty.elim value
      · intro impossible
        exact False.elim (Bool.false_ne_true impossible)
  | unitDone =>
      exact ⟨fun _ => rfl, fun _ => ⟨PUnit.unit⟩⟩
  | boolDone =>
      exact ⟨fun _ => rfl, fun _ => ⟨false⟩⟩

/-- The predicate comparison is literally fibre inhabitation of the displayed
result type. -/
theorem resultDisplay_inhabited_iff_completed (phase : Phase) :
    Nonempty (resultDisplay.val phase) ↔ phase ∈ completedPhase := by
  change phase ∈ inhabitedResult ↔ phase ∈ completedPhase
  exact Set.ext_iff.mp inhabitedResult_eq_completedPhase phase

/-! ## Modal reachability and semantic consequence -/

/-- States that can take one operational step to a state with an inhabited
result fibre. -/
def mayReachInhabitedResult : Set Phase :=
  gsltDiamond (lts codedQuery) inhabitedResult

/-- The initial phase may reach an inhabited dependent result. -/
theorem start_mayReachInhabitedResult :
    Phase.start ∈ mayReachInhabitedResult := by
  apply (gsltDiamond_spec (lts codedQuery) inhabitedResult Phase.start).mpr
  exact ⟨Phase.unitDone, unitEvent.step, ⟨PUnit.unit⟩⟩

/-- The second response supplies a distinct target witness for the same modal
predicate. -/
theorem start_mayReachBoolResult :
    ∃ target, (lts codedQuery).Step Phase.start target ∧
      target = Phase.boolDone ∧ target ∈ inhabitedResult := by
  exact ⟨Phase.boolDone, boolEvent.step, rfl, ⟨false⟩⟩

/-- The coded transition system as a signature of the semantic predicate
institution. -/
def codedSignature :
    (ModallyCoveredTheory.{0})ᵒᵖ :=
  Opposite.op ⟨lts codedQuery⟩

/-- Fibre inhabitation semantically entails completion. -/
theorem inhabitedResult_derives_completedPhase :
    institution.Derives codedSignature {inhabitedResult} completedPhase := by
  rw [← inhabitedResult_eq_completedPhase]
  exact premise_derives_itself codedSignature inhabitedResult

/-- Completion is not a theorem of the empty semantic context: the initial
phase is a concrete countermodel. -/
theorem completedPhase_not_derivable_without_premises :
    ¬ institution.Derives codedSignature ∅ completedPhase := by
  intro derives
  have entails : Entails (∅ : Set (Set Phase)) completedPhase :=
    (derives_iff_entails codedSignature ∅ completedPhase).mp derives
  have startCompleted : Phase.start ∈ completedPhase :=
    entails Phase.start (by
      intro predicate member
      have impossible : False := (Set.mem_empty_iff_false predicate).mp member
      exact False.elim impossible)
  change false = true at startCompleted
  exact Bool.false_ne_true startCompleted

/-! ## Exact code commutes with the modal and institutional views -/

def sourceModalTheory : ModallyCoveredTheory :=
  ⟨lts query⟩

def codedModalTheory : ModallyCoveredTheory :=
  ⟨lts codedQuery⟩

def encodingModalHom : sourceModalTheory ⟶ codedModalTheory :=
  encodingModalTranslation

def decodingModalHom : codedModalTheory ⟶ sourceModalTheory :=
  decodingModalTranslation

def sourceSignature : (ModallyCoveredTheory.{0})ᵒᵖ :=
  Opposite.op sourceModalTheory

def encodingSignatureMap : codedSignature ⟶ sourceSignature :=
  encodingModalHom.op

/-- Exact command coding preserves the one-step modal predicate, not merely
the two concrete examples. -/
theorem exact_code_preserves_mayReachInhabitedResult :
    Set.preimage encodingModalTranslation.mapTerm
        (gsltDiamond (lts codedQuery) inhabitedResult) =
      gsltDiamond (lts query)
        (Set.preimage encodingModalTranslation.mapTerm inhabitedResult) :=
  Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
    encodingModalTranslation.toCoveredTranslation inhabitedResult

/-- Institution sentence transport is the same inverse-image operation as
OSLF modal change of base for this exact code map. -/
theorem exact_code_sentence_transport_agrees_oslf :
    predicateSentence.map encodingSignatureMap completedPhase =
      (oslfModalFunctor.map encodingSignatureMap).mapPred completedPhase :=
  sentence_transport_eq_oslf_pullback encodingSignatureMap completedPhase

/-- Because endpoint coding is identity on phases, it transports the
completion predicate exactly. -/
theorem exact_code_preserves_completedPhase :
    predicateSentence.map encodingSignatureMap completedPhase =
      completedPhase :=
  rfl

/-! ## Connected non-collapse boundary -/

/-- The commuting views coexist without identifying their distinct data.
The modal and institutional layers see inhabited completion; the contextual
layer retains the varying result family; the loose route retains both event
occurrences; and completion determines neither the family nor work/span. -/
theorem semantic_views_boundary :
    Phase.start ∈ mayReachInhabitedResult ∧
      institution.Derives codedSignature {inhabitedResult} completedPhase ∧
      (¬ institution.Derives codedSignature ∅ completedPhase) ∧
      (¬ (simpleToDependentTypeFunctor Phase).essImage resultDisplay) ∧
      (¬ Nonempty
        (Mettapedia.GSLT.LooseRelationEquipment.Representation
          enabledEventRoute)) ∧
      (¬ Nonempty
        (Mettapedia.TypeTheory.DependentFamilyObserverFactorization.FamilyFactorization
          completion Result)) ∧
      ¬ Mettapedia.GSLT.Core.NonFactorization.Factors
        outcomeCompletion outcomeWorkSpan :=
  ⟨start_mayReachInhabitedResult,
    inhabitedResult_derives_completedPhase,
    completedPhase_not_derivable_without_premises,
    resultDisplay_not_in_simple_essentialImage,
    enabledEventRoute_not_representable,
    result_not_completion_determined,
    outcomeWorkSpan_not_completion_determined⟩

#print axioms encodingModalTranslation
#print axioms decodingModalTranslation
#print axioms encoding_then_decoding_modal
#print axioms inhabitedResult_eq_completedPhase
#print axioms resultDisplay_inhabited_iff_completed
#print axioms start_mayReachInhabitedResult
#print axioms inhabitedResult_derives_completedPhase
#print axioms completedPhase_not_derivable_without_premises
#print axioms exact_code_preserves_mayReachInhabitedResult
#print axioms exact_code_sentence_transport_agrees_oslf
#print axioms semantic_views_boundary

end Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolSemanticViews
