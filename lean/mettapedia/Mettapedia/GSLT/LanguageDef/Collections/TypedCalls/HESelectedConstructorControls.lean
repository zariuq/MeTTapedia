import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedConstructorSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownBuildCounterexample

/-!
# Valid open constructors, annotations and completed-value marks

Successful constructor applicability is independent of unrelated typings
attached to the entire expression. A later requested type gate has its own
reader and can reject; neither a held mark nor a diagnostic type list erases
that distinction. All controls use existing source semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedConstructorControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type
open HESelectedConstructorSource

def annotatedSource (type_ : Atom) : Space := Space.ofList
  [HEShownBuildCounterexample.declaration (.symbol "OpenShownBox") HEShownBuildCounterexample.signature,
   HEShownBuildCounterexample.declaration HEShownBuildCounterexample.goodBuilt type_,
   HEShownBuildCounterexample.declaration (.symbol "shown-open-body")
     (CompletedDelivery.arrowType [] HEShownBuildCounterexample.range),
   HEShownBuildCounterexample.equation HEShownBuildCounterexample.call HEShownBuildCounterexample.goodBuilt]

theorem unrelated_expression_annotation_does_not_invalidate_constructor :
    (checkIfFunctionTypeIsApplicable HEShownBuildCounterexample.goodBuilt HEShownBuildCounterexample.signature
      HEShownBuildCounterexample.range (annotatedSource (.symbol "UnrelatedRange")) Bindings.empty 64).isRight = true ∧
    (evalAtom (annotatedSource (.symbol "UnrelatedRange")) GroundedDispatch.none HEShownBuildCounterexample.call
      Atom.undefinedType Bindings.empty 128).map Prod.fst = [HEShownBuildCounterexample.goodBuilt] := by decide +kernel

theorem same_range_annotation_does_not_duplicate_the_constructor_answer :
    (evalAtom (annotatedSource HEShownBuildCounterexample.range) GroundedDispatch.none HEShownBuildCounterexample.call
      Atom.undefinedType Bindings.empty 128).map Prod.fst = [HEShownBuildCounterexample.goodBuilt] := by decide +kernel

theorem expression_annotation_does_not_create_a_defining_equation (type_ : Atom) :
    HEConstructorAdmission.headAbsent (annotatedSource type_) "OpenShownBox" = true := by
  simp [HEConstructorAdmission.headAbsent, HEConstructorAdmission.rowAvoidsHead, annotatedSource,
    HEShownBuildCounterexample.declaration, HEShownBuildCounterexample.equation,
    HEShownBuildCounterexample.call, Space.ofList]

def heldChild : Entry.Value := .expression .held [.symbol "Inner", .var "saved"]
def original : Atom := .expression [.symbol "Outer", .expression [.symbol "compute"]]

theorem publication_retains_annotated_children :
    (published Policy.ready original "Outer" [heldChild] Frame.empty).1 =
      .expression .held [.symbol "Outer", heldChild] ∧
    (published Policy.unmarked original "Outer" [heldChild] Frame.empty).1 =
      .expression .active [.symbol "Outer", heldChild] := by
  constructor
  · simpa only [List.map_cons, List.map_nil, Frame.read_empty] using
      published_successes Policy.ready rfl original "Outer" [heldChild] Frame.empty (by decide)
  · simpa only [List.map_cons, List.map_nil, Frame.read_empty] using
      published_unmarked Policy.unmarked rfl original "Outer" [heldChild] Frame.empty (by decide)

theorem unchanged_policy_does_not_mark_changed_constructor_input :
    (published Policy.unchangedReady original "Outer" [heldChild] Frame.empty).1 =
      .expression .active [.symbol "Outer", heldChild] := by
  have marked := published_unchanged Policy.unchangedReady rfl original "Outer" [heldChild] Frame.empty (by decide)
  simpa [Frame.read_empty, assembled_erase, original, heldChild, Entry.Value.erase] using marked

theorem same_erasure_does_not_identify_readiness :
    (published Policy.ready original "Outer" [heldChild] Frame.empty).1.erase =
      (published Policy.unmarked original "Outer" [heldChild] Frame.empty).1.erase ∧
    (published Policy.ready original "Outer" [heldChild] Frame.empty).1 ≠
      (published Policy.unmarked original "Outer" [heldChild] Frame.empty).1 := by
  rw [publication_retains_annotated_children.1, publication_retains_annotated_children.2]
  constructor
  · simp only [Entry.Value.erase]
  · intro equal
    have statuses := congrArg Entry.Value.status equal
    cases statuses

def readyValue : Entry.Value := .expression .held [.symbol "ReadyBox", .grounded (.int 7)]
def expected : Atom := .symbol "ReturnRange"
def unrelated : Atom := .symbol "OtherRange"
def unrelatedSpace : Space := Space.ofList
  [HEShownBuildCounterexample.declaration readyValue.erase unrelated]
def returnError : Atom := mkError readyValue.erase (.badType expected unrelated)

theorem marked_does_not_mean_unchecked : ¬CompletedNativeKeepRel readyValue.erase expected := by
  rintro (stopped | undefined | atom | ⟨metaType, category, passthrough⟩)
  · simp [readyValue, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty] at stopped
  · simp [expected, Atom.undefinedType] at undefined
  · simp [expected, Atom.atomType] at atom
  · simp only [readyValue, Entry.Value.erase, List.map_cons, List.map_nil] at category
    cases category
    simp [expected, Atom.expressionType, Atom.variableType] at passthrough

/-- An independently requested return-type gate can reject the ready value,
without recursively evaluating its fields or resetting the caller frame. -/
theorem marked_value_still_checks_requested_range :
    NativeCompletedReturnRel unrelatedSpace (rawTypeLookupRel unrelatedSpace) Policy.unmarked
      readyValue expected Frame.empty [(Entry.Value.ofAtom returnError, Frame.empty)] := by
  have queried : rawTypeLookupRel unrelatedSpace Frame.empty.bindings readyValue.erase expected [unrelated] := by
    change StorageTypesRel unrelatedSpace readyValue.erase [unrelated]
    simpa only [show getAtomTypes unrelatedSpace readyValue.erase = [unrelated] from by cbv] using
      FirstSuccessSourceReplies.source_types unrelatedSpace readyValue.erase
  have rejected : ∀ actual ∈ [unrelated], ∀ output,
      ¬Policy.unmarked.matching.Rel expected actual Frame.empty.bindings output := by
    intro actual member output matched
    cases List.mem_singleton.mp member
    have fits := (FirstSuccessSourceApplicability.closed_type_match_iff expected unrelated
      Frame.empty.bindings output rfl rfl).mp matched
    simp [FirstSuccessSourceApplicability.ClosedTypeFits, expected, unrelated, Atom.undefinedType, Atom.atomType] at fits
  have cast : TypeCastBatchRel unrelatedSpace readyValue.erase expected Frame.empty.bindings
      [(returnError, Frame.empty.bindings)] (lookup := rawTypeLookupRel unrelatedSpace)
      (matching := Policy.unmarked.matching.Rel) :=
    .failure queried rejected
  apply NativeCompletedReturnRel.cast marked_does_not_mean_unchecked cast
  refine .cons ⟨by simp [rawResult], .same _, ?_⟩ .nil
  change Entry.Value.ofAtom returnError =
    if returnError == readyValue.erase then readyValue else Entry.Value.ofAtom returnError
  rw [show (returnError == readyValue.erase) = false by cbv]
  rfl

def duplicateSpace : Space := Space.ofList
  [HEShownBuildCounterexample.declaration readyValue.erase expected,
   HEShownBuildCounterexample.declaration readyValue.erase expected]

theorem duplicate_typings_do_not_duplicate_completed_cast :
    NativeCompletedReturnRel duplicateSpace (rawTypeLookupRel duplicateSpace) Policy.unmarked
      readyValue expected Frame.empty [(readyValue, Frame.empty)] := by
  apply completed_at_closed_range duplicateSpace (rawTypeLookupRel duplicateSpace) Policy.unmarked
    readyValue expected Frame.empty [] [expected] rfl
  · change StorageTypesRel duplicateSpace readyValue.erase [expected, expected]
    simpa only [show getAtomTypes duplicateSpace readyValue.erase = [expected, expected] from by cbv] using
      FirstSuccessSourceReplies.source_types duplicateSpace readyValue.erase
  · simp

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedConstructorControls
