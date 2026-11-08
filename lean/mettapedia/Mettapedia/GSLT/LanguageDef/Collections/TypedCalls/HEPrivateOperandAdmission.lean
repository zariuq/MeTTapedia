import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateOperandQueries
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEExpectedPrivateTypePublication

/-!
# Actual inferred applicability of the private-formal control

The second raw formal remains a variable after the first check assigns its
class to Expression. Its argument is still queried through the completed
current inference service; no substituted metatype cut replaces that read.
The active completion-number body is present in source but is not executed
by these static checks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateOperandAdmission

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Spec.Bindings.ScopeObservation
open HEPrivateOperandQueries (space firstOperand activeOperand)
open private scoped_type_class_fresh
  from Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

def operand (firstActive : Bool) : Atom := if firstActive then activeOperand else firstOperand
def call (firstActive : Bool) : Atom := .expression [.symbol "CompletionCoupled", operand firstActive, activeOperand]

def signature (name : String) : SelectedTypePolicy :=
  ⟨HEPrivateOperandQueries.signature name, [.var name, .var name], .symbol "CompletionResult", rfl⟩

theorem operand_lookup (firstActive : Bool) (scope : List String) (before : Frame) (expected : Atom) :
    HEDemandedCurrentReads.lookup scope space before.bindings (operand firstActive) expected [Atom.expressionType] := by
  cases firstActive
  · exact HEPrivateOperandQueries.first_lookup scope before expected
  · exact HEPrivateOperandQueries.active_lookup scope before expected

theorem selected_class (caller selected : Frame) (name : String)
    (fresh : name ∉ specBindingVars caller.bindings)
    (bindings : selected.bindings = HEFreshRangeFrame.extend caller.bindings name Atom.expressionType) :
    selected.bindings.classValues name = [Atom.expressionType] := by
  obtain ⟨assigned, isolated⟩ := HEFreshRangeAlias.extended_private_facts caller.bindings name Atom.expressionType fresh
  rw [bindings]
  simp only [Bindings.classValues, scoped_type_class_fresh isolated, List.filterMap_cons, assigned,
    List.filterMap_nil]

theorem selection (policy : Policy) (caller : Frame) (live : List Atom) (scope : List String)
    (firstActive : Bool) :
    ∃ name selected,
      kindArgumentService.selection space HEDemandedCurrentReads.lookup policy live scope (call firstActive)
        (.symbol "CompletionCoupled") (.symbol "CompletionResult") caller (.selected (signature name) [selected]) ∧
      Frame.TypeRenewRel policy (.var name) Atom.expressionType caller selected ∧
      selected.bindings = HEFreshRangeFrame.extend caller.bindings name Atom.expressionType ∧
      selected.environment = (name, .symbol "Expression") :: caller.environment ∧
      selected.bindings.classValues name = [Atom.expressionType] ∧
      name ∉ specBindingVars caller.bindings ∧
      name ∉ invocationTypeScope scope live (call firstActive) (.symbol "CompletionResult") caller.bindings := by
  let names := invocationTypeScope scope live (call firstActive) (.symbol "CompletionResult") caller.bindings
  obtain ⟨name, head, fresh⟩ := HEPrivateOperandQueries.head_lookup names caller Atom.undefinedType
  have callerFresh : name ∉ specBindingVars caller.bindings := by
    intro present
    exact fresh (by simp [invocationTypeScope, present])
  obtain ⟨selected, renewed, bindings, annotated, _, _⟩ :=
    HEExpectedPrivateTypePublication.fresh_formal policy caller name Atom.expressionType rfl
      (by decide) (by decide) callerFresh
  have classes := selected_class caller selected name callerFresh bindings
  have first : KindArgumentAdmissionRel space (HEDemandedCurrentReads.lookup names space) policy
      (call firstActive) (operand firstActive) (.var name) 1 caller [selected] [] := by
    apply KindArgumentAdmissionRel.inferred
    · intro kind _ cut
      cases cut
    · simpa [checkedFrames, checkedFailures] using
        (ArgumentChecksRel.cons (expression := call firstActive) (position := 1)
          (operand_lookup firstActive names caller (.var name))
          (.cons (TypeCheckRel.accepted renewed) .nil) .nil)
  have sameClass := HEAssignedRangeReturn.valued_class_match selected.bindings name Atom.expressionType []
    rfl (by decide) (by decide) classes (by simp [Spec.Match.Merge.ValuesAgree])
  have nextRenew : Frame.TypeRenewRel policy (.var name) Atom.expressionType selected selected :=
    .unchanged (selected.preserved_type_match policy sameClass)
  have second : KindArgumentAdmissionRel space (HEDemandedCurrentReads.lookup names space) policy
      (call firstActive) activeOperand (.var name) 2 selected [selected] [] := by
    apply KindArgumentAdmissionRel.inferred
    · intro kind _ cut
      cases cut
    · simpa [checkedFrames, checkedFailures] using
        (ArgumentChecksRel.cons (expression := call firstActive) (position := 2)
          (HEPrivateOperandQueries.active_lookup names selected (.var name))
          (.cons (TypeCheckRel.accepted nextRenew) .nil) .nil)
  have returned : TypeMatchRel (.symbol "CompletionResult") (.symbol "CompletionResult")
      selected.bindings selected.bindings :=
    same_symbol_type_match "CompletionResult" selected.bindings (by decide) (by decide)
  have boundaryFresh : name ∉ names := by
    intro present
    exact fresh (by simp [invocationTypeScope, present])
  refine ⟨name, selected, ?_, renewed, bindings, ?_, classes, callerFresh, boundaryFresh⟩
  · refine ⟨[(signature name).functionType], head, .selected (errors := []) ?_ (by simp)⟩
    simpa [names, signature, HEPrivateOperandQueries.signature, call, checkedFrames, checkedFailures] using
      (AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
        (expression := call firstActive) (expected := .symbol "CompletionResult") (selected := signature name)
        (before := caller) (operator := .symbol "CompletionCoupled")
        (arguments := [operand firstActive, activeOperand]) rfl
        (.cons (AdmissionFramesRel.single first) (.cons (AdmissionFramesRel.single second) .nil))
        (.cons (TypeCheckRel.accepted (.unchanged (selected.preserved_type_match policy returned))) .nil))
  · simpa only [Atom.expressionType, Entry.Value.ofAtom] using annotated

namespace Controls

/-- Both operands may be active programs. Their static admission does not
depend on executing either completion-number body. -/
theorem both_active_selected (policy : Policy) (caller : Frame) (live : List Atom) (scope : List String) :
    ∃ name selected,
      kindArgumentService.selection space HEDemandedCurrentReads.lookup policy live scope (call true)
        (.symbol "CompletionCoupled") (.symbol "CompletionResult") caller (.selected (signature name) [selected]) ∧
      selected.environment = (name, .symbol "Expression") :: caller.environment := by
  obtain ⟨name, selected, chosen, _, _, environment, _, _, _⟩ := selection policy caller live scope true
  exact ⟨name, selected, chosen, environment⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateOperandAdmission
