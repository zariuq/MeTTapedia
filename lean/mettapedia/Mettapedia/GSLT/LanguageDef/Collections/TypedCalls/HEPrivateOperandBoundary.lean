import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateOperandAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionClassPublication

/-!
# Inferred applicability and operator completion at private-formal publication

Both operand queries and both operator type instances use the same actual
occurrence-scoped inferred reader. The type-variable frame is earned by the
raw authored-formal checks. Its operator cast is an actual source run, not
an annotation-only replacement for an inferred query.

The final projection remains the named closed-class boundary. Integrating
it as a native scope-exit transition of the primary source/worker requires
the separate operational stack invariant.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateOperandBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEPrivateOperandQueries (space)
open HEPrivateOperandAdmission (call signature)
open HEClosedAliasRetirement

theorem selected_operator {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = HEDemandedCurrentReads.lookup)
    (label : Context) (world : World) (view : environment.view world label = space)
    (policy : Policy) (caller : Frame) (live : List Atom) (scope : List String) (firstActive : Bool) :
    ∃ (left right : String) (selected completed : Frame),
      kindArgumentService.selection space HEDemandedCurrentReads.lookup policy live scope (call firstActive)
        (.symbol "CompletionCoupled") (.symbol "CompletionResult") caller (.selected (signature left) [selected]) ∧
      Stateful.AtomRel environment label world live scope (.symbol "CompletionCoupled") (signature left).functionType
        selected [(.symbol "CompletionCoupled", completed)] world (policy := policy) ∧
      completed.bindings = (HEFreshRangeFrame.extend caller.bindings left Atom.expressionType).addEquality left right ∧
      completed.environment = (right, .symbol "Expression") :: (left, .symbol "Expression") :: caller.environment ∧
      left ∉ specBindingVars caller.bindings ∧ right ∉ specBindingVars caller.bindings ∧ right ≠ left ∧
      left ∉ scope ∧ right ∉ scope := by
  obtain ⟨left, selected, chosen, _, bindings, annotated, _, leftFresh, firstScope⟩ :=
    HEPrivateOperandAdmission.selection policy caller live scope firstActive
  let names := invocationTypeScope scope live (.symbol "CompletionCoupled") (signature left).functionType selected.bindings
  obtain ⟨right, queried, secondScope⟩ := HEPrivateOperandQueries.head_lookup names selected (signature left).functionType
  have rightSelected : right ∉ specBindingVars selected.bindings := by
    intro present
    exact secondScope (by simp [invocationTypeScope, present])
  have rightFresh : right ∉ specBindingVars caller.bindings := by
    intro present
    apply rightSelected
    rw [bindings]
    simp only [HEFreshRangeFrame.extend, specBindingVars, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
    tauto
  have different : right ≠ left := by
    intro same
    apply rightSelected
    rw [same, bindings]
    simp [HEFreshRangeFrame.extend, specBindingVars]
  have selectedRead : selected.read policy (.var left) = .symbol "Expression" := by
    simp [Frame.read, Entry.Value.substitute, annotated, Entry.Value.resolve]
  have isolated : left ∉ selected.bindings.eqVarsInOrder := by
    rw [bindings]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left Atom.expressionType leftFresh).2
  have assigned : selected.bindings.lookup left = some (.symbol "Expression") := by
    rw [bindings]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left Atom.expressionType leftFresh).1
  have actualQuery : environment.lookup names (environment.view world label) selected.bindings
      (.symbol "CompletionCoupled") (signature left).functionType [(signature right).functionType] := by
    rw [lookup, view]
    exact queried
  obtain ⟨completed, run, resultBindings, resultEnvironment⟩ := HEOperatorAliasPublication.source_operator
    environment policy label world live scope selected "CompletionCoupled" left right ["->"] ["CompletionResult"]
      (.symbol "Expression") (by decide) rfl selectedRead isolated assigned rightSelected actualQuery
  refine ⟨left, right, selected, completed, chosen, run, ?_, ?_, leftFresh, rightFresh, different, ?_, ?_⟩
  · rw [resultBindings, bindings]
  · rw [resultEnvironment, annotated]
  · intro present
    exact firstScope (by simp [invocationTypeScope, present])
  · intro present
    exact secondScope (by simp [names, invocationTypeScope, present])

def retained (outer : List String) (functionCallback returnCallback context : GroundedValue)
    (reduced result : String) (firstActive : Bool) (left : String) : List String :=
  HETypeContinuationScope.kept outer
    (HETypeContinuationScope.functionRegion functionCallback (call firstActive) (signature left).functionType
      (.symbol "CompletionResult") (.grounded context))
    (HETypeContinuationScope.continuation returnCallback reduced result (.symbol "CompletionResult") (.grounded context))

theorem private_not_retained (outer : List String) (functionCallback returnCallback context : GroundedValue)
    (reduced result : String) (firstActive : Bool) (left name : String)
    (notOuter : name ∉ outer) (notReduced : name ≠ reduced) (notResult : name ≠ result) :
    name ∉ retained outer functionCallback returnCallback context reduced result firstActive left := by
  simp only [retained, HETypeContinuationScope.kept_mem]
  simp [notOuter, HETypeContinuationScope.continuation, HETypeContinuationScope.nativeCall,
    HETypeContinuationScope.returnDemand, TypeSubst.typeVars, TypeSubst.typeVarsList,
    Atom.expressionType, notReduced, notResult]

/-- Both names are allocated outside the actual emitted instruction names
and the outer scope. The raw closed result continuation therefore retires
them, and the computed class-local record projection restores the caller.
This conclusion does not substitute the larger allocation inventory for
the computed retained set. -/
theorem private_class_boundary {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = HEDemandedCurrentReads.lookup)
    (label : Context) (world : World) (view : environment.view world label = space)
    (policy : Policy) (caller : Frame) (live : List Atom) (scope outer : List String)
    (functionCallback returnCallback : GroundedValue) (reduced result : String) (firstActive : Bool) :
    ∃ (left right : String) (selected completed : Frame),
      let keep := retained outer functionCallback returnCallback (environment.services.contextPayload label)
        reduced result firstActive left
      kindArgumentService.selection space HEDemandedCurrentReads.lookup policy live
        (reduced :: result :: (outer ++ scope)) (call firstActive) (.symbol "CompletionCoupled")
        (.symbol "CompletionResult") caller (.selected (signature left) [selected]) ∧
      Stateful.AtomRel environment label world live (reduced :: result :: (outer ++ scope))
        (.symbol "CompletionCoupled") (signature left).functionType selected
        [(.symbol "CompletionCoupled", completed)] world (policy := policy) ∧
      projectBindings keep left right completed.bindings = some caller.bindings ∧
      projectEnvironment keep left right completed.environment = caller.environment ∧
      expose keep left right completed (.var left) = .symbol "Expression" ∧
      expose keep left right completed (.var right) = .symbol "Expression" ∧
      left ≠ right := by
  obtain ⟨left, right, selected, completed, chosen, run, bindings, annotated,
      leftFresh, rightFresh, different, leftScope, rightScope⟩ := selected_operator environment lookup label world view
    policy caller live (reduced :: result :: (outer ++ scope)) firstActive
  have absent (name : String) (outside : name ∉ reduced :: result :: (outer ++ scope)) :
      name ∉ retained outer functionCallback returnCallback (environment.services.contextPayload label)
        reduced result firstActive left := by
    simp only [List.mem_cons, List.mem_append, not_or] at outside
    exact private_not_retained outer functionCallback returnCallback _ reduced result firstActive left name
      outside.2.2.1 outside.1 outside.2.1
  let keep := retained outer functionCallback returnCallback (environment.services.contextPayload label)
    reduced result firstActive left
  have leftGone : left ∉ keep := absent left leftScope
  have rightGone : right ∉ keep := absent right rightScope
  have raw := project_fresh_class keep caller.bindings left right Atom.expressionType leftFresh rightFresh
  have marked := project_fresh_environment keep caller left right (.symbol "Expression") leftFresh rightFresh
  obtain ⟨leftRead, rightRead⟩ := class_read completed left right (.symbol "Expression") caller.environment
    (Ne.symm different) annotated Policy.ready
  refine ⟨left, right, selected, completed, chosen, run, ?_, ?_, ?_, ?_, Ne.symm different⟩
  · rw [bindings]
    simpa only [if_neg leftGone, if_neg rightGone] using raw
  · rw [annotated]
    simpa only [if_neg leftGone, if_neg rightGone, List.nil_append] using marked
  · rw [expose_removed_left keep left right completed leftGone, leftRead]
  · rw [expose_removed_right keep left right completed rightGone, rightRead]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateOperandBoundary
