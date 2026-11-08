import Mettapedia.Languages.MeTTa.HE.ArgumentAdmission
import Mettapedia.Languages.MeTTa.HE.ScalarValueCasts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeArgumentQueryTransport

/-!
# Actual inferred conditional admission, with held branch cuts

The operator read earns its fresh arrow. The comparison is actually inferred
as Bool; neither held branch is inferred. The return constraint then builds
the selected frame under the original caller, including its old aliases.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeAdmissionBoundary

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type
open Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HERangeArgumentQueryTransport (inferredRead)
open HERangeSourceProgram (space)

def lookup (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) : CastLookup := fun scope _ => inferredRead currentOps world scope

def environment (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView) :
    WorldEnvironment Space Unit :=
  { HERangeSourceProgram.environment minimal with
    lookup := lookup currentOps world
    arguments := kindArgumentService }

theorem number_query (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (value : Int) (expected : Atom) :
    inferredRead currentOps world scope before.bindings (.grounded (.int value)) expected [.symbol "Number"] := by
  let supply : TypeReadSupply.Supply :=
    ⟨invocationTypeScope scope [] (.grounded (.int value)) expected before.bindings, 0⟩
  exact ⟨supply, 1, fun _ member => member,
    congrArg Prod.fst (HERangeTypeReadPrimitives.number_read currentOps HERangeTypeReadPrimitives.source world 0 value supply)⟩

theorem boolean_query (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (world : ExternalView) (scope : List String) (before : Frame) (value : Bool) (expected : Atom) :
    inferredRead currentOps world scope before.bindings (.grounded (.bool value)) expected [.symbol "Bool"] := by
  let supply : TypeReadSupply.Supply :=
    ⟨invocationTypeScope scope [] (.grounded (.bool value)) expected before.bindings, 0⟩
  exact ⟨supply, 1, fun _ member => member,
    congrArg Prod.fst (HERangeTypeReadPrimitives.boolean_read currentOps HERangeTypeReadPrimitives.source world 0 value supply)⟩

theorem number_source (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (policy : Policy) (live : List Atom) (scope : List String) (before : Frame) (value : Int) :
    Stateful.AtomRel (environment minimal currentOps world) space () live scope
      (.grounded (.int value)) (.symbol "Number") before [(.grounded (.int value), before)] () (policy := policy) :=
  Stateful.scalar_from_query _ policy space () live scope before (.int value) "Number"
    (by decide) (by decide) (by decide) (number_query currentOps world _ before value _)

theorem boolean_source (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (policy : Policy) (live : List Atom) (scope : List String) (before : Frame) (value : Bool) :
    Stateful.AtomRel (environment minimal currentOps world) space () live scope
      (.grounded (.bool value)) (.symbol "Bool") before [(.grounded (.bool value), before)] () (policy := policy) :=
  Stateful.scalar_from_query _ policy space () live scope before (.bool value) "Bool"
    (by decide) (by decide) (by decide) (boolean_query currentOps world _ before value _)

theorem conditional_arguments (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (scope : List String) (lower upper : Int) (yes no : Atom) :
    AdmissionArgumentsRel HEArgumentMetatypeRole.Admission space
      (inferredRead (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world scope)
      policy (HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no) 1
      [HEIfSourceSelection.Range.condition lower upper, yes, no]
      [.symbol "Bool", Atom.atomType, Atom.atomType] [before] [before] [] := by
  have condition := HERangeArgumentQueryTransport.comparison_admission world active primitive unobservedClosure
    policy before scope (HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no) 1 lower upper
  have first := HERangeArgumentQueryTransport.held_branch_cut policy before
    (HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no) yes 2
    (inferredRead (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world scope)
  have second := HERangeArgumentQueryTransport.held_branch_cut policy before
    (HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no) no 3
    (inferredRead (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world scope)
  exact .cons (AdmissionFramesRel.single condition)
    (.cons (AdmissionFramesRel.single first) (.cons (AdmissionFramesRel.single second) .nil))

theorem conditional_selection (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (yes no expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ (name : String) (after : Frame),
      (ArgumentService.role HEArgumentMetatypeRole.Admission).selection space
        (lookup (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world)
        policy live scope (HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no)
        (.symbol "if") expected before (.selected (HEIfSourceSelection.signature name) [after]) ∧
      Frame.TypeRenewRel policy expected (.var name) before after ∧
      name ∉ specBindingVars before.bindings := by
  let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
  let expression := HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no
  let names := invocationTypeScope scope live expression expected before.bindings
  obtain ⟨name, queried, fresh⟩ := HERangeArgumentQueryTransport.if_read currentOps world names before Atom.undefinedType
  have callerFresh : name ∉ specBindingVars before.bindings := by
    intro present
    exact fresh (by simp [invocationTypeScope, present])
  obtain ⟨after, renewed⟩ : ∃ after : Frame, Frame.TypeRenewRel policy expected (.var name) before after := by
    rcases demand with rfl | rfl
    · obtain ⟨after, _, renewed, _⟩ := HEFreshRangeFrame.number_range_frame policy before name callerFresh
      exact ⟨after, renewed⟩
    · exact ⟨before, .unchanged (before.preserved_type_match policy (.undefinedLeft _ _))⟩
  refine ⟨name, after, ⟨[(HEIfSourceSelection.signature name).functionType], queried, ?_⟩, renewed, callerFresh⟩
  apply AdmissionScanRel.selected (errors := []) (frames := [after]) ?_ (by simp)
  have args := conditional_arguments world active primitive unobservedClosure policy before names lower upper yes no
  simpa [HEIfSourceSelection.signature, checkedFrames, checkedFailures, lookup, names, expression] using
    AdmissionApplicationRel.checked (admit := HEArgumentMetatypeRole.Admission)
      (expression := expression) (expected := expected) (selected := HEIfSourceSelection.signature name)
      (before := before) (operator := .symbol "if")
      (arguments := [HEIfSourceSelection.Range.condition lower upper, yes, no]) rfl args
      (List.Forall₂.cons (TypeCheckRel.accepted renewed) List.Forall₂.nil)

/-- The earned applicability packet enters the existing continuation
machine. Both branches remain source values; neither has been evaluated or
inferred, and the caller's saved stack is retained beneath publication. -/
theorem conditional_step (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (yes no expected : Atom)
    (yesClosed : Spec.Type.Presentation.TypeSubst.typeVars yes = [])
    (noClosed : Spec.Type.Presentation.TypeSubst.typeVars no = [])
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType)
    (stack : List RecursiveTasks.Contextual.Continuation) :
    ∃ (name : String) (after : Frame),
      RecursiveMachine.Contextual.LocalStep space HERangeSourceProgram.dispatch
        (lookup (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world) policy
        (.work (.atom live scope
          (Entry.Value.ofAtom (HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no))
          expected before), stack)
        (.work (.invocations live scope expected (HEIfSourceSelection.signature name) (.symbol "if")
          [Entry.Value.ofAtom (HEIfSourceSelection.Range.condition lower upper), Entry.Value.ofAtom yes, Entry.Value.ofAtom no]
          [after]), .publish (HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no) :: stack)
        (admission := kindArgumentService) ∧ Frame.TypeRenewRel policy expected (.var name) before after := by
  let expression := HEIfSourceSelection.call (HEIfSourceSelection.Range.condition lower upper) yes no
  have read : before.read policy (Entry.Value.ofAtom expression) = Entry.Value.ofAtom expression := by
    apply HEFreshSyntaxBinding.ground_substitution
    simp [expression, Entry.Value.erase_ofAtom, HEIfSourceSelection.call,
      HEIfSourceSelection.Range.condition, HEFreshEquationFrames.Range.number,
      Spec.Type.Presentation.TypeSubst.typeVars, Spec.Type.Presentation.TypeSubst.typeVarsList, yesClosed, noClosed]
  obtain ⟨name, after, selected, renewed, _⟩ := conditional_selection world active primitive unobservedClosure
    policy before live scope lower upper yes no expected demand
  have converted : Entry.Value.ofAtom expression = .expression .active
      [.symbol "if", Entry.Value.ofAtom (HEIfSourceSelection.Range.condition lower upper),
        Entry.Value.ofAtom yes, Entry.Value.ofAtom no] := by
    simp only [expression, HEIfSourceSelection.call, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  refine ⟨name, after, ?_, renewed⟩
  have step := RecursiveMachine.Contextual.LocalStep.atomFunction
    (admission := kindArgumentService) (space := space) (dispatch := HERangeSourceProgram.dispatch)
    (lookup := lookup (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world)
    (policy := policy) (live := live) (scope := scope) (value := Entry.Value.ofAtom expression)
    (expected := expected) (activation := before) (readiness := .active) (operator := .symbol "if")
    (arguments := [Entry.Value.ofAtom (HEIfSourceSelection.Range.condition lower upper), Entry.Value.ofAtom yes, Entry.Value.ofAtom no])
    (signature := HEIfSourceSelection.signature name) (frames := [after]) (stack := stack)
    (by
      rw [read, converted]
      simp only [Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      apply Entry.Rel.expression
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · rcases demand with rfl | rfl <;> decide
      · exact Or.inr rfl)
    (by rw [read, converted])
    (by simpa only [read, Entry.Value.erase_ofAtom, Entry.Value.erase, kindArgumentService] using selected)
  simpa only [read, Entry.Value.erase_ofAtom] using step

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeAdmissionBoundary
