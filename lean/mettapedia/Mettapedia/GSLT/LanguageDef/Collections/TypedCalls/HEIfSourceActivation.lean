import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfOperatorSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments

/-!
# Source-derived conditional activation for the authored range body

The selected range frame, the independently fresh operator cast, and actual
comparison/held-branch delivery are composed in the existing FunctionRel.
The endpoint is the reached ordinary conditional call, before its equation
body executes. No result of range recursion is supplied at this boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceActivation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEIfSourceSelection (signature)
open HEIfSourceSelection.Range (space condition yes no)
open HEBinaryNumericSource (primitiveEnvironment)
open HEFreshEquationFrames.Range (number bodyAt)

def operands (lower upper : Int) : List Entry.Value :=
  [Entry.Value.ofAtom (condition lower upper), Entry.Value.ofAtom yes, Entry.Value.ofAtom (no lower upper)]

def reachedCall (lower upper : Int) : Entry.Value :=
  .expression .active [.symbol "if", .grounded (.bool (decide (lower ≥ upper))),
    Entry.Value.ofAtom yes, Entry.Value.ofAtom (no lower upper)]

theorem selected_name_fresh (policy : Policy) (before selected : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (name : String)
    (selection : InvocationSelectionRel space scopedLookup policy live scope
      (bodyAt (number lower) (number upper)) (.symbol "if") (.symbol "Number") before
      (.selected (signature name) [selected])) : name ∉ specBindingVars before.bindings := by
  have fresh := InvocationSelectionRel.selected_fresh (enumeration := TypeEnumeration.storage) selection
  intro member
  exact fresh.2.2 name (by simp [signature, TypeSubst.typeVars])
    (by simp [invocationTypeScope, member])

theorem source_activation (services : Minimal.Services) (policy : Policy)
    (before : Frame) (live : List Atom) (scope : List String) (lower upper : Int) :
    ∃ left right selected after,
      InvocationSelectionRel space scopedLookup policy live scope (bodyAt (number lower) (number upper))
        (.symbol "if") (.symbol "Number") before (.selected (signature left) [selected]) ∧
      Stateful.FunctionRel (primitiveEnvironment services) space ()
        (invocationReturnType (signature left) :: live) scope (.symbol "Number") (signature left)
        (.symbol "if") (operands lower upper) selected [(reachedCall lower upper, after)] () (policy := policy) ∧
      selected.bindings = HEFreshRangeFrame.extend before.bindings left (.symbol "Number") ∧
      after.bindings = selected.bindings.addEquality left right ∧
      ∀ readingPolicy,
        after.read readingPolicy (.var left) = .symbol "Number" ∧
        after.read readingPolicy (.var right) = .symbol "Number" := by
  obtain ⟨left, selected, selection, selectedBindings, selectedRead⟩ :=
    HEIfSourceSelection.Range.source_selection policy before live scope lower upper
  have leftFresh := selected_name_fresh policy before selected live scope lower upper left selection
  have facts := HEFreshRangeAlias.extended_private_facts before.bindings left (.symbol "Number") leftFresh
  rw [← selectedBindings] at facts
  let headLive := (signature left).functionType ::
    (operands lower upper).map Entry.Value.erase ++ invocationReturnType (signature left) :: live
  let headScope := scope ++ expectedApplicationScope
    (.expression ((Entry.Value.symbol "if" :: operands lower upper).map Entry.Value.erase)) (.symbol "Number")
  let avoid := HEIfOperatorSource.castScope headScope headLive selected left
  let right := instanceName avoid ["t"] 0 "t"
  obtain ⟨after, headRun, afterBindings, afterRead⟩ :=
    HEIfOperatorSource.source (primitiveEnvironment services) rfl policy space () headLive headScope
      selected left right HEIfSourceSelection.Range.if_declared facts.2 facts.1
      (instanceName_not_mem avoid ["t"] 0 "t")
  have args := HEHeldSourceArguments.Range.arguments services policy after
    ((Entry.Value.symbol "if").erase :: invocationReturnType (signature left) :: live) scope lower upper
  have branches : Stateful.FunctionBranchesRel (primitiveEnvironment services) space ()
      (invocationReturnType (signature left) :: live) scope
      ((operands lower upper).zip (signature left).argumentTypes)
      [(.symbol "if", after)] [(reachedCall lower upper, after)] () (policy := policy) := by
    simpa [operands, signature, functionAssemble, reachedCall] using
      (Stateful.FunctionBranchesRel.continuing (head := (Entry.Value.symbol "if", after))
        (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) args
        Stateful.FunctionBranchesRel.nil)
  have source : Stateful.FunctionRel (primitiveEnvironment services) space ()
      (invocationReturnType (signature left) :: live) scope (.symbol "Number") (signature left)
      (.symbol "if") (operands lower upper) selected [(reachedCall lower upper, after)] () (policy := policy) :=
    .evaluated rfl headRun branches
  exact ⟨left, right, selected, after, selection, source, selectedBindings, afterBindings, afterRead⟩

/-- The derived activation runs in the existing contextual worker with
the caller's saved stack and emitted prefix unchanged. -/
theorem retained_activation (services : Minimal.Services) (policy : Policy)
    (before : Frame) (live : List Atom) (scope : List String) (lower upper : Int)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ left right selected after,
      InvocationSelectionRel space scopedLookup policy live scope (bodyAt (number lower) (number upper))
        (.symbol "if") (.symbol "Number") before (.selected (signature left) [selected]) ∧
      RecursiveMachine.Contextual.WorldSteps
        (primitiveEnvironment services).view (primitiveEnvironment services).services
        (primitiveEnvironment services).dispatch (primitiveEnvironment services).lookup policy
        ⟨(), space, .work (.function (invocationReturnType (signature left) :: live) scope (.symbol "Number")
          (signature left) (.symbol "if") (operands lower upper) selected), stack, emitted⟩
        ⟨(), space, .returning [(reachedCall lower upper, after)], stack, emitted⟩ ∧
      after.bindings = selected.bindings.addEquality left right ∧
      ∀ readingPolicy, after.read readingPolicy (.var left) = .symbol "Number" ∧
        after.read readingPolicy (.var right) = .symbol "Number" := by
  obtain ⟨left, right, selected, after, selection, source, _, bound, read⟩ :=
    source_activation services policy before live scope lower upper
  refine ⟨left, right, selected, after, selection, ?_, bound, read⟩
  exact RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.task_complete
      (task := .function (invocationReturnType (signature left) :: live) scope (.symbol "Number")
        (signature left) (.symbol "if") (operands lower upper) selected) source stack) emitted

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceActivation
