import Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatch

/-!
# Native effects, duplicate answers and two retained caller levels

The local host contract advances one selected context's counter. Its two
successful producer rows are equal values, not one collapsed answer. The
control starts at the reached call after argument production; it does not
claim the entire argument-producing source program has run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open RetainedNativeDispatch

abbrev Store := Bool → Nat
def number (n : Nat) : Entry.Value := .grounded (.int n)
def call : Entry.Value := .expression .active [.symbol "touch", .grounded (.int 7)]
def activation : Completed.Frame := Completed.Controls.argumentAliasFrame
def advance (world : Store) (label : Bool) : Store := Function.update world label (world label + 1)
def rows (world : Store) (label : Bool) : List Result :=
  [(number (world label), activation), (number (world label), activation)]
def errorRows : List Result := [(Entry.Value.ofAtom (Atom.error call.erase (.symbol "boom")), activation)]
def outcome (fails : Bool) (world : Store) (label : Bool) : GroundedResult Entry.Value :=
  if fails then .runtimeError "boom" else .ok
    [(number (world label), Bindings.empty), (number (world label), Bindings.empty)]
def plan (fails : Bool) (world : Store) (label : Bool) : NativeReplyPlan :=
  if fails then .done errorRows else .resume (rows world label)

def dispatch : Spec.Eval.GroundedDispatch where
  executable operator := operator = .symbol "touch"
  outcome := fun _ _ _ => False
  valueProvenance := fun _ _ => .completed
  bindingMode := fun _ _ => .raw

def services (fails : Bool) : WorldServices Bool Store where
  contextPayload label := .bool label
  nativeCall := fun _ _ _ _ _ _ _ _ => False
  groundedCall label world value result after :=
    value = call ∧ result = outcome fails world label ∧ after = advance world label

def environment (fails : Bool) : WorldEnvironment Bool Store where
  view world label := Space.ofList [.expression [.symbol "counter", .grounded (.int (world label))]]
  services := services fails
  dispatch := dispatch
  lookup := Completed.scopedLookup

theorem produced (fails : Bool) (world : Store) (label : Bool) :
    (environment fails).services.groundedAt label world [] [] activation call (outcome fails world label) (advance world label) := by
  exact ⟨rfl, rfl, rfl⟩

theorem prepared (fails : Bool) (world : Store) (label : Bool) :
    NativeOutcomeRel Policy.unmarked dispatch (.symbol "touch") [.grounded (.int 7)] call
      (some Atom.atomType) activation (outcome fails world label) (plan fails world label) := by
  cases fails with
  | true => exact .runtimeError "boom"
  | false =>
    have paired : NativeRowsRel Policy.unmarked dispatch (.symbol "touch") [.grounded (.int 7)] activation
        [(number (world label), Bindings.empty), (number (world label), Bindings.empty)] (rows world label) := by
      simpa [nativeValue, dispatch, rows] using
        (NativeRowsRel.cons (head := (number (world label), Bindings.empty))
          (Frame.NativeRenewRel.empty Policy.unmarked activation)
          (NativeRowsRel.cons (head := (number (world label), Bindings.empty))
            (Frame.NativeRenewRel.empty Policy.unmarked activation) .nil))
    exact .success paired

theorem completed_rows (world : Store) (label : Bool) :
    Stateful.BoundaryBatchRel (environment false) label (advance world label) [] [] none
      (.native call (some Atom.atomType) .completed) (rows world label) (rows world label) (advance world label)
      (policy := Policy.unmarked) := by
  have child : Stateful.BoundaryRel (environment false) label (advance world label) [] [] none
      (.native call (some Atom.atomType) .completed) (number (world label)) activation
      [(number (world label), activation)] (advance world label) (policy := Policy.unmarked) :=
    .nativeCompletedReturn (.keep (Or.inr (Or.inr (Or.inl rfl))))
  simpa only [rows, List.cons_append, List.nil_append] using
    Stateful.BoundaryBatchRel.cons (head := (number (world label), activation)) child
      (.cons (head := (number (world label), activation)) child .nil)

def world : Store := fun label => if label then 40 else 5
def inner : List Continuation := [.tupleTail (.symbol "inside")]
def outerRows : List Result := [(.symbol "outer", Completed.Frame.empty)]
def stack : List Continuation := [.prepend outerRows]
def emitted : List Result := [(.symbol "already", Completed.Frame.empty)]
def before : WorldConfiguration Bool Store :=
  ⟨world, true, .context false (.work (.call [] [] call Atom.atomType activation)) inner, stack, emitted⟩
def after (fails : Bool) : WorldConfiguration Bool Store :=
  resumeNested dispatch before false inner [] [] call Atom.atomType (.symbol "touch") [.grounded (.int 7)]
    (advance world false) (plan fails world false)
def nativeRows (fails : Bool) : List Result := if fails then errorRows else rows world false
def insideRows (fails : Bool) : List Result := (nativeRows fails).map (tuplePrepend (.symbol "inside"))
def answers (fails : Bool) : List Result := emitted ++ (outerRows ++ insideRows fails)

theorem actual_nested_native_step (fails : Bool) :
    WorldStep (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      before (after fails) := by
  exact nested_native_step (environment fails) Policy.unmarked before false inner [] [] call Atom.atomType activation
    (.symbol "touch") [.grounded (.int 7)] (outcome fails world false) (advance world false) (plan fails world false)
    rfl (by simp [call, Entry.Value.erase]) rfl (by simp [call, Entry.Value.erase, IsErrorRel])
    (produced fails world false) (prepared fails world false)

theorem actual_reached_caller_source (fails : Bool) :
    (after fails).SourceRel (environment fails) Policy.unmarked (answers fails) (advance world false) := by
  have innerSource : WorldStackRel (environment fails) Policy.unmarked false (advance world false)
      inner (nativeRows fails) (insideRows fails) (advance world false) :=
    .cons (.tupleTail _ _) (.nil _)
  have outerSource : WorldStackRel (environment fails) Policy.unmarked true (advance world false)
      stack (insideRows fails) (outerRows ++ insideRows fails) (advance world false) :=
    .cons (.prepend _ _) (.nil _)
  refine ⟨insideRows fails, outerRows ++ insideRows fails, advance world false, ?_, outerSource, rfl⟩
  cases fails with
  | true => exact .context (.returning errorRows) innerSource
  | false => exact .context (.work (completed_rows world false)) innerSource

theorem retained_native_source_has_no_whole_run_premise (fails : Bool) :
    before.SourceRel (environment fails) Policy.unmarked (answers fails) (advance world false) := by
  apply (nested_source_iff (environment fails) Policy.unmarked before false inner [] [] call Atom.atomType activation
    (.symbol "touch") [.grounded (.int 7)] (answers fails) (advance world false) rfl
    (by simp [call, Entry.Value.erase]) rfl (by simp [call, Entry.Value.erase, IsErrorRel])).mpr
  exact ⟨outcome fails world false, advance world false, plan fails world false, produced fails world false,
    prepared fails world false, actual_reached_caller_source fails⟩

theorem actual_world_completion (fails : Bool) :
    WorldSteps (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      before ⟨advance world false, true, .returning [], [], answers fails⟩ :=
  RecursiveExecution.Contextual.Stateful.source_to_finished (retained_native_source_has_no_whole_run_premise fails)

theorem one_host_operation_changes_only_the_child_context (fails : Bool) :
    (after fails).world false = 6 ∧ (after fails).world true = 40 ∧
      (after fails).context = true ∧ (after fails).stack = stack ∧ (after fails).emitted = emitted := by
  cases fails <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem duplicate_native_values_remain_duplicate :
    (insideRows false).length = 2 ∧ (insideRows false).map (fun item => item.1.erase) =
      [.expression [.symbol "inside", .grounded (.int 5)], .expression [.symbol "inside", .grounded (.int 5)]] := by cbv

theorem caller_binding_theory_survives_the_native_boundary :
    (insideRows false).map (fun item => item.2.bindings) = [activation.bindings, activation.bindings] := by cbv

theorem resetting_the_old_world_cannot_equal_the_reached_cursor (fails : Bool) :
    {after fails with world := world} ≠ after fails := by
  intro same
  have counters := congrArg (fun state : WorldConfiguration Bool Store => state.world false) same
  have changed := (one_host_operation_changes_only_the_child_context fails).1
  change 5 = (after fails).world false at counters
  rw [changed] at counters
  cases counters

theorem replaying_the_host_operation_changes_its_observable_world :
    (advance (advance world false) false) false = 7 ∧ (advance world false) false = 6 := by decide

end Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls
