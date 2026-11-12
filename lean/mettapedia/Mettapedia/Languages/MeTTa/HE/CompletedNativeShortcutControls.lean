import Mettapedia.Languages.MeTTa.HE.CompletedNativeShortcut
import Mettapedia.Languages.MeTTa.HE.NativeDispatchFocusControls

/-!
# Completed-return shortcut: actual callers and unsafe alternatives

Success bypasses the queue while retaining both context callers, aliases,
duplicate occurrences and the reached effect. Runtime errors retain their
normal plan. Emitted function syntax is a counterexample to omitting the
provenance guard.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.CompletedNativeShortcutControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual NativeDispatchFocus
open RetainedNativeDispatchControls (Store environment dispatch world call activation advance plan rows inner stack emitted)
open NativeDispatchFocusControls (path initial reached allAnswers)
open CompletedNativeShortcut

def checked (fails : Bool) : WorldConfiguration Bool Store :=
  resumeChecked dispatch path initial [] [] call Atom.atomType (.symbol "touch") [.grounded (.int 7)]
    (advance world true) (plan fails world true)

theorem successful_queue_is_replaced_not_renamed :
    (checked false).control = path.fill (.returning (rows world true)) ∧
      (reached false).control = path.fill (.work (.boundaryBatch [] [] none
        (.native call (some Atom.atomType) .completed) (rows world true))) := ⟨rfl, rfl⟩

theorem actual_cursor_changes : checked false ≠ reached false := by
  intro same
  have controls := congrArg (fun state : WorldConfiguration Bool Store => state.control) same
  simp [checked, resumeChecked, eligible, dispatch, PassDemand, reached, resumeAt,
    RetainedNativeDispatch.resumeNative, path, CallPath.fill, plan] at controls

theorem completed_shortcut_source (fails : Bool) :
    (checked fails).SourceRel (environment fails) Policy.unmarked (allAnswers fails) (advance world true) :=
  (resume_source_iff (environment fails) Policy.unmarked path initial [] [] call Atom.atomType (.symbol "touch")
    [.grounded (.int 7)] (advance world true) (plan fails world true) (allAnswers fails) (advance world true)).mp
    (NativeDispatchFocusControls.reached_two_level_source fails)

theorem shortcut_continues_in_the_reached_world (fails : Bool) :
    WorldSteps (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      (checked fails) ⟨advance world true, true, .returning [], [], allAnswers fails⟩ := by
  cases fails <;> exact RecursiveExecution.Contextual.Stateful.source_to_finished (completed_shortcut_source _)

theorem both_duplicate_answers_and_aliases_survive :
    (NativeDispatchFocusControls.twiceInside false).length = 2 ∧
      (NativeDispatchFocusControls.twiceInside false).map (fun row => row.2.bindings) =
        [activation.bindings, activation.bindings] := by cbv

theorem a_completed_queue_cannot_drop_a_duplicate :
    ¬Stateful.BoundaryBatchRel (environment false) true (advance world true) [] [] none
      (.native call (some Atom.atomType) .completed) (rows world true)
      [(RetainedNativeDispatchControls.number 40, activation)] (advance world true) (policy := Policy.unmarked) := by
  intro source
  have same := (batch_iff (Or.inl rfl)).mp source |>.1
  have count := congrArg List.length same
  simp [rows] at count

theorem effects_and_retained_callers_are_not_restarted :
    (checked false).world true = 41 ∧ (checked false).world false = 5 ∧
      (checked false).context = initial.context ∧ (checked false).stack = stack ∧
      (checked false).emitted = emitted := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem an_error_does_not_enter_the_shortcut_queue : checked true = reached true := rfl

theorem a_nontrivial_demand_declines_after_the_effect :
    resumeChecked dispatch path initial [] [] call (.symbol "String") (.symbol "touch") [.grounded (.int 7)]
      (advance world true) (.resume (rows world true)) =
    resumeAt dispatch path initial [] [] call (.symbol "String") (.symbol "touch") [.grounded (.int 7)]
      (advance world true) (.resume (rows world true)) := rfl

theorem undefined_demand_is_also_earned :
    eligible dispatch (.symbol "touch") [.grounded (.int 7)] Atom.undefinedType = true := rfl

open Spec.Eval.Completed.Controls (nativeFunctionValue nativeCallValue nativeEnvironment nativeDispatch)

/-- These are actual source calls on the same function-shaped producer row.
Only its provenance changes. Their erased answers are different. -/
theorem provenance_guard_has_a_source_counterexample (policy : Policy) (base : Nat) :
    Stateful.CallRel (nativeEnvironment (.ok [(nativeFunctionValue, Bindings.empty)]) .completed) () base [] []
      nativeCallValue Atom.atomType Completed.Frame.empty [(nativeFunctionValue, Completed.Frame.empty)] (base + 1) (policy := policy) ∧
    Stateful.CallRel (nativeEnvironment (.ok [(nativeFunctionValue, Bindings.empty)]) .emitted) () base [] []
      nativeCallValue Atom.atomType Completed.Frame.empty [(.symbol "Kept", Completed.Frame.empty)] (base + 1) (policy := policy) ∧
    nativeFunctionValue.erase ≠ Atom.symbol "Kept" :=
  ⟨Spec.Eval.Completed.Controls.native_completed_full_source policy nativeFunctionValue base,
    Spec.Eval.Completed.Controls.native_emitted_full_source policy base,
    Spec.Eval.Completed.Controls.native_provenance_separates⟩

theorem the_emitted_counterexample_is_not_admitted :
    eligible (nativeDispatch (.ok [(nativeFunctionValue, Bindings.empty)]) .emitted)
      (.symbol "host") [] Atom.atomType = false := rfl

theorem completed_function_syntax_is_kept_without_interpretation (policy : Policy) (base : Nat) :
    Stateful.BoundaryBatchRel (nativeEnvironment (.ok [(nativeFunctionValue, Bindings.empty)]) .completed) () base [] [] none
      (.native nativeCallValue (some Atom.atomType) .completed) [(nativeFunctionValue, Completed.Frame.empty)]
      [(nativeFunctionValue, Completed.Frame.empty)] base (policy := policy) :=
  (batch_iff (Or.inl rfl)).mpr ⟨rfl, rfl⟩

theorem executing_completed_function_syntax_is_not_a_valid_return (policy : Policy) (base : Nat) :
    ¬Stateful.BoundaryBatchRel (nativeEnvironment (.ok [(nativeFunctionValue, Bindings.empty)]) .completed) () base [] [] none
      (.native nativeCallValue (some Atom.atomType) .completed) [(nativeFunctionValue, Completed.Frame.empty)]
      [(.symbol "Kept", Completed.Frame.empty)] base (policy := policy) := by
  intro source
  have same := (batch_iff (Or.inl rfl)).mp source |>.1
  have values := congrArg (List.map (fun row : Result => row.1.erase)) same
  simp [Spec.Eval.Completed.Controls.nativeFunctionValue, Entry.Value.erase] at values

theorem bypassing_an_emitted_function_loses_its_known_source_answer (policy : Policy) (base : Nat) :
    ¬Control.WorldSourceRel (nativeEnvironment (.ok [(nativeFunctionValue, Bindings.empty)]) .emitted) policy () base
      (.returning [(nativeFunctionValue, Completed.Frame.empty)]) [(.symbol "Kept", Completed.Frame.empty)] base := by
  intro source
  cases source


end Mettapedia.Languages.MeTTa.HE.CompletedNativeShortcutControls
