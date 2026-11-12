import Mettapedia.Machines.PrivateScalarFold

/-!
# Interruption witnesses and exact uncancelled private-fold completion

An interrupted attempt has a concrete cancellation site within its input.
When no such site can be reached, dispatch completes with the ordinary fold's
full world and reply, including a late refusal and source fault.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PrivateScalarCompletion

open PrivateScalarFold

variable {Value Item World : Type}

theorem interruption_has_site (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool)
    (values : List Item) (index : Nat) (initial : Value)
    (interrupted : attempt nativeStep cancel index values initial = .interrupted) :
    ∃ offset < values.length, cancel (index + offset) = true := by
  induction values generalizing index initial with
  | nil => simp [attempt] at interrupted
  | cons item rest ih =>
    by_cases stopped : cancel index = true
    · exact ⟨0, by simp, by simpa using stopped⟩
    · cases calculated : nativeStep initial item with
      | none => simp [attempt, stopped, calculated] at interrupted
      | some next =>
          obtain ⟨offset, within, cancelled⟩ := ih (index + 1) next (by simpa [attempt, stopped, calculated] using interrupted)
          refine ⟨offset + 1, by simpa using Nat.succ_lt_succ within, ?_⟩
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using cancelled

theorem no_cancel_not_interrupted (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool)
    (values : List Item) (index : Nat) (initial : Value)
    (clear : ∀ offset < values.length, cancel (index + offset) = false) :
    attempt nativeStep cancel index values initial ≠ .interrupted := by
  intro interrupted
  obtain ⟨offset, within, cancelled⟩ := interruption_has_site nativeStep cancel values index initial interrupted
  rw [clear offset within] at cancelled
  cases cancelled

theorem uncancelled_dispatch_exact (sourceStep : FoldNativeCompletion.Step Value Item World)
    (nativeStep : Value → Item → Option Value) (cancel : Nat → Bool)
    (values : List Item) (world : World) (initial : Value)
    (refines : StepRefines sourceStep nativeStep world)
    (clear : ∀ offset < values.length, cancel offset = false) :
    dispatch sourceStep nativeStep cancel values world initial =
      .completed (FoldNativeCompletion.produce sourceStep values world initial).1
        (FoldNativeCompletion.produce sourceStep values world initial).2 := by
  have uninterrupted := no_cancel_not_interrupted nativeStep cancel values 0 initial (by simpa using clear)
  cases tried : attempt nativeStep cancel 0 values initial with
  | value result =>
      have exactFold := accepted_fold_refines sourceStep nativeStep cancel world refines 0 values initial result tried
      simp only [dispatch, tried, exactFold]
  | refused => exact refusal_restarts_original sourceStep nativeStep cancel values world initial tried
  | interrupted => exact False.elim (uninterrupted tried)

end Mettapedia.Machines.PrivateScalarCompletion
