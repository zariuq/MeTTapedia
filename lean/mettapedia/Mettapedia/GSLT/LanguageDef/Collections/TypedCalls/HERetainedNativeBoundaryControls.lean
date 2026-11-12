import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundary
import Mettapedia.Languages.MeTTa.HE.NativeDispatchFocusControls

/-!
# Shared-protocol controls at a two-level retained native site

Cursor observation checks the protocol handoff. The independent host-model
source proof then supplies its complete world-machine continuation. Neither
the cursor observation nor the local host contract is a C execution theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundaryControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open RetainedNativeDispatchControls (Store environment dispatch world call activation outcome advance plan produced prepared)
open NativeDispatchFocusControls (path initial reached allAnswers)
open HERetainedNativeBoundary

def site (fails : Bool) : Site (environment fails) where
  state := initial
  path := path
  live := []
  scope := []
  value := call
  expected := Atom.atomType
  activation := activation
  operator := .symbol "touch"
  arguments := [.grounded (.int 7)]
  atCall := rfl
  shape := by simp [call, Entry.Value.erase]
  executable := rfl
  notError := by simp [call, Entry.Value.erase, IsErrorRel]

def reply (fails : Bool) : Reply Policy.unmarked (site fails) where
  outcome := outcome fails world true
  reached := advance world true
  plan := plan fails world true
  produced := produced fails world true
  prepared := prepared fails world true

theorem protocol_hands_off_the_actual_cursor (fails : Bool) :
    (protocol Policy.unmarked (site fails) (fun state => [state])).run
      (fun frame => [frame.state]) (reply fails) = [reached fails] := by
  exact protocol_run Policy.unmarked (site fails) (fun state => [state]) (reply fails)

theorem a_successful_native_batch_enters_one_language_frame :
    ((protocol Policy.unmarked (site false) (fun state => [state])).enter (reply false)).length = 1 := rfl

theorem a_runtime_error_resumes_the_caller_without_a_body_frame :
    (protocol Policy.unmarked (site true) (fun state => [state])).enter (reply true) = [] ∧
      (protocol Policy.unmarked (site true) (fun state => [state])).early (reply true) = [reached true] :=
  ⟨rfl, rfl⟩

theorem observed_handoff_is_an_actual_world_step (fails : Bool) :
    WorldStep (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      initial (reached fails) := reply_transition Policy.unmarked (site fails) (reply fails)

theorem source_completion_is_earned_from_the_reached_native_reply (fails : Bool) :
    initial.SourceRel (environment fails) Policy.unmarked (allAnswers fails) (advance world true) := by
  apply (source_completion_iff Policy.unmarked (site fails) (allAnswers fails) (advance world true)).mpr
  exact ⟨reply fails, NativeDispatchFocusControls.reached_two_level_source fails⟩

theorem caller_results_include_the_reached_world (fails : Bool) :
    WorldSteps (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      initial ⟨advance world true, true, .returning [], [], allAnswers fails⟩ :=
  RecursiveExecution.Contextual.Stateful.source_to_finished (source_completion_is_earned_from_the_reached_native_reply fails)

theorem a_saved_snapshot_would_erase_a_real_effect (fails : Bool) :
    (reached fails).world true = 41 ∧ initial.world true = 40 ∧ (reached fails).world true ≠ initial.world true := by
  have changed := (NativeDispatchFocusControls.the_repeated_context_identity_observes_its_own_write fails).1
  exact ⟨changed, rfl, by rw [changed]; decide⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundaryControls
