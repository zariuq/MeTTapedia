import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeShortcut
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeBoundaryControls
import Mettapedia.Languages.MeTTa.HE.CompletedNativeShortcutControls

/-! # The checked native shortcut composed with its actual retained protocol -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeShortcutControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open RetainedNativeDispatchControls (Store environment dispatch world advance)
open NativeDispatchFocusControls (initial allAnswers)
open HERetainedNativeBoundaryControls (site reply)
open HERetainedNativeShortcut

theorem checked_protocol_observes_its_changed_cursor (fails : Bool) :
    (HERetainedNativeBoundary.protocol Policy.unmarked (site fails) (fun state => [state])).run
      (fun frame => [checkedBody frame]) (reply fails) = [CompletedNativeShortcutControls.checked fails] :=
  protocol_run Policy.unmarked (site fails) (fun state => [state]) (reply fails)

theorem checked_cursor_has_the_complete_source_continuation (fails : Bool) :
    (checkedCursor (reply fails)).SourceRel (environment fails) Policy.unmarked (allAnswers fails) (advance world true) :=
  CompletedNativeShortcutControls.completed_shortcut_source fails

theorem composed_source_and_canonical_run_are_earned (fails : Bool) :
    initial.SourceRel (environment fails) Policy.unmarked (allAnswers fails) (advance world true) ∧
      WorldSteps (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
        initial ⟨advance world true, true, .returning [], [], allAnswers fails⟩ :=
  ⟨(source_completion_iff Policy.unmarked (site fails) (allAnswers fails) (advance world true)).mpr
      ⟨reply fails, checked_cursor_has_the_complete_source_continuation fails⟩,
    canonical_run_of_checked_source (reply fails) (checked_cursor_has_the_complete_source_continuation fails)⟩

theorem successful_protocol_does_not_retain_a_return_check_queue :
    (checkedCursor (reply false)).control = NativeDispatchFocusControls.path.fill
      (.returning (RetainedNativeDispatchControls.rows world true)) := rfl

theorem a_runtime_error_keeps_the_canonical_retained_cursor :
    checkedCursor (reply true) = NativeDispatchFocusControls.reached true := rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERetainedNativeShortcutControls
