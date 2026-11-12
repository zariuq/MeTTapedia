import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointReturn

/-! # Full named-call controls for result checking and retained resumption -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointControls

open PettaCheckpointFixtures

theorem full_named_entry_returns_one_guarded_answer :
    observation services false (initial false) = some ([num 4], [text "before", text "body"]) := by cbv

theorem bad_result_is_refused_after_its_effect :
    observation services true (initial true) = some ([], [text "before", text "body"]) := by cbv

theorem erasing_the_declared_range_changes_the_full_named_call :
    observation erasedRange true (initial true) = some ([text "wrong"], [text "before", text "body"]) := by cbv

theorem missing_result_guard_is_a_real_suspension : suspended.isSome = true := by cbv

theorem suspension_retains_the_completed_effect_prefix :
    suspended.map (fun saved => saved.2.world.output) = some [text "before", text "body"] := by cbv

theorem resuming_the_actual_guard_does_not_replay_the_body :
    resumed = some ([num 4], [text "before", text "body"]) := by cbv

theorem restarting_the_call_replays_the_completed_effect :
    replayed = some ([num 4], [text "before", text "body", text "body"]) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointControls
