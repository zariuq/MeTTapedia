import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnOrdinaryRuns
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRefusalRuns
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnMultiplicityRuns
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSuspensionRuns

/-! # Kernel-checked executions of the live-source typed return fixtures -/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunControls

open PettaCallerReturnRunFixtures

theorem typed_prefix_calls_keep_query_occurrences_and_effects :
    observed services ordinary = some ([num 4, num 4, num 4], [num 7, num 7, num 9]) :=
  PettaCallerReturnRuns.Ordinary.execution

theorem argument_refusal_keeps_the_other_source_choices :
    observed services mixed = some ([num 4, num 4], [num 7, num 9]) :=
  PettaCallerReturnRuns.Mixed.execution

theorem result_refusal_does_not_undo_effects :
    observed services refused = some ([], [num 7, num 7, num 9]) :=
  PettaCallerReturnRuns.Refused.execution

theorem erased_source_range_changes_the_answer_count :
    observed erasedRange refused = some ([num 4, num 4, num 4], [num 7, num 7, num 9]) :=
  PettaCallerReturnRuns.Erased.execution

theorem source_type_answers_and_query_occurrences_multiply :
    observed services multiple = some (List.replicate 4 (num 4), List.replicate 4 (sym "dual")) :=
  PettaCallerReturnRuns.Multiple.execution

theorem repeated_equations_are_not_erased_with_type_rows :
    observed services repeated = some (List.replicate 8 (num 4), List.replicate 8 (sym "dual")) :=
  PettaCallerReturnRuns.Repeated.execution

theorem unavailable_result_guard_keeps_the_reached_effect_and_choices :
    stopped.map (fun saved => (saved.2.world.output, saved.2.scopes.length,
      saved.2.scopes.head?.map (fun scope => scope.frontier.length))) = some ([num 7], 1, some 3) :=
  PettaCallerReturnRuns.Missing.execution

theorem filling_the_guard_resumes_without_body_replay :
    resumed = some ([num 4, num 4, num 4], [num 7, num 7, num 9]) :=
  PettaCallerReturnRuns.Resumed.execution

theorem restarting_from_the_old_body_repeats_an_effect :
    replayed = some ([num 4, num 4, num 4], [num 7, num 7, num 7, num 9]) :=
  PettaCallerReturnRuns.Replayed.execution

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunControls
