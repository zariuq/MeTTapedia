import Mettapedia.Machines.TIsa.Derivation.Evaluator
import Mettapedia.Machines.TIsa.Derivation.Solutions
import Mettapedia.Machines.TIsa.Derivation.Semantics
import Mettapedia.Machines.TIsa.Derivation.StepAdequacy
import Mettapedia.Machines.TIsa.Derivation.Contents
import Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms
import Mettapedia.Machines.TIsa.Derivation.ContinuationPassing
import Mettapedia.Machines.TIsa.Derivation.Defunctionalized
import Mettapedia.Machines.TIsa.Derivation.Machine
import Mettapedia.Machines.TIsa.Derivation.Instructions
import Mettapedia.Machines.TIsa.Derivation.Examples
import Mettapedia.Machines.TIsa.Derivation.FirstOrderIndex
import Mettapedia.Machines.TIsa.Derivation.AnswerTableLimits
import Mettapedia.Machines.TIsa.Derivation.AnswerTableOnMachine
import Mettapedia.Machines.TIsa.Derivation.AnswerTableSchedule
import Mettapedia.Machines.TIsa.Derivation.SymbolicFiringExamples
import Mettapedia.Machines.TIsa.Derivation.SymbolicSelectionSearch
import Mettapedia.Machines.TIsa.Derivation.SymbolicBatchExamples
import Mettapedia.Machines.TIsa.Derivation.SymbolicRunExamples
import Mettapedia.Machines.TIsa.Derivation.SymbolicScheduleExamples
import Mettapedia.Machines.TIsa.Derivation.OpeningRenaming
import Mettapedia.Machines.TIsa.Derivation.OpeningAction
import Mettapedia.Machines.TIsa.Derivation.SerialReopening
import Mettapedia.Machines.TIsa.Derivation.SymbolicIndex
import Mettapedia.Machines.TIsa.Derivation.SymbolicIndexedPorts
import Mettapedia.Machines.TIsa.Derivation.FiniteUnifier

/-!
# The derivation of the transform calculus' abstract machine and instruction set

From the evaluator of a run (`Evaluator`, proved against the step theory in `StepAdequacy` and
instantiated for first-order terms in `FirstOrderTerms`), through continuation-passing style
(`ContinuationPassing`) and defunctionalization (`Defunctionalized`), to the abstract machine
(`Machine`) and its instruction set (`Instructions`); `Examples` runs a multiset program on all of
them.
-/

namespace Mettapedia.Machines.TIsa.Derivation

#print axioms Semantics.admits_stepFiring
#print axioms Semantics.firing_of_admits
#print axioms Semantics.groundStep_iff
#print axioms Semantics.firings_eq_nil_iff
#print axioms Semantics.run_quiescent_sound
#print axioms Semantics.run_exhausted_sound
#print axioms Semantics.groundStep_values
#print axioms FirstOrderTerms.semantics
#print axioms FirstOrderTerms.rangeRestricted_of_scoped
#print axioms solveK_eq
#print axioms runK_eq
#print axioms eval_iff
#print axioms eval_run_iff
#print axioms eval_meaning
#print axioms machine_iff
#print axioms machine_run_iff
#print axioms complete_run
#print axioms complete_run_bounded
#print axioms search_commits
#print axioms step_eq_execute
#print axioms Examples.machine_runs
#print axioms Examples.outcome_unique
#print axioms Examples.dedup_runs
#print axioms Examples.dedup_unreachable
#print axioms Examples.tisa_run
#print axioms OccurrenceIndex.query_eq_filter
#print axioms complete_using
#print axioms indexed_machine_run_iff
#print axioms FirstOrderTerms.collapsing_equal_edges_loses_a_match
#print axioms AnswerTable.materialized_count_eq_derivations
#print axioms AnswerTable.finite_derivations_eventual_count
#print axioms AnswerTable.infinite_iff_unbounded
#print axioms AnswerTable.presence_complete
#print axioms AnswerTable.count_trace_exact
#print axioms AnswerTable.quiescent_counts
#print axioms AnswerTable.finite_counts_reach_quiescence
#print axioms AnswerTable.infinite_counts_exhaust
#print axioms AnswerTable.presence_trace_reaches_complete_table
#print axioms AnswerTable.ScheduleExamples.four_answers_reach_quiescence
#print axioms AnswerTable.ScheduleExamples.productive_cycle_never_reports_finished_counts
#print axioms AnswerTable.ScheduleExamples.productive_cycle_does_report_finished_presence
#print axioms SymbolicFiring.evaluate_exact
#print axioms SymbolicFiring.proposed_collections_include_every_admitted_choice
#print axioms SymbolicFiring.selected_run_iff
#print axioms SymbolicFiring.PreparedOpening.firingsAt_complete
#print axioms SymbolicFiring.Examples.selected_run_keeps_the_tell_and_publishes
#print axioms SymbolicFiring.Examples.a_possible_second_occurrence_refuses_exact_one
#print axioms SymbolicBatch.evaluate_exact
#print axioms SymbolicBatch.Examples.testing_members_alone_loses_the_joint_step
#print axioms SymbolicBatch.Examples.before_tells_cannot_use_the_joint_solution_as_a_guard
#print axioms SymbolicFiring.LiveWorld.template_fresh
#print axioms SymbolicFiring.SameInput.admitted
#print axioms SymbolicFiring.attempts_cover_models
#print axioms SymbolicFiring.search_empty_iff
#print axioms SymbolicFiring.runK_eq
#print axioms SnapshotMachine.world_changed
#print axioms SnapshotMachine.machine_run_iff
#print axioms SymbolicFiring.complete_run
#print axioms SymbolicFiring.every_complete_run_is_licensed
#print axioms SymbolicFiring.RunExamples.binding_survives_publication
#print axioms SymbolicFiring.RunExamples.no_publication_at_zero_fuel
#print axioms SymbolicRound.evaluate_exact
#print axioms SymbolicRound.roundOK_exact
#print axioms SymbolicFiring.RunExamples.jointly_enabled_absence_guards_do_not_give_a_round
#print axioms SymbolicFiring.RunExamples.exact_count_can_survive_a_refresh_in_either_order
#print axioms SymbolicBatch.advanceRequests_exact
#print axioms SymbolicComplete.evaluate_exact
#print axioms SymbolicJointReopening.admits_joint
#print axioms SymbolicJointReopening.admits_snapshot
#print axioms SymbolicJointReopening.result_models
#print axioms SymbolicScheduleSearch.atWidth_covers_joint
#print axioms SymbolicScheduleSearch.maximal_of_full
#print axioms SymbolicScheduleSearch.evaluateMaximal_exact
#print axioms SymbolicScheduleSearch.Examples.one_of_two_is_extendible
#print axioms SymbolicScheduleSearch.Examples.both_leave_no_extension
#print axioms SymbolicSchedules.source_models_covered
#print axioms SymbolicSchedules.finds_at_some_width
#print axioms SymbolicSchedules.found_at_larger_width
#print axioms SymbolicSchedules.every_complete_run_is_licensed
#print axioms SymbolicSchedules.complete_run
#print axioms SymbolicScheduleSearch.Examples.maximal_budget_is_not_quiescence
#print axioms SymbolicScheduleSearch.Examples.width_one_every_cannot_publish
#print axioms Mettapedia.Logic.LP.MutualInstantiation.permutation_of_mutual_lists
#print axioms OpeningRenaming.variable_permutation
#print axioms OpeningRenaming.occurrence_permutation
#print axioms OpeningAction.sequence_exact
#print axioms SerialReopening.round
#print axioms SymbolicScheduleSearch.atWidth_covers_round_models
#print axioms SymbolicRound.prefixProbeCount_exact
#print axioms SymbolicRound.prefixesOK_exact
#print axioms SymbolicIndex.lookup_perm_filter
#print axioms SymbolicIndex.matching_compatible
#print axioms SymbolicIndex.Examples.unknowns_are_not_missing_and_duplicates_are_not_merged
#print axioms SymbolicIndexedPorts.mem_ports
#print axioms SymbolicIndexedPorts.admitted_ports_found
#print axioms SymbolicIndexedPorts.Examples.an_unknown_is_available_to_both_read_ports
#print axioms SymbolicIndexedPorts.Examples.a_conflicting_constant_is_not_a_candidate
#print axioms FiniteUnifier.complete
#print axioms FiniteUnifier.finishes_at
#print axioms FiniteUnifier.resume
#print axioms FiniteUnifier.solved_exact

end Mettapedia.Machines.TIsa.Derivation
