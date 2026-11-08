import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseExecution
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSurfaceReturnControls

/-! Kernel audit of committed case selection and its actual source entrance. -/

open Mettapedia.Languages.MeTTa.PeTTa.Bridges

#print axioms ScopedCaseSelection.select_has_source
#print axioms ScopedCaseSelection.Selection.execution
#print axioms ScopedCaseSelection.select_iff_source
#print axioms ScopedCaseSelection.selected_record
#print axioms ScopedCaseSelection.selected_occurrence
#print axioms ScopedCaseSelection.selected_body_property
#print axioms ScopedCaseSelection.selected_keeps_fixed
#print axioms ScopedCaseSelection.selected_append
#print axioms ScopedCaseSelection.first_match_ignores_later_arms
#print axioms ScopedCaseSelection.no_selection_iff
#print axioms ScopedCaseSelection.Controls.selected_empty_does_not_try_next_body
#print axioms ScopedCaseSelection.Controls.earlier_incompatible_arm_is_skipped
#print axioms ScopedCaseSelection.Controls.selection_retains_caller_alias
#print axioms ScopedCaseSource.entered_key_once
#print axioms ScopedCaseSource.selected_body_entry
#print axioms ScopedCaseSource.exhausted_patterns_refuse_only_current
#print axioms ScopedCaseExecution.source_entry
#print axioms ScopedCaseExecution.selected_entry
#print axioms ScopedCaseExecution.exhausted_entry
#print axioms ScopedCaseExecution.selected_entry_attach
#print axioms ScopedQueryBinding.case_entry_local
#print axioms ScopedQueryBinding.case_ready_local
#print axioms ScopedQueryBinding.owned_step_safe
#print axioms ScopedQueryBinding.owned_publication_is_raw
