import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns

/-! # Compound source return realization: complete theorem audit -/

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.ReturnsVariable.control_or_variable
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.checksReturnVariable_sound
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.nestedLets_returns_variable
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.bindAnswers_returning
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.selectCase_returning
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.selectAnswers_returning
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.queryBodies_returning
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.queries_returning
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.protected_transition
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.ReturnedValue.append
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.tail_step
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.return_configuration_step
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.return_configuration_steps
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.reached_return_values
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.completed_protected_return
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.ReturnControls.print_prefix_returns_protected
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.ReturnControls.return_recognizer_controls
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.ReturnControls.duplicate_answers_keep_effect_order
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.ReturnControls.match_body_returns_protected
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.ReturnControls.matched_occurrences_are_not_collapsed
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Unifying.ReturnControls.open_return_syntax_is_not_value_stability
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns.source_ground_of_support
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns.protected_value_faithful
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns.completed_source_faithful
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns.completed_source_guard_exact
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns.checked_source_guard_exact
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns.Controls.print_entry_idempotent
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns.Controls.complete_print_run
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns.Controls.effectful_compound_guard_keeps_three_occurrences

