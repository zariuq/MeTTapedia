import Mettapedia.Languages.MeTTa.PeTTa.DestinationRefinementControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding

/-! Kernel audit of actual Destination and typed occurrence binding preservation. -/

#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.Extends.refl
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.Extends.trans
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.append_extends
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.accepted_extends
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.argument_return_extends
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.local_step_extends
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.actual_local_step_extends
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.finished_record_is_reached
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.silent_context_preserved
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.finished_context_preserved
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.resolved_packet_absorbed
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.action_silent
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.action_call
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.scopes_cons
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.ScopeGood.frontier
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.ScopeGood.record
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.focus_good
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.primitive_work_good
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.superpose_work_good
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.selected_frontier_good
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.query_frontier_good
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.invocation_preserves
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.active_preserves
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.collection_preserves
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.scoped_preserves
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.actual_scope_preserves
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.continuing_preserves
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.path_preserves
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.published_record_refines
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.read_ground
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.fixed_of_resolved
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.Fixed.extends
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.actual_resolver_earns_ground_slot
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.reached_work_keeps_ground_slot
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.accepted_protected_return
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.conflicting_return_refused
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.Controls.seven_fixed
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.Controls.eight_fixed
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.Controls.same_context_can_retain_distinct_ground_occurrences
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots.Controls.changing_ground_slot_is_not_a_refinement
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.Controls.refused_branch_keeps_exact_sibling_and_world
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.Controls.both_occurrences_have_separate_ground_witnesses
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.RefinementTransport.Controls.actual_refusal_preserves_the_other_ground_value
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.silent_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.call_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.source_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.install_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.enterRows_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.nextArgument_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.consumeArgument_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.consumeBody_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.delegate_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.step_safe
#print axioms Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding.path_safe

