import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldIngressModel

/-! Source equation ingress checks for the collection fold. The outer
collapse/range/square composition remains a separate endpoint. -/

open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

#print axioms HEOpenSyntaxBinding.bound_read_fixed
#print axioms HEOpenSyntaxBinding.source_fixed_nonvariable
#print axioms HEOpenSyntaxBinding.source_alias
#print axioms HEOpenSyntaxBinding.other_stays_fresh
#print axioms HEOpenSyntaxBinding.resolve_bind_other
#print axioms HEOpenSyntaxBinding.older_closed_read
#print axioms HEOpenSyntaxBinding.older_untouched_read
#print axioms HEOpenSyntaxBinding.mem_bound_support
#print axioms HEOpenSyntaxBinding.other_fixed_read
#print axioms HEOpenSyntaxBinding.alias_read
#print axioms HEOpenSyntaxBinding.unifier_preserves_constraints

#print axioms HEFoldOpenParameters.capture

#print axioms HEFoldParameterCapture.unify_list_append
#print axioms HEFoldParameterCapture.closed_prefix
#print axioms HEFoldParameterCapture.capture

#print axioms HEFoldSourceFrontier.complete_frame

#print axioms HEFoldSourceInvocation.query_read
#print axioms HEFoldSourceInvocation.invocation
#print axioms HEFoldSourceInvocation.eval_source

#print axioms HEFoldIngressModel.append_query
#print axioms HEFoldIngressModel.emitter
#print axioms HEFoldIngressModel.append_interface
#print axioms HEFoldIngressModel.ordinary
#print axioms HEFoldIngressModel.source
#print axioms HEFoldIngressModel.retained_run
#print axioms HEFoldIngressModel.missing_equation_refuses
#print axioms HEFoldIngressModel.Controls.duplicates_and_error_source
#print axioms HEFoldIngressModel.Controls.empty_source
#print axioms HEFoldIngressModel.Controls.equal_parameters_break_template

