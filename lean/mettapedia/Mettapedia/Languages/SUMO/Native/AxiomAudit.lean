import Mettapedia.Languages.SUMO.Native

/-!
# Axiom audit for the native SUMO authority

This file records the trusted-assumption surface of the semantic, deductive,
checking, proof-search, and NIK authority theorems.  It is intentionally kept
separate from the public umbrella so ordinary builds do not print the audit.
-/

#print axioms Mettapedia.Languages.SUMO.Native.SemanticsCanary.allInSpine_two_denotes
#print axioms Mettapedia.Languages.SUMO.Native.SemanticsCanary.fixed_tail_accepted
#print axioms Mettapedia.Languages.SUMO.Native.SemanticsCanary.fixed_short_tail_rejected
#print axioms Mettapedia.Languages.SUMO.Native.SemanticsCanary.variadic_repeated_domain_accepted
#print axioms Mettapedia.Languages.SUMO.Native.SemanticsCanary.variadic_wrong_optional_domain_rejected
#print axioms Mettapedia.Languages.SUMO.Native.SemanticsCanary.application_behavior_does_not_determine_domains
#print axioms Mettapedia.Languages.SUMO.Native.SignatureSemantics.RealizesOperator.source_restrictions_iff_object_language
#print axioms Mettapedia.Languages.SUMO.Native.SignatureSemantics.RealizesOperator.tail_guard_iff_source_signature
#print axioms Mettapedia.Languages.SUMO.Native.SignatureSemantics.SignatureSemanticsCanary.example_realizes_operator
#print axioms Mettapedia.Languages.SUMO.Native.SignatureSemantics.SignatureSemanticsCanary.example_realizes_source
#print axioms Mettapedia.Languages.SUMO.Native.SignatureSemantics.SignatureSemanticsCanary.example_optional_argument_accepted
#print axioms Mettapedia.Languages.SUMO.Native.SignatureSemantics.SignatureSemanticsCanary.example_optional_argument_rejected
#print axioms Mettapedia.Languages.SUMO.Native.Model.satisfies_instantiateObject
#print axioms Mettapedia.Languages.SUMO.Native.Model.satisfies_instantiateRow
#print axioms Mettapedia.Languages.SUMO.Native.Derivation.sound
#print axioms Mettapedia.Languages.SUMO.Native.Certificate.check_complete
#print axioms Mettapedia.Languages.SUMO.Native.Certificate.infer_complete
#print axioms Mettapedia.Languages.SUMO.Native.ProofSearch.derivable_iff_reaches_empty
#print axioms Mettapedia.Languages.SUMO.Native.NIKAuthority.checker_authority
#print axioms Mettapedia.Languages.SUMO.Native.NIKAuthority.entailmentChecker_authority
#print axioms Mettapedia.Languages.SUMO.Native.SignatureInference.domainConsequences_sound
#print axioms Mettapedia.Languages.SUMO.Native.SignatureInference.expandedAssumptions_sound
#print axioms Mettapedia.Languages.SUMO.Native.SignatureInference.checker_authority
#print axioms Mettapedia.Languages.SUMO.Native.SignatureInference.checker_projection
#print axioms Mettapedia.Languages.SUMO.Native.SignatureInference.invocation_acceptance_reaches_native_empty
