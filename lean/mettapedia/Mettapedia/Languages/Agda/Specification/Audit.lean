import Mettapedia.Languages.Agda.Specification.Examples

/-!
# Foundation audit for the independent application-only reference

The audited declarations cover scope actions, finite computation, uniqueness,
capture avoidance, spine composition, and the positive and negative controls.
-/

namespace Mettapedia.Languages.Agda.Specification

#print axioms Renaming.lift_comp
#print axioms Term.rename_id
#print axioms Term.rename_comp
#print axioms Ty.rename_comp
#print axioms TyAbs.rename_comp
#print axioms Spine.append_assoc
#print axioms Spine.rename_append
#print axioms Substitute.identity
#print axioms Substitute.rename
#print axioms Apply.deterministic
#print axioms Instantiate.deterministic
#print axioms Substitute.deterministic
#print axioms SubstituteAbs.deterministic
#print axioms SubstituteTy.deterministic
#print axioms SubstituteTyAbs.deterministic
#print axioms SubstituteSpine.deterministic
#print axioms Apply.mapRenaming
#print axioms Instantiate.mapRenaming
#print axioms Substitute.mapRenaming
#print axioms Substitute.rename_single
#print axioms Apply.append
#print axioms SubstituteSpine.append
#print axioms Examples.identity_apply
#print axioms Examples.noBind_apply
#print axioms Examples.constant_apply
#print axioms Examples.capture_preserved
#print axioms Examples.capture_rejected
#print axioms Examples.substitute_applied_variable
#print axioms Examples.constant_two_arguments
#print axioms Examples.annotatedPi_identity
#print axioms Examples.pi_is_not_a_function
#print axioms Examples.sort_is_not_a_function
#print axioms Examples.definition_spine
#print axioms Examples.constructor_spine
#print axioms Examples.selfApply_no_result

end Mettapedia.Languages.Agda.Specification
