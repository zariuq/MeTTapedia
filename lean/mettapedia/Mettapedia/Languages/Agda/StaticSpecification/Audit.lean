import Mettapedia.Languages.Agda.StaticSpecification.Examples

/-!
# Independent static-reference axiom audit

This audit checks the finite-Set relevant Pi fragment and its retained structural
metatheory. It makes no native-presentation adequacy, normalization, decision,
confluence, general subject-reduction, or full Agda claim.
-/

namespace Mettapedia.Languages.Agda.StaticSpecification

#print axioms Renaming.lift_comp
#print axioms Term.rename_id
#print axioms Term.rename_comp
#print axioms Ty.rename_comp
#print axioms Term.subst_id
#print axioms Term.subst_comp
#print axioms Ty.subst_comp
#print axioms Abs.subst_comp
#print axioms TyAbs.subst_comp
#print axioms Elim.subst_comp
#print axioms Term.subst_weaken
#print axioms Ty.subst_weaken
#print axioms Term.applySpine_subst
#print axioms Abs.instantiate_subst
#print axioms TyAbs.instantiate_subst
#print axioms FormTy.context
#print axioms Typing.context
#print axioms TypeEq.context
#print axioms TermEq.context
#print axioms TypeEq.level_eq
#print axioms Typing.sort_level
#print axioms FormTy.sort_annotation
#print axioms FormTy.rename
#print axioms Typing.rename
#print axioms TypeEq.rename
#print axioms TermEq.rename
#print axioms FormTy.weaken
#print axioms Typing.weaken
#print axioms TypeEq.weaken
#print axioms TermEq.weaken
#print axioms FormTy.substitute
#print axioms Typing.substitute
#print axioms TypeEq.substitute
#print axioms TermEq.substitute
#print axioms SubDeriv.lift
#print axioms SubDeriv.identity
#print axioms SubDeriv.comp
#print axioms SubDeriv.single
#print axioms SubDeriv.pair
#print axioms Typing.instantiate
#print axioms SpineTyping.typing
#print axioms SpineTyping.rename
#print axioms SpineTyping.substitute
#print axioms FormCtx.lookup
#print axioms Typing.applyNewest
#print axioms Typing.etaExpand
#print axioms TermEq.etaExpand
#print axioms Examples.identityAtTypeVariable
#print axioms Examples.substitutedOlderType
#print axioms Examples.substitutedNewestType
#print axioms Examples.distinct_type_images
#print axioms Examples.substitutedIdentity
#print axioms Examples.closedBeta
#print axioms Examples.closedBetaReduct
#print axioms Examples.beta_is_not_raw_equality
#print axioms Examples.closedEta
#print axioms Examples.eta_is_not_raw_equality
#print axioms Examples.orderedSpineTyping
#print axioms Examples.orderedSpineResult
#print axioms Examples.swapping_spine_changes_raw_term
#print axioms Examples.avoids_capture
#print axioms Examples.rejects_captured_result
#print axioms Examples.nonbinding_instantiation
#print axioms Examples.wrong_universe_rejected
#print axioms Examples.wrong_annotation_rejected
#print axioms Examples.malformed_telescope_rejected
#print axioms Examples.malformed_telescope_has_no_typing
#print axioms Examples.distinct_universes_not_convertible
#print axioms Examples.retained_derivations_distinct

end Mettapedia.Languages.Agda.StaticSpecification
