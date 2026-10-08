import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualQuantifiers
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicateAction
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualRefinements

/-!
# Quantifiers on the chosen generated dependent model

Predicate equations descend through both quantifiers. Equal domain
presentations compare through their actual context isomorphism. These
comparisons prove base change for the chosen CwF display substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Quantifiers

open _root_.CategoryTheory
open QuotientComprehensionSyntax
open Mettapedia.GSLT.Core.ContextualLadder

universe u
variable {S : Symbols.{u}} {D : Signature S}

def forallAt {context : Context D} (domain : TypeOver context)
    (predicate : QPredicate (extend context domain)) : QPredicate context :=
  _root_.Quotient.lift (fun formed => QPredicate.mk (rawForall domain formed))
    (fun first second same => _root_.Quotient.sound
      (conclude (.universalCongruence context.raw domain.code domain.code first.code second.code)
        ⟨typeEquality_refl domain, same, second.formed, trivial⟩)) predicate

def existsAt {context : Context D} (domain : TypeOver context)
    (predicate : QPredicate (extend context domain)) : QPredicate context :=
  _root_.Quotient.lift (fun formed => QPredicate.mk (rawExists domain formed))
    (fun first second same => _root_.Quotient.sound
      (conclude (.existentialCongruence context.raw domain.code domain.code first.code second.code)
        ⟨typeEquality_refl domain, same, second.formed, trivial⟩)) predicate

theorem forallAt_reindex {source target : Context D} (morphism : source ⟶ target)
    (domain : TypeOver target) (predicate : QPredicate (extend target domain)) :
    (forallAt domain predicate).reindex morphism =
      forallAt (domain.reindex morphism) (predicate.reindex (rawLift morphism domain)) := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  exact congrArg QPredicate.mk (rawForall_reindex morphism domain formed)

theorem existsAt_reindex {source target : Context D} (morphism : source ⟶ target)
    (domain : TypeOver target) (predicate : QPredicate (extend target domain)) :
    (existsAt domain predicate).reindex morphism =
      existsAt (domain.reindex morphism) (predicate.reindex (rawLift morphism domain)) := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  exact congrArg QPredicate.mk (rawExists_reindex morphism domain formed)

theorem forallAt_compared {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : QPredicate (extend context first)) (secondBody : QPredicate (extend context second))
    (sameBody : firstBody = secondBody.reindex (extensionComparison first second sameDomain).hom) :
    forallAt first firstBody = forallAt second secondBody := by
  revert sameBody
  refine _root_.Quotient.inductionOn₂ firstBody secondBody fun left right same => ?_
  have rawSame := (QPredicate.mk_eq_iff _ _).mp same
  rw [Refinements.extensionComparison_predicate_code] at rawSame
  exact _root_.Quotient.sound
    (conclude (.universalCongruence context.raw first.code second.code left.code right.code)
      ⟨sameDomain, rawSame, right.formed, trivial⟩)

theorem existsAt_compared {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : QPredicate (extend context first)) (secondBody : QPredicate (extend context second))
    (sameBody : firstBody = secondBody.reindex (extensionComparison first second sameDomain).hom) :
    existsAt first firstBody = existsAt second secondBody := by
  revert sameBody
  refine _root_.Quotient.inductionOn₂ firstBody secondBody fun left right same => ?_
  have rawSame := (QPredicate.mk_eq_iff _ _).mp same
  rw [Refinements.extensionComparison_predicate_code] at rawSame
  exact _root_.Quotient.sound
    (conclude (.existentialCongruence context.raw first.code second.code left.code right.code)
      ⟨sameDomain, rawSame, right.formed, trivial⟩)

noncomputable def all {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (predicate : QPredicate (QuotientCwf.ext context domain).as) : QPredicate context.as :=
  forallAt (QuotientCwf.typeRepresentative domain) predicate

noncomputable def some {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (predicate : QPredicate (QuotientCwf.ext context domain).as) : QPredicate context.as :=
  existsAt (QuotientCwf.typeRepresentative domain) predicate

theorem reindex_representative {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (predicate : QPredicate target.as) :
    PredicateAction.reindex morphism predicate = predicate.reindex (QuotientCwf.representative morphism) := by
  calc
    _ = PredicateAction.reindex (QuotientCwf.project (QuotientCwf.representative morphism)) predicate :=
      congrArg (fun arrow => PredicateAction.reindex arrow predicate)
        (QuotientCwf.project_representative morphism).symm
    _ = _ := rfl

theorem reindexed_body_comparison {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty target)
    (predicate : QPredicate (QuotientCwf.ext target domain).as) :
    predicate.reindex (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain)) =
      (PredicateAction.reindex
        (TypeOver.extensionSubstitution (C := QuotientCwf.cwf D) morphism domain) predicate).reindex
          (extensionComparison
            ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))
            (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain morphism))
            (reindexed_domain_equality morphism domain)).hom := by
  let comparison := (extensionComparison
    ((QuotientCwf.typeRepresentative domain).reindex (QuotientCwf.representative morphism))
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub domain morphism))
    (reindexed_domain_equality morphism domain)).hom
  have complete : comparison ≫ nativeLift morphism domain =
      rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain) := by
    apply Hom.ext
    funext index
    change ((nativeLift morphism domain).substitution index).substitute comparison.substitution =
      (rawLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative domain)).substitution index
    rw [show comparison.substitution = TermExpr.var from extensionComparison_hom_substitution _ _ _]
    exact (TermExpr.substitute_identity _).trans
      (congrFun (nativeLift_substitution morphism domain) index |>.trans
        (congrFun (rawLift_substitution (QuotientCwf.representative morphism)
          (QuotientCwf.typeRepresentative domain)) index).symm)
  have projected : PredicateAction.reindex
      (TypeOver.extensionSubstitution (C := QuotientCwf.cwf D) morphism domain) predicate =
      predicate.reindex (nativeLift morphism domain) := by
    rw [← nativeLift_projects]
    rfl
  calc
    _ = predicate.reindex (comparison ≫ nativeLift morphism domain) :=
      congrArg (fun arrow => predicate.reindex arrow) complete.symm
    _ = (predicate.reindex (nativeLift morphism domain)).reindex comparison :=
      QPredicate.reindex_comp predicate comparison (nativeLift morphism domain)
    _ = _ := congrArg (fun body => body.reindex comparison) projected.symm

theorem all_substitution {source target : QuotientCwf.QContext D} (morphism : source ⟶ target)
    (domain : QuotientCwf.Ty target) (predicate : QPredicate (QuotientCwf.ext target domain).as) :
    PredicateAction.reindex morphism (all domain predicate) =
      all (QuotientCwf.tySub domain morphism)
        (PredicateAction.reindex (TypeOver.extensionSubstitution (C := QuotientCwf.cwf D) morphism domain)
          predicate) := by
  exact (reindex_representative morphism (all domain predicate)).trans
    ((forallAt_reindex (QuotientCwf.representative morphism)
      (QuotientCwf.typeRepresentative domain) predicate).trans
      (forallAt_compared _ _ (reindexed_domain_equality morphism domain) _ _
        (reindexed_body_comparison morphism domain predicate)))

theorem some_substitution {source target : QuotientCwf.QContext D} (morphism : source ⟶ target)
    (domain : QuotientCwf.Ty target) (predicate : QPredicate (QuotientCwf.ext target domain).as) :
    PredicateAction.reindex morphism (some domain predicate) =
      some (QuotientCwf.tySub domain morphism)
        (PredicateAction.reindex (TypeOver.extensionSubstitution (C := QuotientCwf.cwf D) morphism domain)
          predicate) := by
  exact (reindex_representative morphism (some domain predicate)).trans
    ((existsAt_reindex (QuotientCwf.representative morphism)
      (QuotientCwf.typeRepresentative domain) predicate).trans
      (existsAt_compared _ _ (reindexed_domain_equality morphism domain) _ _
        (reindexed_body_comparison morphism domain predicate)))

theorem all_adjunction {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (body : QPredicate (QuotientCwf.ext context domain).as) (premise : QPredicate context.as) :
    PredicateAction.reindex (QuotientCwf.wk domain) premise ≤ body ↔ premise ≤ all domain body := by
  refine _root_.Quotient.inductionOn₂ body premise fun formed first => ?_
  exact raw_forall_adjoint (QuotientCwf.typeRepresentative domain) first formed

theorem some_adjunction {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (body : QPredicate (QuotientCwf.ext context domain).as) (consequent : QPredicate context.as) :
    some domain body ≤ consequent ↔ body ≤ PredicateAction.reindex (QuotientCwf.wk domain) consequent := by
  refine _root_.Quotient.inductionOn₂ body consequent fun formed last => ?_
  exact raw_exists_adjoint (QuotientCwf.typeRepresentative domain) formed last

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Quantifiers
