import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticPredicateReadout

/-!
# Retained refinement readouts in the generated source model

Authored domain and predicate annotations are recovered through the actual
extension comparison. Its section square retains the complete supplied
argument. The semantic guard yields a generated entailment of the authored
predicate at that argument. Mixed annotation congruence then identifies the
authored introduction and forgetting with the chosen source operations.
No unrestricted section is inferred from a conditionally formed term.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem refinement_class {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (body : PredicateOver (QuotientCwf.ext context domain).as) (bodyClass : QPredicate.mk body = predicate) :
    QType.mk (Refinements.rawType annotation (authoredPredicate annotation domainClass body)) =
      Refinements.type domain predicate := by
  change _ = Refinements.typeAt (QuotientCwf.typeRepresentative domain) predicate
  rw [← bodyClass]
  apply (QType.mk_eq_iff _ _).mpr
  exact typeEquality_symm (Refinements.rawType_compared _ _ (domain_equality annotation domainClass)
    body (authoredPredicate annotation domainClass body) (by
      rw [authoredPredicate_roundtrip]
      exact predicateEquality_refl body))

theorem comprehension_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : PropExpr S (context.as.arity + 1)}
    {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (first : TypeReadout context domainCode domain)
    (second : PredicateReadout (QuotientCwf.ext context domain) bodyCode predicate) :
    TypeReadout context (.comprehension domainCode bodyCode) (Refinements.type domain predicate) := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyRead, bodyClass⟩
  refine ⟨Refinements.rawType annotation (authoredPredicate annotation domainClass body), ?_,
    refinement_class annotation domainClass body bodyClass⟩
  change TypeExpr.comprehension annotation.code (authoredPredicate annotation domainClass body).code = _
  rw [authoredPredicate_code, codeRead, bodyRead]

set_option backward.isDefEq.respectTransparency false in
theorem authored_section_comparison {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (term : QuotientCwf.Tm context domain) (actual : Term context.as annotation)
    (classes : QTerm.mk actual = term.val) :
    QuotientCwf.project (nativeSection actual ≫
      (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
        (domain_equality annotation domainClass)).inv) = selfExtend (QuotientCwf.cwf D) term := by
  let converted := actual.convertType (QuotientCwf.typeRepresentative domain)
    (typeEquality_symm (domain_equality annotation domainClass))
  have convertedClass : QTerm.mk converted = term.val :=
    (QTerm.mk_convertType actual _ _).trans classes
  have complete : nativeSection actual ≫
      (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
        (domain_equality annotation domainClass)).inv = nativeSection converted := by
    apply Hom.ext
    change composeSubstitution
      (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
        (domain_equality annotation domainClass)).inv.substitution
      (nativeSection actual).substitution = (nativeSection converted).substitution
    rw [extensionComparison_inv_substitution, identity_composeSubstitution,
      nativeSection_substitution, nativeSection_substitution]
    rfl
  exact (congrArg QuotientCwf.project complete).trans
    (nativeSection_projects_of_class term converted convertedClass)

set_option backward.isDefEq.respectTransparency false in
theorem predicate_at_authored_class {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (body : PredicateOver (QuotientCwf.ext context domain).as) (bodyClass : QPredicate.mk body = predicate)
    (term : QuotientCwf.Tm context domain) (actual : Term context.as annotation)
    (classes : QTerm.mk actual = term.val) :
    QPredicate.mk ((authoredPredicate annotation domainClass body).reindex (nativeSection actual)) =
      RefinementValues.guard predicate term := by
  unfold authoredPredicate
  rw [← PredicateOver.reindex_comp]
  change PredicateAction.reindex (QuotientCwf.project (nativeSection actual ≫
    (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
      (domain_equality annotation domainClass)).inv)) (QPredicate.mk body) = _
  rw [authored_section_comparison annotation domainClass term actual classes, bodyClass]
  rfl

theorem authored_guard {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (body : PredicateOver (QuotientCwf.ext context domain).as) (bodyClass : QPredicate.mk body = predicate)
    (term : QuotientCwf.Tm context domain) (actual : Term context.as annotation)
    (classes : QTerm.mk actual = term.val) (guard : RefinementValues.guard predicate term = ⊤) :
    Holds D (.entails context.as.raw
      ((authoredPredicate annotation domainClass body).code.substitute (instantiate actual.code))) := by
  have predicateRead := predicate_at_authored_class annotation domainClass body bodyClass term actual classes
  have entailed := predicateRead.symm ▸ (Logic.entails_iff_eq_top _).mpr guard
  change Holds D (.entails context.as.raw
    ((authoredPredicate annotation domainClass body).code.substitute (nativeSection actual).substitution))
    at entailed
  rw [nativeSection_substitution] at entailed
  exact entailed

theorem chosen_predicate_comparison {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (body : PredicateOver (QuotientCwf.ext context domain).as) (bodyClass : QPredicate.mk body = predicate) :
    Holds D (.predicateEq (QuotientCwf.ext context domain).as.raw
      (RefinementValues.predicateRepresentative predicate).code
      ((authoredPredicate annotation domainClass body).reindex
        (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
          (domain_equality annotation domainClass)).hom).code) := by
  rw [authoredPredicate_roundtrip]
  exact (QPredicate.mk_eq_iff _ _).mp
    ((RefinementValues.predicateRepresentative_class predicate).trans bodyClass.symm)

set_option backward.isDefEq.respectTransparency false in
theorem refine_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : PropExpr S (context.as.arity + 1)}
    {termCode : TermExpr S context.as.arity} {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (first : TypeReadout context domainCode domain)
    (second : PredicateReadout (QuotientCwf.ext context domain) bodyCode predicate)
    (term : QuotientCwf.Tm context domain) (guard : RefinementValues.guard predicate term = ⊤)
    (termRead : TermReadout context termCode ⟨domain, term⟩) :
    TermReadout context (.refine domainCode bodyCode termCode)
      ⟨Refinements.type domain predicate, RefinementValues.intro_of_top predicate term guard⟩ := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyRead, bodyClass⟩
  rcases retype termRead annotation domainClass.symm with ⟨actual, termCodeRead, termClass⟩
  let rightGuard := authored_guard annotation domainClass body bodyClass term actual termClass guard
  let reconstructed := Refinements.rawIntro (authoredPredicate annotation domainClass body) actual rightGuard
  refine ⟨_, reconstructed, ?_, ?_⟩
  · change TermExpr.refine annotation.code (authoredPredicate annotation domainClass body).code actual.code = _
    rw [authoredPredicate_code, codeRead, bodyRead, termCodeRead]
  · have leftGuard := RefinementValues.raw_guard predicate term ((Logic.entails_iff_eq_top _).mpr guard)
    have compared := Refinements.rawIntro_compared _ _ (domain_equality annotation domainClass)
      (RefinementValues.predicateRepresentative predicate) (authoredPredicate annotation domainClass body)
      (chosen_predicate_comparison annotation domainClass body bodyClass)
      (chosenTerm term) actual (chosenTerm_represents term actual termClass) leftGuard rightGuard
    have types := Refinements.rawType_compared _ _ (domain_equality annotation domainClass)
      (RefinementValues.predicateRepresentative predicate) (authoredPredicate annotation domainClass body)
      (chosen_predicate_comparison annotation domainClass body bodyClass)
    exact ((QTerm.mk_eq_iff _ _).mpr ⟨types, compared⟩).symm

set_option backward.isDefEq.respectTransparency false in
theorem forget_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : PropExpr S (context.as.arity + 1)}
    {termCode : TermExpr S context.as.arity} {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (first : TypeReadout context domainCode domain)
    (second : PredicateReadout (QuotientCwf.ext context domain) bodyCode predicate)
    (term : QuotientCwf.Tm context (Refinements.type domain predicate))
    (termRead : TermReadout context termCode ⟨Refinements.type domain predicate, term⟩) :
    TermReadout context (.forget domainCode bodyCode termCode)
      ⟨domain, RefinementValues.forget predicate term⟩ := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyRead, bodyClass⟩
  rcases retype termRead (Refinements.rawType annotation (authoredPredicate annotation domainClass body))
      (refinement_class annotation domainClass body bodyClass).symm with
    ⟨actual, termCodeRead, termClass⟩
  let reconstructed := Refinements.rawForget actual
  refine ⟨annotation, reconstructed, ?_, ?_⟩
  · change TermExpr.forget annotation.code (authoredPredicate annotation domainClass body).code actual.code = _
    rw [authoredPredicate_code, codeRead, bodyRead, termCodeRead]
  · have sameValue := ((QTerm.mk_eq_iff _ _).mp
      ((RefinementValues.refinementTermRepresentative_class predicate term).trans termClass.symm)).2
    have compared := Refinements.rawForget_compared _ _ (domain_equality annotation domainClass)
      (RefinementValues.predicateRepresentative predicate) (authoredPredicate annotation domainClass body)
      (chosen_predicate_comparison annotation domainClass body bodyClass)
      (RefinementValues.refinementTermRepresentative predicate term) actual sameValue
    exact ((QTerm.mk_eq_iff _ _).mpr ⟨domain_equality annotation domainClass, compared⟩).symm

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
