import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticProductReadout

/-!
# Source dependent sum section readouts

Reified first components determine the type of each supplied second component.
Generated type conversion and mixed annotation congruence then reconstruct the
authored pair and projections from their complete native classes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open DependentTypes QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem sigma_class {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (body : TypeOver (QuotientCwf.ext context domain).as) (bodyClass : QType.mk body = codomain) :
    QType.mk (rawSigma annotation (authoredBody annotation domainClass body)) = Sums.sigma domain codomain :=
  (QType.mk_eq_iff _ _).mpr (typeEquality_symm
    (rawSigma_typeEquality _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass)))

theorem instantiated_class {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (body : TypeOver (QuotientCwf.ext context domain).as) (bodyClass : QType.mk body = codomain)
    (argument : QuotientCwf.Tm context domain) (actual : Term context.as annotation)
    (argumentClass : QTerm.mk actual = argument.val) :
    QType.mk ((authoredBody annotation domainClass body).reindex (nativeSection actual)) =
      QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) argument) := by
  have arguments := (QTerm.mk_eq_iff _ _).mp ((chosenTerm_class argument).trans argumentClass.symm)
  calc
    _ = QType.mk ((QuotientCwf.typeRepresentative codomain).reindex (nativeSection (chosenTerm argument))) :=
      (QType.mk_eq_iff _ _).mpr (typeEquality_symm
        (rawInstantiation_typeEquality _ _ (domain_equality annotation domainClass) _ _
          (body_equality annotation domainClass body bodyClass) _ _ arguments.2))
    _ = _ := type_at_argument codomain argument

set_option backward.isDefEq.respectTransparency false in
theorem pair_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : TypeExpr S (context.as.arity + 1)}
    {firstCode secondCode : TermExpr S context.as.arity}
    (first : TypeReadout context domainCode domain)
    (second : TypeReadout (QuotientCwf.ext context domain) bodyCode codomain)
    (left : QuotientCwf.Tm context domain)
    (right : QuotientCwf.Tm context (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) left)))
    (leftRead : TermReadout context firstCode ⟨domain, left⟩)
    (rightRead : TermReadout context secondCode
      ⟨QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) left), right⟩) :
    TermReadout context (.pair domainCode bodyCode firstCode secondCode)
      ⟨Sums.sigma domain codomain, Sums.pair left right⟩ := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyCodeRead, bodyClass⟩
  rcases retype leftRead annotation domainClass.symm with ⟨actualFirst, firstCodeRead, firstClass⟩
  rcases retype rightRead ((authoredBody annotation domainClass body).reindex (nativeSection actualFirst))
    (instantiated_class annotation domainClass body bodyClass left actualFirst firstClass).symm with
    ⟨actualSecond, secondCodeRead, secondClass⟩
  let reconstructed := Sums.rawPair actualFirst actualSecond
  refine ⟨_, reconstructed, ?_, ?_⟩
  · change TermExpr.pair annotation.code (authoredBody annotation domainClass body).code
      actualFirst.code actualSecond.code = _
    rw [authoredBody_code, codeRead, bodyCodeRead, firstCodeRead, secondCodeRead]
  · have firsts := (QTerm.mk_eq_iff _ _).mp ((chosenTerm_class left).trans firstClass.symm)
    have seconds := (QTerm.mk_eq_iff _ _).mp
      ((Sums.componentRepresentative_class left right).trans secondClass.symm)
    exact (Sums.rawPair_compared _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass)
      (chosenTerm left) actualFirst (Sums.componentRepresentative left right) actualSecond
      firsts.2 seconds.2).symm

set_option backward.isDefEq.respectTransparency false in
theorem first_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : TypeExpr S (context.as.arity + 1)}
    {valueCode : TermExpr S context.as.arity}
    (first : TypeReadout context domainCode domain)
    (second : TypeReadout (QuotientCwf.ext context domain) bodyCode codomain)
    (value : QuotientCwf.Tm context (Sums.sigma domain codomain))
    (valueRead : TermReadout context valueCode ⟨Sums.sigma domain codomain, value⟩) :
    TermReadout context (.fst domainCode bodyCode valueCode) ⟨domain, Sums.fst value⟩ := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyCodeRead, bodyClass⟩
  rcases retype valueRead (rawSigma annotation (authoredBody annotation domainClass body))
    (sigma_class annotation domainClass body bodyClass).symm with ⟨actual, valueCodeRead, valueClass⟩
  let reconstructed := Sums.rawFst actual
  refine ⟨annotation, reconstructed, ?_, ?_⟩
  · change TermExpr.fst annotation.code (authoredBody annotation domainClass body).code actual.code = _
    rw [authoredBody_code, codeRead, bodyCodeRead, valueCodeRead]
  · have values := (QTerm.mk_eq_iff _ _).mp
      ((Sums.pairRepresentative_class value).trans valueClass.symm)
    exact (Sums.rawFst_compared _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass) (Sums.pairRepresentative value) actual values.2).symm

set_option backward.isDefEq.respectTransparency false in
theorem second_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : TypeExpr S (context.as.arity + 1)}
    {valueCode : TermExpr S context.as.arity}
    (first : TypeReadout context domainCode domain)
    (second : TypeReadout (QuotientCwf.ext context domain) bodyCode codomain)
    (value : QuotientCwf.Tm context (Sums.sigma domain codomain))
    (valueRead : TermReadout context valueCode ⟨Sums.sigma domain codomain, value⟩) :
    TermReadout context (.snd domainCode bodyCode valueCode)
      ⟨QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) (Sums.fst value)), Sums.snd value⟩ := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyCodeRead, bodyClass⟩
  rcases retype valueRead (rawSigma annotation (authoredBody annotation domainClass body))
    (sigma_class annotation domainClass body bodyClass).symm with ⟨actual, valueCodeRead, valueClass⟩
  let reconstructed := Sums.rawSnd actual
  refine ⟨_, reconstructed, ?_, ?_⟩
  · change TermExpr.snd annotation.code (authoredBody annotation domainClass body).code actual.code = _
    rw [authoredBody_code, codeRead, bodyCodeRead, valueCodeRead]
  · have values := (QTerm.mk_eq_iff _ _).mp
      ((Sums.pairRepresentative_class value).trans valueClass.symm)
    exact (Sums.rawSnd_compared _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass) (Sums.pairRepresentative value) actual values.2).symm

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification
