import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticTypeReadout

/-!
# Source product section readouts

Dependent annotation readouts reconstruct authored product domains and bodies.
The actual supplied body, function and argument classes are retyped by generated
conversion, then compared with the chosen implementation through the mixed
annotation congruence rules. The resulting lambda and application retain their
complete authored codes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open DependentTypes QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem pi_class {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (body : TypeOver (QuotientCwf.ext context domain).as) (bodyClass : QType.mk body = codomain) :
    QType.mk (rawPi annotation (authoredBody annotation domainClass body)) = Products.pi domain codomain :=
  (QType.mk_eq_iff _ _).mpr (typeEquality_symm
    (rawPi_typeEquality _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass)))

noncomputable def authoredTerm {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    {body : TypeOver (QuotientCwf.ext context domain).as}
    (term : Term (QuotientCwf.ext context domain).as body) :
    Term (extend context.as annotation) (authoredBody annotation same body) :=
  term.reindex (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
    (domain_equality annotation same)).inv

set_option backward.isDefEq.respectTransparency false in
theorem authoredTerm_code {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    {body : TypeOver (QuotientCwf.ext context domain).as}
    (term : Term (QuotientCwf.ext context domain).as body) :
    (authoredTerm annotation same term).code = term.code := by
  change term.code.substitute _ = _
  rw [extensionComparison_inv_substitution, TermExpr.substitute_identity]

set_option backward.isDefEq.respectTransparency false in
theorem authoredTerm_roundtrip {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    {body : TypeOver (QuotientCwf.ext context domain).as}
    (term : Term (QuotientCwf.ext context domain).as body) :
    QTerm.mk ((authoredTerm annotation same term).reindex
      (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
        (domain_equality annotation same)).hom) = QTerm.mk term := by
  unfold authoredTerm
  rw [← QTerm.reindex_mk, ← QTerm.reindex_mk, ← QTerm.reindex_comp, Iso.hom_inv_id]
  exact QTerm.reindex_id (QTerm.mk term)

set_option backward.isDefEq.respectTransparency false in
theorem lambda_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : TypeExpr S (context.as.arity + 1)}
    {termCode : TermExpr S (context.as.arity + 1)}
    (first : TypeReadout context domainCode domain)
    (second : TypeReadout (QuotientCwf.ext context domain) bodyCode codomain)
    (term : QuotientCwf.Tm (QuotientCwf.ext context domain) codomain)
    (bodyRead : TermReadout (QuotientCwf.ext context domain) termCode ⟨codomain, term⟩) :
    TermReadout context (.lam domainCode bodyCode termCode)
      ⟨Products.pi domain codomain, Products.lam term⟩ := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyCodeRead, bodyClass⟩
  rcases retype bodyRead body bodyClass.symm with ⟨actual, termCodeRead, termClass⟩
  let reconstructed := Products.rawLam (authoredTerm annotation domainClass actual)
  refine ⟨_, reconstructed, ?_, ?_⟩
  · change TermExpr.lam annotation.code (authoredBody annotation domainClass body).code
      (authoredTerm annotation domainClass actual).code = _
    rw [authoredBody_code, authoredTerm_code, codeRead, bodyCodeRead, termCodeRead]
  · have supplied : QTerm.mk (chosenTerm term) = QTerm.mk
        ((authoredTerm annotation domainClass actual).reindex
          (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
            (domain_equality annotation domainClass)).hom) :=
      (chosenTerm_class term).trans
        (termClass.symm.trans (authoredTerm_roundtrip annotation domainClass actual).symm)
    have compared := Products.rawLam_compared _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass)
      (chosenTerm term) (authoredTerm annotation domainClass actual)
      ((QTerm.mk_eq_iff _ _).mp supplied).2
    exact compared.symm

set_option backward.isDefEq.respectTransparency false in
theorem application_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : TypeExpr S (context.as.arity + 1)}
    {functionCode argumentCode : TermExpr S context.as.arity}
    (first : TypeReadout context domainCode domain)
    (second : TypeReadout (QuotientCwf.ext context domain) bodyCode codomain)
    (function : QuotientCwf.Tm context (Products.pi domain codomain))
    (argument : QuotientCwf.Tm context domain)
    (functionRead : TermReadout context functionCode ⟨Products.pi domain codomain, function⟩)
    (argumentRead : TermReadout context argumentCode ⟨domain, argument⟩) :
    TermReadout context (.app domainCode bodyCode functionCode argumentCode)
      ⟨QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) argument), Products.app function argument⟩ := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyCodeRead, bodyClass⟩
  rcases retype functionRead (rawPi annotation (authoredBody annotation domainClass body))
    (pi_class annotation domainClass body bodyClass).symm with
    ⟨actualFunction, functionCodeRead, functionClass⟩
  rcases retype argumentRead annotation domainClass.symm with ⟨actualArgument, argumentCodeRead, argumentClass⟩
  let reconstructed := Products.rawApp actualFunction actualArgument
  refine ⟨_, reconstructed, ?_, ?_⟩
  · change TermExpr.app annotation.code (authoredBody annotation domainClass body).code
      actualFunction.code actualArgument.code = _
    rw [authoredBody_code, codeRead, bodyCodeRead, functionCodeRead, argumentCodeRead]
  · have functions := (QTerm.mk_eq_iff _ _).mp
      ((Products.functionRepresentative_class function).trans functionClass.symm)
    have arguments := (QTerm.mk_eq_iff _ _).mp
      ((chosenTerm_class argument).trans argumentClass.symm)
    exact (Products.rawApp_compared _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass)
      (Products.functionRepresentative function) actualFunction (chosenTerm argument) actualArgument
      functions.2 arguments.2).symm

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
