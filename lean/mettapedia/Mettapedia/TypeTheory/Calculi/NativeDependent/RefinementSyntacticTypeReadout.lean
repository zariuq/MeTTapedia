import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticReification

/-!
# Source dependent formation readouts

Successful dependent annotation readouts supply actual generated formation
trees. The chosen domain representative is compared with the authored domain
by a typed extension isomorphism. Product and sum formation recover their
authored annotations through this comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open DependentTypes

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem domain_equality {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain) :
    Holds D (.typeEq context.as.raw (QuotientCwf.typeRepresentative domain).code annotation.code) :=
  (QType.mk_eq_iff _ _).mp ((QuotientCwf.typeRepresentative_class domain).trans same.symm)

noncomputable def authoredBody {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    (body : TypeOver (QuotientCwf.ext context domain).as) : TypeOver (extend context.as annotation) :=
  body.reindex (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
    (domain_equality annotation same)).inv

set_option backward.isDefEq.respectTransparency false in
theorem authoredBody_code {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    (body : TypeOver (QuotientCwf.ext context domain).as) :
    (authoredBody annotation same body).code = body.code := by
  change body.code.substitute _ = _
  rw [extensionComparison_inv_substitution, TypeExpr.substitute_identity]

set_option backward.isDefEq.respectTransparency false in
theorem authoredBody_roundtrip {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    (body : TypeOver (QuotientCwf.ext context domain).as) :
    (authoredBody annotation same body).reindex
      (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
        (domain_equality annotation same)).hom = body := by
  unfold authoredBody
  rw [← TypeOver.reindex_comp, Iso.hom_inv_id]
  exact body.reindex_id

theorem body_equality {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (annotation : TypeOver context.as) (domainClass : QType.mk annotation = domain)
    (body : TypeOver (QuotientCwf.ext context domain).as) (bodyClass : QType.mk body = codomain) :
    Holds D (.typeEq (QuotientCwf.ext context domain).as.raw
      (QuotientCwf.typeRepresentative codomain).code
      ((authoredBody annotation domainClass body).reindex
        (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
          (domain_equality annotation domainClass)).hom).code) := by
  rw [authoredBody_roundtrip]
  exact (QType.mk_eq_iff _ _).mp
    ((QuotientCwf.typeRepresentative_class codomain).trans bodyClass.symm)

theorem pi_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {domainCode : TypeExpr S context.as.arity}
    {bodyCode : TypeExpr S (context.as.arity + 1)}
    (first : TypeReadout context domainCode domain)
    (second : TypeReadout (QuotientCwf.ext context domain) bodyCode codomain) :
    TypeReadout context (.pi domainCode bodyCode) (Products.pi domain codomain) := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyRead, bodyClass⟩
  refine ⟨rawPi annotation (authoredBody annotation domainClass body), ?_, ?_⟩
  · change TypeExpr.pi annotation.code (authoredBody annotation domainClass body).code = _
    rw [authoredBody_code, codeRead, bodyRead]
  · apply (QType.mk_eq_iff _ _).mpr
    exact typeEquality_symm (rawPi_typeEquality _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass))

theorem sigma_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {domainCode : TypeExpr S context.as.arity}
    {bodyCode : TypeExpr S (context.as.arity + 1)}
    (first : TypeReadout context domainCode domain)
    (second : TypeReadout (QuotientCwf.ext context domain) bodyCode codomain) :
    TypeReadout context (.sigma domainCode bodyCode) (Sums.sigma domain codomain) := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyRead, bodyClass⟩
  refine ⟨rawSigma annotation (authoredBody annotation domainClass body), ?_, ?_⟩
  · change TypeExpr.sigma annotation.code (authoredBody annotation domainClass body).code = _
    rw [authoredBody_code, codeRead, bodyRead]
  · apply (QType.mk_eq_iff _ _).mpr
    exact typeEquality_symm (rawSigma_typeEquality _ _ (domain_equality annotation domainClass) _ _
      (body_equality annotation domainClass body bodyClass))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
