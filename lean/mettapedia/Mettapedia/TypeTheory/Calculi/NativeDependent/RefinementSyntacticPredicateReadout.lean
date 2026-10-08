import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticTypeReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualImages

/-!
# Generated predicate and ordinary-proposition readouts

The chosen source operations recover authored logical codes by the actual
generated predicate equations. Quantified bodies are transported through the
domain comparison before their annotations are read back. Quotation and
predicate readout compare complete proposition sections; logical type images
are recovered as existential support without choosing a data inhabitant.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open QuotientComprehensionSyntax

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem propositions_readout (context : QuotientCwf.QContext D) :
    TypeReadout context .propositions (PropositionModel.omega context) :=
  ⟨propositionsType context.as, rfl, rfl⟩

theorem truth_readout (context : QuotientCwf.QContext D) : PredicateReadout context .truth ⊤ :=
  ⟨Logic.truth context.as, rfl, rfl⟩

theorem falsehood_readout (context : QuotientCwf.QContext D) : PredicateReadout context .falsehood ⊥ :=
  ⟨Logic.falsehood context.as, rfl, rfl⟩

theorem conjunction_readout {context : QuotientCwf.QContext D}
    {firstCode secondCode : PropExpr S context.as.arity} {first second : QPredicate context.as}
    (left : PredicateReadout context firstCode first) (right : PredicateReadout context secondCode second) :
    PredicateReadout context (.and firstCode secondCode) (first ⊓ second) := by
  rcases left with ⟨firstRaw, firstCodeRead, firstClass⟩
  rcases right with ⟨secondRaw, secondCodeRead, secondClass⟩
  refine ⟨Logic.conjunction firstRaw secondRaw, ?_, ?_⟩
  · change PropExpr.and firstRaw.code secondRaw.code = _
    rw [firstCodeRead, secondCodeRead]
  · rw [← firstClass, ← secondClass]
    rfl

theorem disjunction_readout {context : QuotientCwf.QContext D}
    {firstCode secondCode : PropExpr S context.as.arity} {first second : QPredicate context.as}
    (left : PredicateReadout context firstCode first) (right : PredicateReadout context secondCode second) :
    PredicateReadout context (.or firstCode secondCode) (first ⊔ second) := by
  rcases left with ⟨firstRaw, firstCodeRead, firstClass⟩
  rcases right with ⟨secondRaw, secondCodeRead, secondClass⟩
  refine ⟨Logic.disjunction firstRaw secondRaw, ?_, ?_⟩
  · change PropExpr.or firstRaw.code secondRaw.code = _
    rw [firstCodeRead, secondCodeRead]
  · rw [← firstClass, ← secondClass]
    rfl

theorem implication_readout {context : QuotientCwf.QContext D}
    {firstCode secondCode : PropExpr S context.as.arity} {first second : QPredicate context.as}
    (left : PredicateReadout context firstCode first) (right : PredicateReadout context secondCode second) :
    PredicateReadout context (.implies firstCode secondCode) (first ⇨ second) := by
  rcases left with ⟨firstRaw, firstCodeRead, firstClass⟩
  rcases right with ⟨secondRaw, secondCodeRead, secondClass⟩
  refine ⟨Logic.implication firstRaw secondRaw, ?_, ?_⟩
  · change PropExpr.implies firstRaw.code secondRaw.code = _
    rw [firstCodeRead, secondCodeRead]
  · rw [← firstClass, ← secondClass]
    rfl

noncomputable def authoredPredicate {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    (body : PredicateOver (QuotientCwf.ext context domain).as) :
    PredicateOver (extend context.as annotation) :=
  body.reindex (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
    (domain_equality annotation same)).inv

set_option backward.isDefEq.respectTransparency false in
theorem authoredPredicate_code {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    (body : PredicateOver (QuotientCwf.ext context domain).as) :
    (authoredPredicate annotation same body).code = body.code := by
  change body.code.substitute
    (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
      (domain_equality annotation same)).inv.substitution = body.code
  rw [extensionComparison_inv_substitution]
  exact PropExpr.substitute_identity body.code

set_option backward.isDefEq.respectTransparency false in
theorem authoredPredicate_roundtrip {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (annotation : TypeOver context.as) (same : QType.mk annotation = domain)
    (body : PredicateOver (QuotientCwf.ext context domain).as) :
    (authoredPredicate annotation same body).reindex
      (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
        (domain_equality annotation same)).hom = body := by
  apply PredicateOver.ext
  change (authoredPredicate annotation same body).code.substitute
    (extensionComparison (QuotientCwf.typeRepresentative domain) annotation
      (domain_equality annotation same)).hom.substitution = body.code
  rw [authoredPredicate_code, extensionComparison_hom_substitution]
  exact PropExpr.substitute_identity body.code

theorem universal_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : PropExpr S (context.as.arity + 1)}
    {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (first : TypeReadout context domainCode domain)
    (second : PredicateReadout (QuotientCwf.ext context domain) bodyCode predicate) :
    PredicateReadout context (.all domainCode bodyCode) (Quantifiers.all domain predicate) := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyRead, bodyClass⟩
  refine ⟨Quantifiers.rawForall annotation (authoredPredicate annotation domainClass body), ?_, ?_⟩
  · change PropExpr.all annotation.code (authoredPredicate annotation domainClass body).code = _
    rw [authoredPredicate_code, codeRead, bodyRead]
  · exact (Quantifiers.forallAt_compared (QuotientCwf.typeRepresentative domain) annotation
      (domain_equality annotation domainClass) predicate
      (QPredicate.mk (authoredPredicate annotation domainClass body))
      (by rw [QPredicate.reindex_mk, authoredPredicate_roundtrip]; exact bodyClass.symm)).symm

theorem existential_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : PropExpr S (context.as.arity + 1)}
    {predicate : QPredicate (QuotientCwf.ext context domain).as}
    (first : TypeReadout context domainCode domain)
    (second : PredicateReadout (QuotientCwf.ext context domain) bodyCode predicate) :
    PredicateReadout context (.exists domainCode bodyCode) (Quantifiers.some domain predicate) := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyRead, bodyClass⟩
  refine ⟨Quantifiers.rawExists annotation (authoredPredicate annotation domainClass body), ?_, ?_⟩
  · change PropExpr.exists annotation.code (authoredPredicate annotation domainClass body).code = _
    rw [authoredPredicate_code, codeRead, bodyRead]
  · exact (Quantifiers.existsAt_compared (QuotientCwf.typeRepresentative domain) annotation
      (domain_equality annotation domainClass) predicate
      (QPredicate.mk (authoredPredicate annotation domainClass body))
      (by rw [QPredicate.reindex_mk, authoredPredicate_roundtrip]; exact bodyClass.symm)).symm

theorem quote_readout {context : QuotientCwf.QContext D} {code : PropExpr S context.as.arity}
    {predicate : QPredicate context.as} (readout : PredicateReadout context code predicate) :
    TermReadout context (.quote code)
      ⟨PropositionModel.omega context, PropositionModel.quote predicate⟩ := by
  rcases readout with ⟨actual, codeRead, classes⟩
  refine ⟨propositionsType context.as, quotePredicate actual, ?_, ?_⟩
  · change TermExpr.quote actual.code = _
    rw [codeRead]
  · rw [← classes]
    rfl

theorem holds_supplied_class {context : QuotientCwf.QContext D}
    (term : Term context.as (propositionsType context.as)) :
    PropositionModel.holds (⟨QTerm.mk term, rfl⟩ : QuotientCwf.Tm context (PropositionModel.omega context)) =
      QPredicate.mk (holdsProposition term) := by
  apply (PropositionModel.equivalence context).injective
  change PropositionModel.quote (PropositionModel.holds _) = PropositionModel.quote _
  rw [PropositionModel.quote_holds]
  apply Subtype.ext
  change QTerm.mk term = QTerm.mk (quotePredicate (holdsProposition term))
  apply (QTerm.mk_eq_iff _ _).mpr
  exact ⟨typeEquality_refl (propositionsType context.as),
    termEquality_symm (conclude (.quoteHolds context.as.raw term.code) ⟨term.typed, trivial⟩)⟩

theorem holds_readout {context : QuotientCwf.QContext D} {code : TermExpr S context.as.arity}
    (term : QuotientCwf.Tm context (PropositionModel.omega context))
    (readout : TermReadout context code ⟨PropositionModel.omega context, term⟩) :
    PredicateReadout context (.holds code) (PropositionModel.holds term) := by
  rcases retype readout (propositionsType context.as) rfl with ⟨actual, codeRead, classes⟩
  have sections : (⟨QTerm.mk actual, rfl⟩ : QuotientCwf.Tm context (PropositionModel.omega context)) = term :=
    Subtype.ext classes
  refine ⟨holdsProposition actual, ?_, ?_⟩
  · change PropExpr.holds actual.code = _
    rw [codeRead]
  · exact (holds_supplied_class actual).symm.trans (congrArg PropositionModel.holds sections)

theorem image_readout {context : QuotientCwf.QContext D} {code : TypeExpr S context.as.arity}
    {domain : QuotientCwf.Ty context} (readout : TypeReadout context code domain) :
    PredicateReadout context (.image code) (Quantifiers.some domain ⊤) := by
  rcases readout with ⟨annotation, codeRead, classes⟩
  refine ⟨Quantifiers.rawImage annotation, ?_, ?_⟩
  · change PropExpr.image annotation.code = _
    rw [codeRead]
  · calc
      _ = Quantifiers.existsAt annotation ⊤ := Quantifiers.image_support annotation
      _ = Quantifiers.existsAt (QuotientCwf.typeRepresentative domain) ⊤ :=
        (Quantifiers.existsAt_compared _ _ (domain_equality annotation classes) ⊤ ⊤
          (Logic.top_reindex _).symm).symm
      _ = _ := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
