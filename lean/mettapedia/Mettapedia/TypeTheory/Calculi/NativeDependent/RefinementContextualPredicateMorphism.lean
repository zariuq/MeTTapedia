import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualConstructorReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateInterpretation

/-!
# Predicate and ordinary proposition preservation by interpretation

The semantic map on actual generated predicate classes preserves their
Heyting operations and the two display quantifiers. Ordinary propositions
retain their independently interpreted quotient terms. Chosen assumption
contexts are compared through their actual successful mixed-context readout.
The source predicates remain generated definable predicates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open QuotientComprehensionSyntax
open Refinement.Abstract

universe u c s t m p
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}
variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

theorem predicateValue_top (context : Context D) :
    predicateValue model (⊤ : QPredicate context) = ⊤ :=
  Option.some.inj ((predicate_readout model (Logic.truth context)).symm.trans
    (model.data.evaluate_truth (contextValue model context)))

theorem predicateValue_bot (context : Context D) :
    predicateValue model (⊥ : QPredicate context) = ⊥ :=
  Option.some.inj ((predicate_readout model (Logic.falsehood context)).symm.trans
    (model.data.evaluate_falsehood (contextValue model context)))

theorem predicateValue_inf {context : Context D} (first second : QPredicate context) :
    predicateValue model (first ⊓ second) =
      predicateValue model first ⊓ predicateValue model second := by
  refine _root_.Quotient.inductionOn₂ first second fun left right => ?_
  exact Option.some.inj ((predicate_readout model (Logic.conjunction left right)).symm.trans
    (model.data.evaluate_and (contextValue model context) left.code right.code
      (rawPredicate model left) (rawPredicate model right)
      (predicate_readout model left) (predicate_readout model right)))

theorem predicateValue_sup {context : Context D} (first second : QPredicate context) :
    predicateValue model (first ⊔ second) =
      predicateValue model first ⊔ predicateValue model second := by
  refine _root_.Quotient.inductionOn₂ first second fun left right => ?_
  exact Option.some.inj ((predicate_readout model (Logic.disjunction left right)).symm.trans
    (model.data.evaluate_or (contextValue model context) left.code right.code
      (rawPredicate model left) (rawPredicate model right)
      (predicate_readout model left) (predicate_readout model right)))

theorem predicateValue_himp {context : Context D} (first second : QPredicate context) :
    predicateValue model (first ⇨ second) =
      predicateValue model first ⇨ predicateValue model second := by
  refine _root_.Quotient.inductionOn₂ first second fun left right => ?_
  exact Option.some.inj ((predicate_readout model (Logic.implication left right)).symm.trans
    (model.data.evaluate_implies (contextValue model context) left.code right.code
      (rawPredicate model left) (rawPredicate model right)
      (predicate_readout model left) (predicate_readout model right)))

noncomputable def predicateHom (context : Context D) :
    HeytingHom (QPredicate context)
      (model.localModel.doctrine.Predicate (contextValue model context).1) where
  toFun := predicateValue model
  map_inf' := predicateValue_inf model
  map_sup' := predicateValue_sup model
  map_bot' := predicateValue_bot model context
  map_himp' := predicateValue_himp model

theorem predicateHom_natural {source target : quotientContext D}
    (substitution : source ⟶ target) (predicate : QPredicate target.as) :
    predicateHom model source.as (PredicateAction.reindex substitution predicate) =
      model.localModel.doctrine.reindex ((quotientFunctor model).map substitution)
        (predicateHom model target.as predicate) :=
  predicate_substitution model predicate substitution

theorem predicate_readout_transport {n : Nat}
    {first second : Abstract.ModelScope C model.localModel n}
    (contexts : first = second) (code : PropExpr S n)
    {left : model.localModel.doctrine.Predicate first.1}
    {right : model.localModel.doctrine.Predicate second.1} (predicates : HEq left right)
    (read : model.data.evaluatePredicate first code = some left) :
    model.data.evaluatePredicate second code = some right := by
  cases contexts
  cases eq_of_heq predicates
  exact read

theorem represented_predicate_readout {context : QuotientCwf.QContext D}
    (predicate : QPredicate context.as) :
    model.data.evaluatePredicate (contextValue model context.as)
      (AssumptionModel.chosen predicate).code = some (predicateValue model predicate) :=
  (predicate_readout model (AssumptionModel.chosen predicate)).trans
    (congrArg some (congrArg (predicateValue model) (AssumptionModel.chosen_class predicate)))

theorem represented_predicate_body_readout {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (body : QPredicate (QuotientCwf.ext context domain).as)
    (predicate : model.localModel.doctrine.Predicate
      (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (predicates : HEq (predicateValue model body) predicate) :
    model.data.evaluatePredicate ((contextValue model context.as).snoc (typeValue model domain))
      (AssumptionModel.chosen body).code = some predicate :=
  predicate_readout_transport model (represented_extension model domain) _ predicates
    (represented_predicate_readout model body)

theorem all_value {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (body : QPredicate (QuotientCwf.ext context domain).as)
    (predicate : model.localModel.doctrine.Predicate
      (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (predicates : HEq (predicateValue model body) predicate) :
    predicateValue model (Quantifiers.all domain body) =
      model.localModel.doctrine.all (typeValue model domain) predicate := by
  have computes := model.data.evaluate_all (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (AssumptionModel.chosen body).code
    (typeValue model domain) predicate (represented_type_readout model domain)
    (represented_predicate_body_readout model domain body predicate predicates)
  have represented : QPredicate.mk (Quantifiers.rawForall
      (QuotientCwf.typeRepresentative domain) (AssumptionModel.chosen body)) =
        Quantifiers.all domain body :=
    congrArg (Quantifiers.forallAt (QuotientCwf.typeRepresentative domain))
      (AssumptionModel.chosen_class body)
  exact (congrArg (predicateValue model) represented).symm.trans
    (Option.some.inj ((predicate_readout model (Quantifiers.rawForall
      (QuotientCwf.typeRepresentative domain) (AssumptionModel.chosen body))).symm.trans computes))

theorem some_value {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context)
    (body : QPredicate (QuotientCwf.ext context domain).as)
    (predicate : model.localModel.doctrine.Predicate
      (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (predicates : HEq (predicateValue model body) predicate) :
    predicateValue model (Quantifiers.some domain body) =
      model.localModel.doctrine.some (typeValue model domain) predicate := by
  have computes := model.data.evaluate_exists (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (AssumptionModel.chosen body).code
    (typeValue model domain) predicate (represented_type_readout model domain)
    (represented_predicate_body_readout model domain body predicate predicates)
  have represented : QPredicate.mk (Quantifiers.rawExists
      (QuotientCwf.typeRepresentative domain) (AssumptionModel.chosen body)) =
        Quantifiers.some domain body :=
    congrArg (Quantifiers.existsAt (QuotientCwf.typeRepresentative domain))
      (AssumptionModel.chosen_class body)
  exact (congrArg (predicateValue model) represented).symm.trans
    (Option.some.inj ((predicate_readout model (Quantifiers.rawExists
      (QuotientCwf.typeRepresentative domain) (AssumptionModel.chosen body))).symm.trans computes))

theorem omega_value (context : QuotientCwf.QContext D) :
    typeValue model (PropositionModel.omega context) =
      model.localModel.propositions.omega (contextValue model context.as).1 :=
  Option.some.inj ((type_readout model (propositionsType context.as)).symm.trans
    (model.data.evaluate_propositions (contextValue model context.as)))

theorem quote_value {context : QuotientCwf.QContext D} (predicate : QPredicate context.as) :
    HEq (termValue model (PropositionModel.quote predicate))
      (model.localModel.propositions.quote (predicateValue model predicate)) := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  have actual : QTerm.mk (quotePredicate formed) = (PropositionModel.quote (QPredicate.mk formed)).val :=
    rfl
  have first := represented_term_readout model (PropositionModel.quote (QPredicate.mk formed))
    (quotePredicate formed) actual
  have second := model.data.evaluate_quote (contextValue model context.as) formed.code
    (rawPredicate model formed) (predicate_readout model formed)
  exact (Sigma.mk.inj (Option.some.inj (first.symm.trans second))).2

theorem holds_value {context : QuotientCwf.QContext D}
    (term : QuotientCwf.Tm context (PropositionModel.omega context))
    (value : C.toCwf.Tm (contextValue model context.as).1
      (model.localModel.propositions.omega (contextValue model context.as).1))
    (terms : HEq (termValue model term) value) :
    predicateValue model (PropositionModel.holds term) = model.localModel.propositions.holds value := by
  have quotation := quote_value model (PropositionModel.holds term)
  rw [PropositionModel.quote_holds] at quotation
  have quotes : model.localModel.propositions.quote
      (predicateValue model (PropositionModel.holds term)) = value :=
    eq_of_heq (quotation.symm.trans terms)
  calc
    _ = model.localModel.propositions.holds (model.localModel.propositions.quote
        (predicateValue model (PropositionModel.holds term))) :=
      (model.localModel.propositions.holds_quote _).symm
    _ = _ := congrArg model.localModel.propositions.holds quotes

theorem context_assumption (context : Context D) (predicate : PredicateOver context) :
    contextValue model (assumed context predicate) =
      (contextValue model context).assume (rawPredicate model predicate) :=
  Abstract.Derivation.contextValue_unique model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice (assumed context predicate).formed.judgment) _
      (model.data.evaluateContext_assume context.raw predicate.code _ _
        (context_readout model context) (predicate_readout model predicate))

theorem represented_assumption (context : QuotientCwf.QContext D) (predicate : QPredicate context.as) :
    contextValue model (AssumptionModel.selected context predicate).as =
      (contextValue model context.as).assume (predicateValue model predicate) := by
  have represented : rawPredicate model (AssumptionModel.chosen predicate) =
      predicateValue model predicate :=
    congrArg (predicateValue model) (AssumptionModel.chosen_class predicate)
  exact (context_assumption model context.as (AssumptionModel.chosen predicate)).trans
    (congrArg (Mettapedia.TypeTheory.ContextualPredicateModelScopes.Scope.assume
      (contextValue model context.as)) represented)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
