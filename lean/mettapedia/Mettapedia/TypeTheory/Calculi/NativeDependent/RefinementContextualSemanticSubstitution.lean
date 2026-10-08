import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualSemanticFunctor
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicateAction

/-!
# Semantic substitution of generated families, sections and predicates

The independently evaluated ordered substitution commutes with the actual
source quotient actions. The comparison retains the semantic section and
its dependent annotation, and acts on definable predicates as well.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Refinement.Abstract

universe u c s t m p
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}
variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

noncomputable def arrowSubstitution {source target : Context D} (morphism : source ⟶ target) :
    ModelSubstitution model.data (contextValue model source) (contextValue model target)
      morphism.substitution :=
  ModelSubstitution.ofEvaluated model.data _ _ _ _ (arrow_readout model morphism)

theorem rawType_reindex {source target : Context D} (type : TypeOver target)
    (morphism : source ⟶ target) :
    rawType model (type.reindex morphism) = C.toCwf.tySub (rawType model type) (rawArrow model morphism) :=
  Abstract.Derivation.typeValue_unique model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice (type.reindex morphism).formed)
      _ (context_readout model source) _
        (model.data.evaluateType_substitute model.products_substitution type.code _ _
          morphism.substitution (arrowSubstitution model morphism) _ (type_readout model type))

theorem rawTotal_reindex {source target : Context D} (term : TotalTerm target)
    (morphism : source ⟶ target) :
    rawTotal model (term.reindex morphism) = (rawTotal model term).substitute (rawArrow model morphism) :=
  Option.some.inj ((term_readout model (term.2.reindex morphism)).symm.trans
    (model.data.evaluateTerm_substitute model.products_substitution term.2.code _ _
      morphism.substitution (arrowSubstitution model morphism) _ (term_readout model term.2)))

theorem rawPredicate_reindex {source target : Context D} (predicate : PredicateOver target)
    (morphism : source ⟶ target) :
    rawPredicate model (predicate.reindex morphism) =
      model.localModel.doctrine.reindex (rawArrow model morphism) (rawPredicate model predicate) :=
  Abstract.Derivation.predicateValue_unique model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice (predicate.reindex morphism).formed)
      _ (context_readout model source) _
        (model.data.evaluatePredicate_substitute model.products_substitution predicate.code _ _
          morphism.substitution (arrowSubstitution model morphism) _ (predicate_readout model predicate))

theorem typeValue_reindex {source target : Context D} (type : QType target)
    (morphism : source ⟶ target) :
    typeValue model (type.reindex morphism) = C.toCwf.tySub (typeValue model type) (rawArrow model morphism) := by
  induction type using _root_.Quotient.inductionOn with
  | h representative => exact rawType_reindex model representative morphism

theorem totalValue_reindex {source target : Context D} (term : QTerm target)
    (morphism : source ⟶ target) :
    totalValue model (term.reindex morphism) = (totalValue model term).substitute (rawArrow model morphism) := by
  induction term using _root_.Quotient.inductionOn with
  | h representative => exact rawTotal_reindex model representative morphism

theorem predicateValue_reindex {source target : Context D} (predicate : QPredicate target)
    (morphism : source ⟶ target) :
    predicateValue model (predicate.reindex morphism) =
      model.localModel.doctrine.reindex (rawArrow model morphism) (predicateValue model predicate) := by
  induction predicate using _root_.Quotient.inductionOn with
  | h representative => exact rawPredicate_reindex model representative morphism

theorem type_substitution {source target : quotientContext D} (type : QType target.as)
    (morphism : source ⟶ target) :
    typeValue model (QuotientCwf.tySub type morphism) =
      C.toCwf.tySub (typeValue model type) ((quotientFunctor model).map morphism) := by
  induction morphism using Quot.inductionOn with
  | h representative => exact typeValue_reindex model type representative

theorem total_substitution {source target : quotientContext D} (term : QTerm target.as)
    (morphism : source ⟶ target) :
    totalValue model (QuotientCwf.totalSub term morphism) =
      (totalValue model term).substitute ((quotientFunctor model).map morphism) := by
  induction morphism using Quot.inductionOn with
  | h representative => exact totalValue_reindex model term representative

theorem predicate_substitution {source target : quotientContext D} (predicate : QPredicate target.as)
    (morphism : source ⟶ target) :
    predicateValue model (PredicateAction.reindex morphism predicate) =
      model.localModel.doctrine.reindex ((quotientFunctor model).map morphism)
        (predicateValue model predicate) := by
  induction morphism using Quot.inductionOn with
  | h representative => exact predicateValue_reindex model predicate representative

theorem term_substitution {source target : quotientContext D} {type : QType target.as}
    (term : QuotientCwf.Tm target type) (morphism : source ⟶ target) :
    HEq (termValue model (QuotientCwf.tmSub term morphism))
      (C.toCwf.tmSub (termValue model term) ((quotientFunctor model).map morphism)) := by
  have values := total_substitution model term.val morphism
  have types := (totalValue_type model term.val).trans (congrArg (typeValue model) term.property)
  exact (termValue_retains_section model (QuotientCwf.tmSub term morphism)).trans
    ((Sigma.mk.inj values).2.trans
      (TypeOver.tmSub_heq types (termValue_retains_section model term).symm
        ((quotientFunctor model).map morphism)))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
