import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicateMorphism

/-!
# Assumption inclusions under contextual interpretation

The independently evaluated substitution of an authored assumption inclusion
is the supplied target inclusion. The comparison uses every retained variable
of the mixed scope, including variables preceding assumption binders.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Refinement.Abstract

universe u c s t m p
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}
variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

theorem raw_assumption_inclusion_heq (context : Context D) (predicate : PredicateOver context) :
    HEq (rawArrow model (assumptionInclusion context predicate))
      (model.localModel.assumptions.inclusion (rawPredicate model predicate)) := by
  apply evaluated_arrows_heq model (context_assumption model context predicate)
    TermExpr.var (arrow_readout model (assumptionInclusion context predicate))
  exact (model.data.evaluateSubstitution_eq_some_iff _ _ _ _).mpr (fun _ => rfl)

theorem inclusion_predicate_heq {context : C.toCwf.Ctx}
    {first second : model.localModel.doctrine.Predicate context} (predicates : first = second) :
    HEq (model.localModel.assumptions.inclusion first)
      (model.localModel.assumptions.inclusion second) := by
  cases predicates
  rfl

theorem assumption_inclusion_value {context : QuotientCwf.QContext D}
    (predicate : QPredicate context.as) :
    HEq ((quotientFunctor model).map (AssumptionModel.inclusion predicate))
      (model.localModel.assumptions.inclusion (predicateValue model predicate)) := by
  change HEq (rawArrow model (assumptionInclusion context.as (AssumptionModel.chosen predicate))) _
  exact (raw_assumption_inclusion_heq model context.as (AssumptionModel.chosen predicate)).trans
    (inclusion_predicate_heq model
      (congrArg (predicateValue model) (AssumptionModel.chosen_class predicate)))

theorem assumption_context_value (context : QuotientCwf.QContext D) (predicate : QPredicate context.as) :
    (contextValue model (AssumptionModel.selected context predicate).as).1 =
      model.localModel.assumptions.assumed (contextValue model context.as).1
        (predicateValue model predicate) :=
  congrArg Sigma.fst (represented_assumption model context predicate)

theorem assumption_inclusion_square (context : QuotientCwf.QContext D) (predicate : QPredicate context.as) :
    (quotientFunctor model).map (AssumptionModel.inclusion predicate) =
      eqToHom (congrArg ContextualBase.Context.mk (assumption_context_value model context predicate)) ≫
        model.localModel.assumptions.inclusion (predicateValue model predicate) :=
  hom_eq_of_source_heq (congrArg ContextualBase.Context.mk (assumption_context_value model context predicate))
    _ _ (assumption_inclusion_value model predicate)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
