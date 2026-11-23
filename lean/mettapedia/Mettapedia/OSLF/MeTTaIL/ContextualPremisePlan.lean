import Mettapedia.OSLF.MeTTaIL.ContextualStep

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- An exact, deterministic path through an ordered premise list. Each
successful step retains the bindings for the next one. A failed step
determines the result independently of the remaining premises. -/
inductive PremisePlan (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recur : Pattern → List Pattern) :
    Bindings → List Premise → Option Bindings → Prop where
  | done (bindings : Bindings) :
      PremisePlan base lang recur bindings [] (some bindings)
  | advance {before after : Bindings} {premise : Premise}
      {rest : List Premise} {result : Option Bindings}
      (step : premiseStepUsing base lang recur before premise = [after])
      (tail : PremisePlan base lang recur after rest result) :
      PremisePlan base lang recur before (premise :: rest) result
  | reject {before : Bindings} {premise : Premise} {rest : List Premise}
      (step : premiseStepUsing base lang recur before premise = []) :
      PremisePlan base lang recur before (premise :: rest) none

theorem PremisePlan.evaluate
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {recur : Pattern → List Pattern} {before : Bindings}
    {premises : List Premise} {result : Option Bindings}
    (plan : PremisePlan base lang recur before premises result) :
    premisesUsing base lang recur premises before = result.toList := by
  induction plan with
  | done => rfl
  | advance step _ ih =>
      simp only [premisesUsing, step, List.flatMap_singleton, ih]
  | reject step => simp only [premisesUsing, step, List.flatMap_nil]; rfl

/-- A rejecting prefix excludes every continuation of that row. -/
theorem PremisePlan.append_rejected
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {recur : Pattern → List Pattern} {before : Bindings} {stages : List Premise}
    (plan : PremisePlan base lang recur before stages none) (suffix : List Premise) :
    PremisePlan base lang recur before (stages ++ suffix) none := by
  induction stages generalizing before with
  | nil => cases plan
  | cons _ _ ih =>
      cases plan with
      | advance step tail => exact .advance step (ih tail)
      | reject step => exact .reject step

/-- Exact row readout given a unique left match and a premise plan. This
preserves the exact ordered output list, including the empty case. -/
theorem applyRuleUsing_eq_of_plan
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {recur : Pattern → List Pattern} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings} {result : Option Bindings}
    (matched : matchPatternForRule lang rule term = [bindings])
    (plan : PremisePlan base lang recur bindings rule.premises result) :
    applyRuleUsing base lang recur rule term =
      result.toList.map (applyBindingsForRule lang rule) := by
  simp only [applyRuleUsing, matched, List.flatMap_singleton, plan.evaluate]

theorem applyRuleUsing_eq_nil_of_rejected_prefix
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    {recur : Pattern → List Pattern} {rule : RewriteRule} {term : Pattern}
    {bindings : Bindings} {stages : List Premise}
    (matched : matchPatternForRule lang rule term = [bindings])
    (prefixExact : rule.premises.take stages.length = stages)
    (plan : PremisePlan base lang recur bindings stages none) :
    applyRuleUsing base lang recur rule term = [] := by
  apply applyRuleUsing_eq_of_plan matched (result := none)
  have decomposed : rule.premises = stages ++ rule.premises.drop stages.length := by
    calc
      _ = rule.premises.take stages.length ++ rule.premises.drop stages.length :=
        (List.take_append_drop stages.length rule.premises).symm
      _ = _ := congrArg (· ++ rule.premises.drop stages.length) prefixExact
  rw [decomposed]
  exact plan.append_rejected _

#print axioms applyRuleUsing_eq_of_plan
#print axioms applyRuleUsing_eq_nil_of_rejected_prefix

end Mettapedia.OSLF.MeTTaIL.ContextualStep
