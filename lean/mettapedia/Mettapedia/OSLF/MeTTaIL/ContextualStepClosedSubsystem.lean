import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Closed operation subsystems of contextual rule execution

A rule-data service whose recursive calls remain in its own operation heads
has exactly the same results after disjoint operation rules are added. This
is a result about the actual recursive interpreter, including output order
and multiplicity, not an assumed equivalence of services.
-/

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Syntax Match ReflectiveCanonical ReflectiveSubstitution

def HasOperationHead (names : List String) : Pattern → Prop
  | .apply name _ => name ∈ names
  | _ => False

def CallsWithin (names : List String) : List Premise → Prop
  | [] => True
  | .congruence source _ :: rest =>
      HasOperationHead names source ∧ CallsWithin names rest
  | _ :: _ => False

instance (names : List String) (source : Pattern) :
    Decidable (HasOperationHead names source) := by
  cases source <;> unfold HasOperationHead <;> infer_instance

instance (names : List String) (premises : List Premise) :
    Decidable (CallsWithin names premises) := by
  induction premises with
  | nil => unfold CallsWithin; infer_instance
  | cons premise rest ih =>
    cases premise <;> unfold CallsWithin <;> infer_instance

theorem HasOperationHead.applyBindings {names : List String} {source : Pattern}
    (closed : HasOperationHead names source) (bindings : Bindings) :
    HasOperationHead names (applyBindings bindings source) := by
  cases source <;> simp_all [HasOperationHead, Match.applyBindings]

theorem matchPattern_eq_nil_of_disjoint_operationHeads
    {leftNames rightNames : List String} {pattern source : Pattern}
    (left : HasOperationHead leftNames pattern)
    (right : HasOperationHead rightNames source)
    (distinct : ∀ a ∈ leftNames, ∀ b ∈ rightNames, a ≠ b) :
    matchPattern pattern source = [] := by
  cases pattern <;> simp only [HasOperationHead] at left
  case apply first arguments =>
    cases source <;> simp only [HasOperationHead] at right
    case apply second terms =>
      simp [matchPattern, distinct first left second right]

theorem premisesUsing_eq_of_callsWithin
    {names : List String} {base₁ base₂ : BasePremiseEvaluator}
    {lang₁ lang₂ : LanguageDef} {first second : Pattern → List Pattern}
    (same : ∀ source, HasOperationHead names source → first source = second source)
    (premises : List Premise) (closed : CallsWithin names premises)
    (bindings : Bindings) :
    premisesUsing base₁ lang₁ first premises bindings =
      premisesUsing base₂ lang₂ second premises bindings := by
  induction premises generalizing bindings with
  | nil => rfl
  | cons premise rest ih =>
    cases premise <;> simp only [CallsWithin] at closed
    case congruence source target =>
      simp only [premisesUsing, premiseStepUsing,
        same _ (closed.1.applyBindings bindings)]
      congr 1
      funext result
      exact ih closed.2 result

theorem applyRuleUsing_eq_of_callsWithin
    {names : List String} {base₁ base₂ : BasePremiseEvaluator}
    {lang₁ lang₂ : LanguageDef} {first second : Pattern → List Pattern}
    (same : ∀ source, HasOperationHead names source → first source = second source)
    (rule : RewriteRule) (closed : CallsWithin names rule.premises)
    (source : Pattern) :
    applyRuleUsing base₁ lang₁ first rule source =
      applyRuleUsing base₂ lang₂ second rule source := by
  simp only [applyRuleUsing, matchPatternForRule_eq_syntactic,
    applyBindingsForRule, applyBindingsForRuleUsing_empty]
  congr 1
  funext bindings
  rw [premisesUsing_eq_of_callsWithin same rule.premises closed bindings]

theorem rewriteAt_closed_extension
    (names : List String) (original extended : LanguageDef)
    (extra : List RewriteRule) (base₁ base₂ : BasePremiseEvaluator)
    (rules : extended.rewrites = original.rewrites ++ extra)
    (closed : ∀ rule ∈ original.rewrites, CallsWithin names rule.premises)
    (disjoint : ∀ source, HasOperationHead names source →
      ∀ rule ∈ extra, matchPattern rule.left source = [])
    (fuel : Nat) (source : Pattern) (head : HasOperationHead names source) :
    rewriteAt base₁ original fuel source = rewriteAt base₂ extended fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    simp only [rewriteAt, rules, List.flatMap_append]
    have extraEmpty : extra.flatMap
        (fun rule => applyRuleUsing base₂ extended
          (rewriteAt base₂ extended fuel) rule source) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro rule member
      simp [applyRuleUsing, matchPatternForRule_eq_syntactic,
        disjoint source head rule member]
    rw [extraEmpty, List.append_nil]
    apply List.flatMap_congr
    intro rule member
    exact applyRuleUsing_eq_of_callsWithin ih rule (closed rule member) source

end Mettapedia.OSLF.MeTTaIL.ContextualStep
