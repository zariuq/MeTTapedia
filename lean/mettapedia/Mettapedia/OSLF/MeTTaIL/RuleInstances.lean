import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Steps of a theory whose rules carry no premise

When no rule of a language carries a premise and no rule moves a metavariable
across a binder, a step is nothing but an instance of a rule: the left side
matches the source, and the target is the right side under the same bindings.
When the left sides are matched exactly, the source is the left side under
those bindings as well, so a step is a pair of instances of the two sides of
one rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- The rules of the language carry no premise and move no metavariable
across a binder. -/
def PlainRules (lang : LanguageDef) : Prop :=
  ∀ rule ∈ lang.rewrites, rule.premises = [] ∧ ruleDepthAligned rule = true

/-- A step of a plain-rule language is a rule whose left side matches the
source and whose right side, under the same bindings, is the target. -/
theorem step_iff_exists_match {relEnv : RelationEnv} {lang : LanguageDef}
    (plain : PlainRules lang) {source target : Pattern} :
    Step (engineBasePremises relEnv) lang source target ↔
      ∃ rule ∈ lang.rewrites, ∃ bindings ∈ matchPattern rule.left source,
        applyBindings bindings rule.right = target := by
  rw [step_iff_rootStep_of_noncontextualRules (fun rule membership => by
    rw [(plain rule membership).1]
    exact .nil)]
  constructor
  · rintro ⟨rule, ruleMember, initial, matched, final, premises, targetEq⟩
    rw [(plain rule ruleMember).1] at premises
    obtain rfl : final = initial := by simpa [applyPremisesWithEnv] using premises
    refine ⟨rule, ruleMember, final, by simpa using matched, ?_⟩
    rw [← targetEq]
    exact (applyBindingsForRuleUsing_empty_eq_applyBindings rule final
      (plain rule ruleMember).2).symm
  · rintro ⟨rule, ruleMember, bindings, matched, targetEq⟩
    refine ⟨rule, ruleMember, bindings, by simpa using matched, bindings, ?_, ?_⟩
    · rw [(plain rule ruleMember).1]
      simp [applyPremisesWithEnv]
    · rw [← targetEq]
      exact applyBindingsForRuleUsing_empty_eq_applyBindings rule bindings
        (plain rule ruleMember).2

/-- With left sides matched exactly, a step is the two sides of one rule
under one substitution. -/
theorem sides_of_step {relEnv : RelationEnv} {lang : LanguageDef}
    (plain : PlainRules lang)
    (exact : ∀ rule ∈ lang.rewrites, Pattern.isMatchCorrect rule.left = true)
    {source target : Pattern}
    (step : Step (engineBasePremises relEnv) lang source target) :
    ∃ rule ∈ lang.rewrites, ∃ bindings : Bindings,
      source = applyBindings bindings rule.left ∧
        target = applyBindings bindings rule.right := by
  obtain ⟨rule, ruleMember, bindings, matched, targetEq⟩ :=
    (step_iff_exists_match plain).mp step
  exact ⟨rule, ruleMember, bindings,
    (matchPattern_correct matched (exact rule ruleMember)).symm, targetEq.symm⟩

end Mettapedia.OSLF.MeTTaIL.ContextualStep
