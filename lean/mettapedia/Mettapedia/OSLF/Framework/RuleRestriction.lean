import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction

/-!
# Restricting a language definition to some of its rules

A `LanguageDef` restricted to some of its rewrite rules is again a `LanguageDef`
with the same sorts, constructors and equations (`LanguageDef.restrictRewrites`).
The OSLF construction applies to it unchanged, so every rule has its own generated
step-future modality: the diamond of the restriction to that rule (`ruleDiamond`).
Dynamic logic's action-indexed possibility `⟨α⟩` is this modality at the rule `α`.

* Restriction keeps equation-freeness, and its steps are steps of the whole
  language (`step_of_restrictRewrites`), so a rule's diamond implies the
  language's (`ruleDiamond_le_generatedDiamond`).
* For a rule without premises that places its right side without shifting, its
  diamond is membership of the rule together with a match of its left side
  (`ruleDiamond_iff`).
* When every rule of the language is of that kind, the language's generated
  diamond is exactly the join of its rules' diamonds
  (`generatedDiamond_iff_exists_ruleDiamond`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

/-- The language with only the rewrite rules `keep` accepts. -/
def LanguageDef.restrictRewrites (language : LanguageDef) (keep : RewriteRule → Bool) : LanguageDef :=
  { language with rewrites := language.rewrites.filter keep }

theorem LanguageDef.restrictRewrites_rewrites (language : LanguageDef) (keep : RewriteRule → Bool) :
    (language.restrictRewrites keep).rewrites = language.rewrites.filter keep := rfl

theorem LanguageDef.isEquationFree_restrictRewrites (language : LanguageDef)
    (keep : RewriteRule → Bool) :
    (language.restrictRewrites keep).isEquationFree = language.isEquationFree := rfl

end Mettapedia.OSLF.MeTTaIL.Syntax

namespace Mettapedia.OSLF.Framework.RuleRestriction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.OSLF.Framework.TypeSynthesis
open Classical

theorem step_of_restrictRewrites {relEnv : RelationEnv} {language : LanguageDef}
    {keep : RewriteRule → Bool} {source target : Pattern}
    (step : Step (engineBasePremises relEnv) (language.restrictRewrites keep) source target) :
    Step (engineBasePremises relEnv) language source target :=
  Step.mono_rules (fun _ member => (List.mem_filter.mp member).1) step

/-- The generated step-future modality of an equation-free language, on a raw
predicate. -/
def generatedDiamond (language : LanguageDef) (equationFree : language.isEquationFree = true)
    (predicate : Pattern → Prop) : Pattern → Prop :=
  (langDiamond language (equationPredicateUsingOfEquationFree RelationEnv.empty equationFree predicate)).1

theorem generatedDiamond_iff (language : LanguageDef) (equationFree : language.isEquationFree = true)
    (predicate : Pattern → Prop) (world : Pattern) :
    generatedDiamond language equationFree predicate world ↔
      ∃ target, Step (engineBasePremises RelationEnv.empty) language world target ∧ predicate target := by
  unfold generatedDiamond langDiamond
  rw [langDiamondUsing_spec]
  exact exists_congr fun target => and_congr_left fun _ =>
    langSemanticReducesUsing_iff_langReducesUsing_of_equation_free RelationEnv.empty equationFree _ _

/-- The generated step-future modality of one rule: the diamond of the language
restricted to that rule. -/
noncomputable def ruleDiamond (language : LanguageDef) (equationFree : language.isEquationFree = true)
    (rule : RewriteRule) (predicate : Pattern → Prop) : Pattern → Prop :=
  generatedDiamond (language.restrictRewrites fun candidate => decide (candidate = rule))
    ((language.isEquationFree_restrictRewrites _).trans equationFree) predicate

theorem ruleDiamond_le_generatedDiamond (language : LanguageDef)
    (equationFree : language.isEquationFree = true) (rule : RewriteRule)
    (predicate : Pattern → Prop) {world : Pattern}
    (holds : ruleDiamond language equationFree rule predicate world) :
    generatedDiamond language equationFree predicate world := by
  unfold ruleDiamond at holds
  rw [generatedDiamond_iff] at holds ⊢
  obtain ⟨target, step, satisfies⟩ := holds
  exact ⟨target, step_of_restrictRewrites step, satisfies⟩

/-- A rule without premises that places its right side without shifting. -/
def IsUnconditionalAligned (rule : RewriteRule) : Prop :=
  rule.premises = [] ∧ ruleDepthAligned rule = true

/-- **The diamond of an unconditional rule** is a match of its left side whose
instance of the right side satisfies the predicate. -/
theorem ruleDiamond_iff (language : LanguageDef) (equationFree : language.isEquationFree = true)
    {rule : RewriteRule} (unconditional : IsUnconditionalAligned rule) (predicate : Pattern → Prop)
    (world : Pattern) :
    ruleDiamond language equationFree rule predicate world ↔
      rule ∈ language.rewrites ∧
        ∃ bindings ∈ matchPattern rule.left world, predicate (applyBindings bindings rule.right) := by
  have restricted : isUnconditionalAligned
      (language.restrictRewrites fun candidate => decide (candidate = rule)) = true := by
    simp only [isUnconditionalAligned, LanguageDef.restrictRewrites_rewrites, List.all_eq_true,
      List.mem_filter, decide_eq_true_eq, Bool.and_eq_true, List.isEmpty_iff]
    rintro _ ⟨-, rfl⟩
    exact unconditional
  unfold ruleDiamond
  rw [generatedDiamond_iff]
  simp only [step_iff_mem_rootReducts _ _ restricted, rootReducts, LanguageDef.restrictRewrites_rewrites,
    List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨_, ⟨member, rfl⟩, bindings, matched, rfl⟩, satisfies⟩
    exact ⟨member, bindings, matched, satisfies⟩
  · rintro ⟨member, bindings, matched, satisfies⟩
    exact ⟨_, ⟨rule, ⟨member, rfl⟩, bindings, matched, rfl⟩, satisfies⟩

/-- **The language's diamond is the join of its rules' diamonds**, when every rule
is unconditional. -/
theorem generatedDiamond_iff_exists_ruleDiamond (language : LanguageDef)
    (equationFree : language.isEquationFree = true)
    (unconditional : isUnconditionalAligned language = true) (predicate : Pattern → Prop)
    (world : Pattern) :
    generatedDiamond language equationFree predicate world ↔
      ∃ rule ∈ language.rewrites, ruleDiamond language equationFree rule predicate world := by
  have certified : ∀ rule ∈ language.rewrites, IsUnconditionalAligned rule := by
    intro rule member
    have := List.all_eq_true.mp unconditional rule member
    simp only [Bool.and_eq_true, List.isEmpty_iff] at this
    exact this
  rw [generatedDiamond_iff]
  simp only [step_iff_mem_rootReducts _ _ unconditional, rootReducts, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨rule, member, bindings, matched, rfl⟩, satisfies⟩
    exact ⟨rule, member, (ruleDiamond_iff language equationFree (certified rule member) _ _).mpr
      ⟨member, bindings, matched, satisfies⟩⟩
  · rintro ⟨rule, member, holds⟩
    obtain ⟨-, bindings, matched, satisfies⟩ :=
      (ruleDiamond_iff language equationFree (certified rule member) _ _).mp holds
    exact ⟨_, ⟨rule, member, bindings, matched, rfl⟩, satisfies⟩

#print axioms ruleDiamond_iff
#print axioms generatedDiamond_iff_exists_ruleDiamond

end Mettapedia.OSLF.Framework.RuleRestriction
