import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Exact one-layer execution for nonrecursive LanguageDefs

Authored congruence and scoped-step premises are the premise forms that consume
the recursive `rewriteAt` argument.  Consequently a language whose premises are
free of both has the same one-step result at every positive contextual fuel.  This module records that fact once, independently of any particular
LanguageDef.

When every rule is moreover unconditional and places its right side without
shifting, one step is exactly a syntactic match of some rule's left side followed
by substitution into its right side (`step_iff_mem_rootReducts`).
-/

namespace Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction

open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

set_option autoImplicit false

/-- A premise that does not recursively invoke the enclosing reduction. -/
def PremiseNonrecursive : Premise → Prop
  | .congruence _ _ => False
  | .scopedStep _ => False
  | _ => True

/-- Every premise of a rule is nonrecursive. -/
def RewriteRuleNonrecursive (rule : RewriteRule) : Prop :=
  ∀ premise ∈ rule.premises, PremiseNonrecursive premise

/-- Every authored rewrite row of a language is nonrecursive. -/
def LanguageDefNonrecursive (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.rewrites, RewriteRuleNonrecursive rule

theorem premiseStepUsing_eq_of_nonrecursive
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (first second : Pattern → List Pattern) (bindings : Bindings)
    (premise : Premise) (nonrecursive : PremiseNonrecursive premise) :
    premiseStepUsing base language first bindings premise =
      premiseStepUsing base language second bindings premise := by
  cases premise <;> simp_all [PremiseNonrecursive, premiseStepUsing]

theorem premisesUsing_eq_of_nonrecursive
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (first second : Pattern → List Pattern) (premises : List Premise)
    (nonrecursive : ∀ premise ∈ premises, PremiseNonrecursive premise)
    (bindings : Bindings) :
    premisesUsing base language first premises bindings =
      premisesUsing base language second premises bindings := by
  induction premises generalizing bindings with
  | nil => rfl
  | cons premise rest inductionHypothesis =>
      simp only [premisesUsing]
      rw [premiseStepUsing_eq_of_nonrecursive base language first second
        bindings premise (nonrecursive premise (by simp))]
      apply List.flatMap_congr
      intro next nextMember
      exact inductionHypothesis
        (fun candidate membership => nonrecursive candidate (by simp [membership]))
        next

theorem applyRuleUsing_eq_of_nonrecursive
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (first second : Pattern → List Pattern) (rule : RewriteRule)
    (nonrecursive : RewriteRuleNonrecursive rule) (term : Pattern) :
    applyRuleUsing base language first rule term =
      applyRuleUsing base language second rule term := by
  simp only [applyRuleUsing]
  apply List.flatMap_congr
  intro bindings bindingsMember
  rw [premisesUsing_eq_of_nonrecursive base language first second
    rule.premises nonrecursive bindings]

/-- Positive contextual fuel is observationally irrelevant for a
congruence-free LanguageDef. -/
theorem rewriteAt_succ_eq_one
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (nonrecursive : LanguageDefNonrecursive language) (fuel : Nat) (term : Pattern) :
    rewriteAt base language (fuel + 1) term = rewriteAt base language 1 term := by
  simp only [rewriteAt]
  apply List.flatMap_congr
  intro rule ruleMember
  exact applyRuleUsing_eq_of_nonrecursive base language
    (rewriteAt base language fuel) (fun _ => []) rule
    (nonrecursive rule ruleMember) term

/-- For a nonrecursive LanguageDef, the least declarative step relation is
exactly membership in the executable one-layer result. -/
theorem step_iff_mem_rewriteAt_one
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (nonrecursive : LanguageDefNonrecursive language) (source target : Pattern) :
    Step base language source target ↔ target ∈ rewriteAt base language 1 source := by
  constructor
  · rintro ⟨fuel, step⟩
    cases fuel with
    | zero => cases step
    | succ fuel =>
        have member := (mem_rewriteAt_iff_stepAt).2 step
        rwa [rewriteAt_succ_eq_one base language nonrecursive fuel source] at member
  · intro member
    exact ⟨1, (mem_rewriteAt_iff_stepAt).1 member⟩

/-! ## Unconditional languages -/

/-- Every rule has no premises and places its right side without shifting. -/
def isUnconditionalAligned (language : LanguageDef) : Bool :=
  language.rewrites.all fun rule => rule.premises.isEmpty && ruleDepthAligned rule

/-- The root reducts of a term: every rule, every syntactic match of its left side,
its right side under that match. -/
def rootReducts (language : LanguageDef) (term : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rule =>
    (matchPattern rule.left term).map fun bindings => applyBindings bindings rule.right

theorem rewriteAt_succ_eq_rootReducts (base : BasePremiseEvaluator) (language : LanguageDef)
    (unconditional : isUnconditionalAligned language = true) (fuel : Nat) (term : Pattern) :
    rewriteAt base language (fuel + 1) term = rootReducts language term := by
  simp only [rewriteAt, rootReducts]
  apply List.flatMap_congr
  intro rule member
  have certified := List.all_eq_true.mp unconditional rule member
  simp only [Bool.and_eq_true, List.isEmpty_iff] at certified
  obtain ⟨premiseFree, aligned⟩ := certified
  simp only [applyRuleUsing, premiseFree, premisesUsing, matchPatternForRule,
    applyBindingsForRule, applyBindingsForRuleUsing_empty_eq_applyBindings _ _ aligned,
    matchPatternForRule_eq_syntactic_of_no_presentations
      (rfl : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty.presentations = [])]
  induction matchPattern rule.left term with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, List.map_cons, ih]
      rfl

/-- **One step of an unconditional language is a root reduct.** -/
theorem step_iff_mem_rootReducts (base : BasePremiseEvaluator) (language : LanguageDef)
    (unconditional : isUnconditionalAligned language = true) (source target : Pattern) :
    Step base language source target ↔ target ∈ rootReducts language source := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    cases fuel with
    | zero => simp [rewriteAt] at member
    | succ fuel => rwa [rewriteAt_succ_eq_rootReducts base language unconditional] at member
  · intro member
    exact ⟨1, by rwa [rewriteAt_succ_eq_rootReducts base language unconditional]⟩

section AxiomAudit

#print axioms rewriteAt_succ_eq_one
#print axioms step_iff_mem_rewriteAt_one
#print axioms step_iff_mem_rootReducts

end AxiomAudit

end Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
