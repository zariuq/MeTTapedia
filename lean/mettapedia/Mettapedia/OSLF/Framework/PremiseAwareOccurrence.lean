import Mettapedia.OSLF.Framework.WeightedOccurrence
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Occurrences of premise-aware contextual rewriting

The top-level `rewriteOccurrences` adapter deliberately uses `rewriteStep`,
which skips authored rules with premises. This adapter instead follows the
fuel-indexed `rewriteAt` engine. Its rule and alternative indices describe
each executable result at one fixed fuel; they are not stable semantic names
and do not expose the recursive premise derivation itself.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PremiseAwareOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- One authored rule's alternatives in the premise-aware engine. -/
def ruleOccurrencesAt (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursiveFuel ruleIndex : Nat) (rule : RewriteRule) (source : Pattern) :
    List RewriteOccurrence :=
  (applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source).zipIdx.map
    fun (target, alternativeIndex) =>
      { ruleIndex, ruleName := rule.name, alternativeIndex, target }

/-- Enumerate authored rule indices without discarding premise-aware
alternatives. -/
def rewriteOccurrencesFromAt (base : BasePremiseEvaluator)
    (lang : LanguageDef) (recursiveFuel ruleIndex : Nat)
    (rules : List RewriteRule) (source : Pattern) : List RewriteOccurrence :=
  match rules with
  | [] => []
  | rule :: rest =>
      ruleOccurrencesAt base lang recursiveFuel ruleIndex rule source ++
        rewriteOccurrencesFromAt base lang recursiveFuel (ruleIndex + 1) rest source

/-- The executable rule occurrences at one explicit contextual fuel. -/
def rewriteAtOccurrences (base : BasePremiseEvaluator) (lang : LanguageDef)
    (fuel : Nat) (source : Pattern) : List RewriteOccurrence :=
  match fuel with
  | 0 => []
  | recursiveFuel + 1 =>
      rewriteOccurrencesFromAt base lang recursiveFuel 0 lang.rewrites source

private theorem ruleOccurrencesAt_targets (base : BasePremiseEvaluator)
    (lang : LanguageDef) (recursiveFuel ruleIndex : Nat)
    (rule : RewriteRule) (source : Pattern) :
    (ruleOccurrencesAt base lang recursiveFuel ruleIndex rule source).map
      RewriteOccurrence.target =
        applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source := by
  simp [ruleOccurrencesAt, List.map_map, Function.comp_def,
    List.zipIdx_map_fst]

private theorem rewriteOccurrencesFromAt_targets (base : BasePremiseEvaluator)
    (lang : LanguageDef) (recursiveFuel ruleIndex : Nat)
    (rules : List RewriteRule) (source : Pattern) :
    (rewriteOccurrencesFromAt base lang recursiveFuel ruleIndex rules source).map
      RewriteOccurrence.target =
        rules.flatMap fun rule =>
          applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source := by
  induction rules generalizing ruleIndex with
  | nil => rfl
  | cons rule rest ih =>
      simp [rewriteOccurrencesFromAt, ruleOccurrencesAt_targets, ih]

/-- Forgetting occurrence indices recovers the complete premise-aware
executable reduct list, with its ordering and duplicate multiplicity. -/
theorem rewriteAtOccurrences_targets (base : BasePremiseEvaluator)
    (lang : LanguageDef) (fuel : Nat) (source : Pattern) :
    (rewriteAtOccurrences base lang fuel source).map RewriteOccurrence.target =
      rewriteAt base lang fuel source := by
  cases fuel with
  | zero => rfl
  | succ recursiveFuel =>
      exact rewriteOccurrencesFromAt_targets base lang recursiveFuel 0
        lang.rewrites source

/-- Every alternative contributed by a particular rule retains that rule's
index and authored name. -/
theorem ruleOccurrencesAt_identity (base : BasePremiseEvaluator)
    (lang : LanguageDef) (recursiveFuel ruleIndex : Nat)
    (rule : RewriteRule) (source : Pattern) (occurrence : RewriteOccurrence)
    (member : occurrence ∈
      ruleOccurrencesAt base lang recursiveFuel ruleIndex rule source) :
    occurrence.ruleIndex = ruleIndex ∧ occurrence.ruleName = rule.name := by
  simp only [ruleOccurrencesAt, List.mem_map] at member
  obtain ⟨pair, _, rfl⟩ := member
  exact ⟨rfl, rfl⟩

/-- A retained alternative index selects the exact value returned by that
authored rule at this recursive fuel, not merely a value somewhere in its
result list. -/
theorem ruleOccurrencesAt_selected
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursiveFuel ruleIndex : Nat) (rule : RewriteRule) (source : Pattern)
    (occurrence : RewriteOccurrence)
    (member : occurrence ∈
      ruleOccurrencesAt base lang recursiveFuel ruleIndex rule source) :
    occurrence.ruleIndex = ruleIndex ∧
      occurrence.ruleName = rule.name ∧
      (applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source)[occurrence.alternativeIndex]? =
        some occurrence.target := by
  simp only [ruleOccurrencesAt, List.mem_map] at member
  obtain ⟨⟨target, index⟩, inZip, rfl⟩ := member
  exact ⟨rfl, rfl, List.mk_mem_zipIdx_iff_getElem?.mp inZip⟩

private theorem rewriteOccurrencesFromAt_selected
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursiveFuel : Nat) :
    ∀ (ruleIndex : Nat) (rules : List RewriteRule) (source : Pattern)
      (occurrence : RewriteOccurrence),
      occurrence ∈ rewriteOccurrencesFromAt base lang recursiveFuel
        ruleIndex rules source →
      ∃ offset rule,
        rules[offset]? = some rule ∧
        occurrence.ruleIndex = ruleIndex + offset ∧
        occurrence.ruleName = rule.name ∧
        (applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source)[occurrence.alternativeIndex]? =
          some occurrence.target := by
  intro ruleIndex rules
  induction rules generalizing ruleIndex with
  | nil =>
      intro source occurrence member
      simp [rewriteOccurrencesFromAt] at member
  | cons rule rest inductionHypothesis =>
      intro source occurrence member
      have split : occurrence ∈
          ruleOccurrencesAt base lang recursiveFuel ruleIndex rule source ∨
          occurrence ∈ rewriteOccurrencesFromAt base lang recursiveFuel
            (ruleIndex + 1) rest source := by
        simpa only [rewriteOccurrencesFromAt, List.mem_append] using member
      rcases split with selected | later
      · obtain ⟨indexEq, nameEq, targetEq⟩ :=
          ruleOccurrencesAt_selected base lang recursiveFuel ruleIndex
            rule source occurrence selected
        exact ⟨0, rule, rfl, by simpa using indexEq, nameEq, targetEq⟩
      · obtain ⟨offset, chosen, atOffset, indexEq, nameEq, targetEq⟩ :=
          inductionHypothesis (ruleIndex + 1) source occurrence later
        refine ⟨offset + 1, chosen, ?_, ?_, nameEq, targetEq⟩
        · simpa only [List.getElem?_cons_succ] using atOffset
        · omega

/-- Each admitted finite-fuel occurrence authenticates both its authored
rule position and the exact alternative selected from that rule's runtime
result list. The name alone would not distinguish duplicate rule entries. -/
theorem rewriteAtOccurrences_selected
    (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursiveFuel : Nat) (source : Pattern)
    (occurrence : RewriteOccurrence)
    (member : occurrence ∈ rewriteAtOccurrences base lang
      (recursiveFuel + 1) source) :
    ∃ rule,
      lang.rewrites[occurrence.ruleIndex]? = some rule ∧
      occurrence.ruleName = rule.name ∧
      (applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source)[occurrence.alternativeIndex]? =
        some occurrence.target := by
  obtain ⟨offset, rule, selected, indexEq, nameEq, targetEq⟩ :=
    rewriteOccurrencesFromAt_selected base lang recursiveFuel 0
      lang.rewrites source occurrence (by simpa [rewriteAtOccurrences] using member)
  refine ⟨rule, ?_, nameEq, targetEq⟩
  simpa [indexEq] using selected

/-- A successful authored rule application has an executable occurrence that
retains its rule identity, rather than merely its target. -/
theorem ruleOccurrencesAt_named_of_mem (base : BasePremiseEvaluator)
    (lang : LanguageDef) (recursiveFuel ruleIndex : Nat)
    (rule : RewriteRule) (source target : Pattern)
    (result : target ∈
      applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source) :
    ∃ occurrence ∈ ruleOccurrencesAt base lang recursiveFuel ruleIndex rule source,
      occurrence.target = target ∧
      occurrence.ruleIndex = ruleIndex ∧ occurrence.ruleName = rule.name := by
  have mapped : target ∈
      (ruleOccurrencesAt base lang recursiveFuel ruleIndex rule source).map
        RewriteOccurrence.target := by
    rw [ruleOccurrencesAt_targets]
    exact result
  obtain ⟨occurrence, member, targetEq⟩ := List.mem_map.mp mapped
  obtain ⟨indexEq, nameEq⟩ :=
    ruleOccurrencesAt_identity base lang recursiveFuel ruleIndex rule source
      occurrence member
  exact ⟨occurrence, member, targetEq, indexEq, nameEq⟩

/-- Searching an authored rule list preserves the name of a selected rule,
even when other rules can produce the same target. -/
theorem rewriteOccurrencesFromAt_named_of_mem (base : BasePremiseEvaluator)
    (lang : LanguageDef) (recursiveFuel ruleIndex : Nat)
    (rules : List RewriteRule) (rule : RewriteRule) (source target : Pattern)
    (ruleMember : rule ∈ rules)
    (result : target ∈
      applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source) :
    ∃ occurrence ∈
        rewriteOccurrencesFromAt base lang recursiveFuel ruleIndex rules source,
      occurrence.target = target ∧ occurrence.ruleName = rule.name := by
  induction rules generalizing ruleIndex with
  | nil => cases ruleMember
  | cons head tail ih =>
      rcases List.mem_cons.mp ruleMember with equal | inTail
      · subst head
        obtain ⟨occurrence, member, targetEq, _, nameEq⟩ :=
          ruleOccurrencesAt_named_of_mem base lang recursiveFuel ruleIndex rule
            source target result
        exact ⟨occurrence, by simp [rewriteOccurrencesFromAt, member],
          targetEq, nameEq⟩
      · obtain ⟨occurrence, member, targetEq, nameEq⟩ :=
          ih (ruleIndex + 1) inTail
        exact ⟨occurrence, by simp [rewriteOccurrencesFromAt, member],
          targetEq, nameEq⟩

/-- The premise-aware engine exposes a rule-named occurrence at a finite
contextual depth whenever that rule contributes a target. -/
theorem rewriteAtOccurrences_named_of_rule_result (base : BasePremiseEvaluator)
    (lang : LanguageDef) (recursiveFuel : Nat) (rule : RewriteRule)
    (source target : Pattern) (ruleMember : rule ∈ lang.rewrites)
    (result : target ∈
      applyRuleUsing base lang (rewriteAt base lang recursiveFuel) rule source) :
    ∃ occurrence ∈ rewriteAtOccurrences base lang (recursiveFuel + 1) source,
      occurrence.target = target ∧ occurrence.ruleName = rule.name := by
  simpa [rewriteAtOccurrences] using
    rewriteOccurrencesFromAt_named_of_mem base lang recursiveFuel 0
      lang.rewrites rule source target ruleMember result

/-- A named executable occurrence has exactly the support of one bounded
premise-aware contextual step. -/
theorem occurrence_support_iff_stepAt (base : BasePremiseEvaluator)
    (lang : LanguageDef) (fuel : Nat) (source target : Pattern) :
    (∃ occurrence ∈ rewriteAtOccurrences base lang fuel source,
      occurrence.target = target) ↔ StepAt base lang fuel source target := by
  rw [← mem_rewriteAt_iff_stepAt]
  rw [← rewriteAtOccurrences_targets]
  simp

/-- Some finite-fuel executable occurrence exists exactly when the least
authored premise-aware relation takes a step. -/
theorem occurrence_support_iff_step (base : BasePremiseEvaluator)
    (lang : LanguageDef) (source target : Pattern) :
    (∃ fuel, ∃ occurrence ∈ rewriteAtOccurrences base lang fuel source,
      occurrence.target = target) ↔ Step base lang source target := by
  rw [← exists_mem_rewriteAt_iff_step]
  apply exists_congr
  intro fuel
  rw [← rewriteAtOccurrences_targets]
  simp

/-- The same exact-support statement through the public empty-environment
OSLF reduction interface. -/
theorem occurrence_support_iff_langReduces (lang : LanguageDef)
    (source target : Pattern) :
    (∃ fuel, ∃ occurrence ∈
      rewriteAtOccurrences (engineBasePremises RelationEnv.empty) lang fuel source,
      occurrence.target = target) ↔ langReduces lang source target := by
  exact occurrence_support_iff_step
    (engineBasePremises RelationEnv.empty) lang source target

end Mettapedia.OSLF.Framework.PremiseAwareOccurrence
