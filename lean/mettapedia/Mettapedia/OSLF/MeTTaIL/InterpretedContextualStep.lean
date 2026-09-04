import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.ReflectionProfile

/-!
# Contextual reduction under an explicit rule interpretation

The five-field language authors rule syntax and premises.  Matching and
contractum instantiation are interpretation choices: the ordinary syntactic
interpretation is canonical, while an admitted reflection profile can supply
a different interpretation without becoming a field of `LanguageDef`.

This module parameterizes both the executable contextual compiler and its
inductive specification by that choice and proves them extensionally equal.
-/

namespace Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Reflection
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-- The two operations required to interpret an authored rewrite schema. -/
structure RuleInterpretation where
  matchRule : LanguageDef → RewriteRule → Pattern → List Bindings
  instantiateRule : LanguageDef → RewriteRule → Bindings → Pattern

namespace RuleInterpretation

/-- Ordinary first-order matching and substitution. -/
def syntactic : RuleInterpretation where
  matchRule := fun _ rule term => matchPattern rule.left term
  instantiateRule := fun _ rule bindings => applyBindings bindings rule.right

/-- Matching and substitution selected by a separately authored profile. -/
def reflection (profile : ReflectionProfile) : RuleInterpretation where
  matchRule := fun _ rule term => matchPatternForRuleUsing profile rule term
  instantiateRule := fun _ rule bindings =>
    applyBindingsForRuleUsing profile rule bindings

@[simp] theorem reflection_matchRule
    (profile : ReflectionProfile) (language : LanguageDef)
    (rule : RewriteRule) (term : Pattern) :
    (reflection profile).matchRule language rule term =
      matchPatternForRuleUsing profile rule term :=
  rfl

@[simp] theorem reflection_instantiateRule
    (profile : ReflectionProfile) (language : LanguageDef)
    (rule : RewriteRule) (bindings : Bindings) :
    (reflection profile).instantiateRule language rule bindings =
      applyBindingsForRuleUsing profile rule bindings :=
  rfl

end RuleInterpretation

/-- Apply one rule with a supplied interpretation and recursive congruence. -/
def applyRuleUsing
    (interpretation : RuleInterpretation)
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern)
    (rule : RewriteRule) (term : Pattern) : List Pattern :=
  (interpretation.matchRule language rule term).flatMap fun initialBindings =>
    (premisesUsing base language recursiveStep rule.premises initialBindings).map
      fun finalBindings =>
        interpretation.instantiateRule language rule finalBindings

/-- Fuel-indexed compilation of contextual reduction under an interpretation. -/
def rewriteAt
    (interpretation : RuleInterpretation)
    (base : BasePremiseEvaluator) (language : LanguageDef) :
    Nat → Pattern → List Pattern
  | 0, _ => []
  | fuel + 1, term =>
      language.rewrites.flatMap fun rule =>
        applyRuleUsing interpretation base language
          (rewriteAt interpretation base language fuel) rule term

mutual
  /-- Evidence for one premise at a fixed interpreted recursive depth. -/
  inductive PremiseAt
      (interpretation : RuleInterpretation)
      (base : BasePremiseEvaluator) (language : LanguageDef) :
      Nat → Bindings → Premise → Bindings → Prop where
    | freshness {bindings result : Bindings} {condition : FreshnessCondition} :
        result ∈ base language bindings (.freshness condition) →
        PremiseAt interpretation base language fuel bindings
          (.freshness condition) result
    | relationQuery {bindings result : Bindings} {relation : String}
        {arguments : List Pattern} :
        result ∈ base language bindings (.relationQuery relation arguments) →
        PremiseAt interpretation base language fuel bindings
          (.relationQuery relation arguments) result
    | forAll {bindings result : Bindings} {collection parameter : String}
        {body : Premise} :
        result ∈ base language bindings (.forAll collection parameter body) →
        PremiseAt interpretation base language fuel bindings
          (.forAll collection parameter body) result
    | congruence
        {bindings premiseBindings result : Bindings}
        {source target candidate : Pattern} :
        StepAt interpretation base language fuel
          (applyBindings bindings source) candidate →
        premiseBindings ∈ matchPattern target candidate →
        mergeBindings bindings premiseBindings = some result →
        PremiseAt interpretation base language fuel bindings
          (.congruence source target) result

  /-- Evidence for an ordered list of interpreted premises. -/
  inductive PremisesAt
      (interpretation : RuleInterpretation)
      (base : BasePremiseEvaluator) (language : LanguageDef) :
      Nat → Bindings → List Premise → Bindings → Prop where
    | nil (bindings : Bindings) :
        PremisesAt interpretation base language fuel bindings [] bindings
    | cons {initial middle final : Bindings} {premise : Premise}
        {premises : List Premise} :
        PremiseAt interpretation base language fuel initial premise middle →
        PremisesAt interpretation base language fuel middle premises final →
        PremisesAt interpretation base language fuel initial
          (premise :: premises) final

  /-- One interpreted authored-rule step at a bounded contextual depth. -/
  inductive StepAt
      (interpretation : RuleInterpretation)
      (base : BasePremiseEvaluator) (language : LanguageDef) :
      Nat → Pattern → Pattern → Prop where
    | rule
        {fuel : Nat} {source target : Pattern} {rule : RewriteRule}
        {initialBindings finalBindings : Bindings} :
        rule ∈ language.rewrites →
        initialBindings ∈ interpretation.matchRule language rule source →
        PremisesAt interpretation base language fuel initialBindings
          rule.premises finalBindings →
        interpretation.instantiateRule language rule finalBindings = target →
        StepAt interpretation base language (fuel + 1) source target
end

/-- The least finite contextual relation under an explicit interpretation. -/
def Step (interpretation : RuleInterpretation)
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (source target : Pattern) : Prop :=
  ∃ fuel, StepAt interpretation base language fuel source target

private theorem mem_premiseStepUsing_iff
    {interpretation : RuleInterpretation}
    {base : BasePremiseEvaluator} {language : LanguageDef} {fuel : Nat}
    {recursiveStep : Pattern → List Pattern}
    (recursiveExact : ∀ {source target},
      target ∈ recursiveStep source ↔
        StepAt interpretation base language fuel source target)
    {bindings result : Bindings} {premise : Premise} :
    result ∈ premiseStepUsing base language recursiveStep bindings premise ↔
      PremiseAt interpretation base language fuel bindings premise result := by
  cases premise with
  | freshness condition =>
      exact ⟨PremiseAt.freshness, fun evidence => by cases evidence; assumption⟩
  | relationQuery relation arguments =>
      exact ⟨PremiseAt.relationQuery, fun evidence => by cases evidence; assumption⟩
  | forAll collection parameter body =>
      exact ⟨PremiseAt.forAll, fun evidence => by cases evidence; assumption⟩
  | congruence source target =>
      constructor
      · intro member
        simp only [premiseStepUsing, List.mem_flatMap,
          List.mem_filterMap] at member
        obtain ⟨candidate, recursiveMember, premiseBindings,
          matchMember, merged⟩ := member
        exact .congruence (recursiveExact.mp recursiveMember)
          matchMember merged
      · intro evidence
        cases evidence with
        | congruence recursive matchMember merged =>
            simp only [premiseStepUsing, List.mem_flatMap,
              List.mem_filterMap]
            exact ⟨_, recursiveExact.mpr recursive, _, matchMember, merged⟩

private theorem mem_premisesUsing_iff
    {interpretation : RuleInterpretation}
    {base : BasePremiseEvaluator} {language : LanguageDef} {fuel : Nat}
    {recursiveStep : Pattern → List Pattern}
    (recursiveExact : ∀ {source target},
      target ∈ recursiveStep source ↔
        StepAt interpretation base language fuel source target)
    {premises : List Premise} {initial final : Bindings} :
    final ∈ premisesUsing base language recursiveStep premises initial ↔
      PremisesAt interpretation base language fuel initial premises final := by
  induction premises generalizing initial final with
  | nil =>
      simp only [premisesUsing, List.mem_singleton]
      constructor
      · intro equal
        subst final
        exact .nil initial
      · intro evidence
        cases evidence
        rfl
  | cons premise premises inductionHypothesis =>
      simp only [premisesUsing, List.mem_flatMap]
      constructor
      · rintro ⟨middle, first, rest⟩
        exact .cons ((mem_premiseStepUsing_iff recursiveExact).mp first)
          ((inductionHypothesis (initial := middle) (final := final)).mp rest)
      · intro evidence
        cases evidence with
        | cons first rest =>
            exact ⟨_, (mem_premiseStepUsing_iff recursiveExact).mpr first,
              (inductionHypothesis (initial := _) (final := final)).mpr rest⟩

/-- The interpreted compiler and its independent bounded relation agree. -/
theorem mem_rewriteAt_iff_stepAt
    {interpretation : RuleInterpretation}
    {base : BasePremiseEvaluator} {language : LanguageDef} {fuel : Nat}
    {source target : Pattern} :
    target ∈ rewriteAt interpretation base language fuel source ↔
      StepAt interpretation base language fuel source target := by
  induction fuel generalizing source target with
  | zero =>
      constructor
      · intro member
        cases member
      · intro step
        cases step
  | succ fuel inductionHypothesis =>
      simp only [rewriteAt]
      constructor
      · intro member
        rw [List.mem_flatMap] at member
        obtain ⟨rule, ruleMember, ruleResult⟩ := member
        unfold applyRuleUsing at ruleResult
        rw [List.mem_flatMap] at ruleResult
        obtain ⟨initialBindings, matched, finalResult⟩ := ruleResult
        rw [List.mem_map] at finalResult
        obtain ⟨finalBindings, premises, targetEq⟩ := finalResult
        exact .rule ruleMember matched
          ((mem_premisesUsing_iff
            (fun {_ _} => inductionHypothesis)).mp premises) targetEq
      · intro step
        cases step with
        | rule ruleMember matched premises targetEq =>
            rw [List.mem_flatMap]
            refine ⟨_, ruleMember, ?_⟩
            unfold applyRuleUsing
            rw [List.mem_flatMap]
            refine ⟨_, matched, ?_⟩
            rw [List.mem_map]
            exact ⟨_, (mem_premisesUsing_iff
              (fun {_ _} => inductionHypothesis)).mpr premises, targetEq⟩

/-! ## Syntactic interpretation recovers the core contextual engine -/

/-- Executing the explicit syntactic rule interpretation is exactly the core
contextual compiler at every finite recursive depth.  This is an operational
compiler theorem; it does not define a second OSLF construction. -/
theorem rewriteAt_syntactic_eq_contextual
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (fuel : Nat) (source : Pattern) :
    rewriteAt .syntactic base language fuel source =
      Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
        base language fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [rewriteAt,
        Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt]
      apply List.flatMap_congr
      intro rule _ruleMember
      unfold applyRuleUsing
        Mettapedia.OSLF.MeTTaIL.ContextualStep.applyRuleUsing
      rw [show
        rewriteAt .syntactic base language fuel =
          Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
            base language fuel from
        funext inductionHypothesis]
      simp only [RuleInterpretation.syntactic,
        matchPatternForRule_eq_syntactic,
        applyBindingsForRule_eq_syntactic]

/-- The least relational syntactic interpretation is exactly the core
contextual relation. -/
theorem step_syntactic_iff_contextual
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (source target : Pattern) :
    Step .syntactic base language source target ↔
      Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
        base language source target := by
  constructor
  · rintro ⟨fuel, step⟩
    refine ⟨fuel,
      Mettapedia.OSLF.MeTTaIL.ContextualStep.mem_rewriteAt_iff_stepAt.mp ?_⟩
    rw [← rewriteAt_syntactic_eq_contextual base language fuel source]
    exact mem_rewriteAt_iff_stepAt.mpr step
  · rintro ⟨fuel, step⟩
    refine ⟨fuel, mem_rewriteAt_iff_stepAt.mp ?_⟩
    rw [rewriteAt_syntactic_eq_contextual base language fuel source]
    exact
      Mettapedia.OSLF.MeTTaIL.ContextualStep.mem_rewriteAt_iff_stepAt.mpr step

/-- A single authored congruence premise lifts one interpreted recursive step. -/
theorem step_of_single_congruence_rule
    {interpretation : RuleInterpretation}
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {rule : RewriteRule} {source target : Pattern}
    {initialBindings finalBindings premiseBindings : Bindings}
    {premiseSource premiseTarget candidate : Pattern}
    (ruleMember : rule ∈ language.rewrites)
    (matched : initialBindings ∈
      interpretation.matchRule language rule source)
    (premisesEq : rule.premises =
      [.congruence premiseSource premiseTarget])
    (recursive : Step interpretation base language
      (applyBindings initialBindings premiseSource) candidate)
    (premiseMatched : premiseBindings ∈ matchPattern premiseTarget candidate)
    (merged : mergeBindings initialBindings premiseBindings =
      some finalBindings)
    (targetEq : interpretation.instantiateRule language rule finalBindings =
      target) :
    Step interpretation base language source target := by
  obtain ⟨fuel, recursiveAt⟩ := recursive
  have premiseEvidence :
      PremisesAt interpretation base language fuel initialBindings
        rule.premises finalBindings := by
    rw [premisesEq]
    exact .cons (.congruence recursiveAt premiseMatched merged)
      (.nil finalBindings)
  exact ⟨fuel + 1, .rule ruleMember matched premiseEvidence targetEq⟩

end Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
