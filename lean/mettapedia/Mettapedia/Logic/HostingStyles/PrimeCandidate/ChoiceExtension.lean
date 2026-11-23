import Mettapedia.GSLT.LanguageDef.RewriteValidationBatch
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ProbeDynamics
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.OSLF.MeTTaIL.PlainRuleValidation

/-!
# The probe extended with choice

`NucleusDerivedModalTyping.probeWithChoice` adds to the probe a binary
constructor `prime-choose` of processes, with a rewrite to each branch, and a
constructor `prime-collect` of the sort `Alternatives`.  Its validation was
left as an evaluation there; it is proved here (`probeWithChoice_validate`),
so the extension is a presentation (`choicePresentation`) and has a generated
context theory.

What the extension changes, and what it does not:

* It generates the nondeterminism that the probe names: a choice has a
  transition to each branch (`choice_branches`).
* Its reduction still fires one rule at the root, between heads or from a
  choice to a branch (`choice_step_cases`).  It has a rank (`choiceRank`), so
  it is terminating (`choice_terminating`): the cyclic reduction of the
  rule-table evaluator has no image in it.
* The bound of three steps is gone: a tower of choices reduces in as many
  steps as it is high (`choiceTower_steps`).
* Its static equivalence is still quotation and dropping alone, so its
  contexts have a linear size (`choiceLinearSize`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_applyBindings)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeCandidates.NucleusDerivedModalTyping

/-! ## The extension passes the declaration gate -/

theorem probeWithChoice_typeNames : probeWithChoice.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt"] := by
  decide

theorem probeWithChoice_signatures :
    RewriteValidationCertificate.constructorSignatures probeWithChoice =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1), ("prime-choose", 2),
        ("prime-collect", 1)] := by
  decide

theorem probeWithChoice_labels :
    RewriteValidationCertificate.constructorLabels probeWithChoice =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt", "prime-choose", "prime-collect"] := by
  decide

theorem probeWithChoice_rewrites : probeWithChoice.rewrites =
    [MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, evaluationDemandRewrite, needRewrite,
      needReturnRewrite, reflectedDemandRewrite, chooseLeftRewrite, chooseRightRewrite] :=
  rfl

/-- Every rewrite of the extension passes its row of the declaration gate. -/
theorem probeWithChoice_rewrites_checked :
    ∀ rewrite ∈ probeWithChoice.rewrites,
      RewriteValidationCertificate.check probeWithChoice rewrite = true := by
  intro rewrite member
  rw [probeWithChoice_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.premiseTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      probeWithChoice_typeNames, probeWithChoice_signatures, probeWithChoice_labels,
      MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite, needRewrite, evaluationDemandRewrite,
      needReturnRewrite, reflectedDemandRewrite, chooseLeftRewrite, chooseRightRewrite,
      MeTTaZero.queryRequestPattern, MeTTaZero.queryAnswerPattern,
      MeTTaZero.evaluationRequestPattern, MeTTaZero.evaluationAnswerPattern,
      MeTTaZero.metavariable,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped, TypeExpr.baseNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt]

/-- **The probe extended with choice passes the declaration gate.** -/
theorem probeWithChoice_validate : probeWithChoice.validate = [] := by
  exact RewriteValidationCertificate.validate_eq_nil_of_signature_and_checks
    (RewriteValidationCertificate.validate_signature_of_plain_equations (lang := probeWithChoice)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel) probeWithChoice_rewrites_checked

/-- **The probe extended with choice, as a presentation.** -/
def choicePresentation : ValidatedLanguageDef := ⟨probeWithChoice, probeWithChoice_validate⟩

/-! ## Its steps -/

/-- `prime-choose left right`. -/
def choose (left right : Pattern) : Pattern := .apply "prime-choose" [left, right]

/-- A step by a rule without premise and with aligned binders relates the
instances of its two sides under one binding. -/
theorem instances_of_plain_rule {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat}
    {rule : RewriteRule} {initial final : Bindings} {source : Pattern}
    (plain : rule.premises = []) (correct : Pattern.isMatchCorrect rule.left = true)
    (aligned : ruleDepthAligned rule = true) (matched : initial ∈ matchPattern rule.left source)
    (premises : PremisesAt base lang fuel initial rule.premises final) :
    source = applyBindings final rule.left ∧
      applyRuleBindings rule final = applyBindings final rule.right := by
  rw [plain] at premises
  cases premises
  exact ⟨(matchPattern_correct matched correct).symm,
    applyRuleBindings_eq_applyBindings rule _ aligned⟩

/-- **Every step of the extension goes along an edge of the probe, or from a
choice to one of its branches.** -/
theorem choice_step_cases {base : BasePremiseEvaluator} {source target : Pattern}
    (step : Step base probeWithChoice source target) :
    (∃ edge ∈ probeEdges, head? source = some edge.1 ∧ head? target = some edge.2) ∨
      ∃ left right, source = choose left right ∧ (target = left ∨ target = right) := by
  obtain ⟨rule, member, _, initial, final, matched, premises, rfl⟩ := exists_rule_of_step step
  rw [probeWithChoice_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨("zero-query", "zero-query-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("zero-evaluate", "zero-evaluate-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("zero-evaluate", "prime-need"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("prime-need", "prime-need-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("prime-need-answer", "zero-evaluate-answer"), by decide,
      head?_of_matched matched, head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("prime-evaluate-name", "prime-need"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · obtain ⟨sourceEq, targetEq⟩ :=
      instances_of_plain_rule (rule := chooseLeftRewrite) rfl (by decide) (by decide) matched
        premises
    refine .inr ⟨applyBindings final (.fvar "left"), applyBindings final (.fvar "right"), ?_,
      .inl ?_⟩
    · rw [sourceEq]
      simp [chooseLeftRewrite, choose, applyBindings]
    · rw [targetEq]
      rfl
  · obtain ⟨sourceEq, targetEq⟩ :=
      instances_of_plain_rule (rule := chooseRightRewrite) rfl (by decide) (by decide) matched
        premises
    refine .inr ⟨applyBindings final (.fvar "left"), applyBindings final (.fvar "right"), ?_,
      .inr ?_⟩
    · rw [sourceEq]
      simp [chooseRightRewrite, choose, applyBindings]
    · rw [targetEq]
      rfl

/-! ## Its rank -/

mutual
  /-- The rank of a pattern in the extension: a choice ranks above the sum of
  its branches, any other application has the rank of its head. -/
  def choiceHeight : Pattern → Nat
    | .apply label arguments =>
        if label = "prime-choose" then 1 + choiceHeightList arguments else headRank label
    | .bvar _ => 0
    | .fvar _ => 0
    | .lambda _ _ => 0
    | .multiLambda _ _ _ => 0
    | .subst _ _ => 0
    | .collection _ _ _ => 0

  /-- The sum of the ranks of a list of patterns. -/
  def choiceHeightList : List Pattern → Nat
    | [] => 0
    | pattern :: patterns => choiceHeight pattern + choiceHeightList patterns
end

/-- The rank of an application whose head is neither choice nor quotation is
the rank of its head. -/
theorem choiceHeight_of_head? {pattern : Pattern} {label : String}
    (head : head? pattern = some label) (notChoice : label ≠ "prime-choose")
    (notQuote : label ≠ "prime-quote") : choiceHeight (contract pattern) = headRank label := by
  obtain ⟨arguments, rfl⟩ := eq_apply_of_head? head
  rw [contract_apply_of_ne notQuote, choiceHeight, if_neg notChoice]

/-- The rank of a choice is above the ranks of its branches. -/
theorem choiceHeight_choose (left right : Pattern) :
    choiceHeight (contract (choose left right)) =
      1 + (choiceHeight (contract left) + choiceHeight (contract right)) := by
  rw [choose, contract_apply_of_ne (by decide)]
  simp [choiceHeight, choiceHeightList]

/-- **Every step of the extension lowers the rank.** -/
theorem choice_step_lowers {base : BasePremiseEvaluator} {source target : Pattern}
    (step : Step base probeWithChoice source target) :
    choiceHeight (contract target) < choiceHeight (contract source) := by
  rcases choice_step_cases step with ⟨edge, member, sourceHead, targetHead⟩ | ⟨left, right, rfl, branch⟩
  · simp only [probeEdges, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [choiceHeight_of_head? sourceHead (by decide) (by decide),
        choiceHeight_of_head? targetHead (by decide) (by decide)] <;>
      decide
  · rw [choiceHeight_choose]
    rcases branch with rfl | rfl <;> omega

/-- **The extension has a rank**, for every evaluator of its premises. -/
def choiceRank (base : BasePremiseEvaluator) : (contextTheory base choicePresentation).Rank where
  rank := fun term => choiceHeight (contract term.1)
  lowers := fun step => by
    obtain ⟨redex, contractum, before, fired, after⟩ := step
    have sourceSame : contract _ = contract redex.1 := probeWithChoice_quoteDropOnly.contract_eq before
    have targetSame : contract contractum.1 = contract _ :=
      probeWithChoice_quoteDropOnly.contract_eq after
    rw [sourceSame, ← targetSame]
    exact choice_step_lowers fired

/-- **The reduction of the extension is terminating.** -/
theorem choice_terminating (base : BasePremiseEvaluator) :
    (contextTheory base choicePresentation).Terminating :=
  (choiceRank base).terminating

/-- **The contexts of the extension have a linear size.** -/
def choiceLinearSize (base : BasePremiseEvaluator) :
    (contextTheory base choicePresentation).LinearSize :=
  QuoteDropOnly.linearSize choicePresentation probeWithChoice_quoteDropOnly base

/-! ## What the extension adds: choice, and reductions of every length -/

/-- A choice reduces to its left branch. -/
theorem chooseLeft_step (base : BasePremiseEvaluator) (left right : Pattern) :
    Step base probeWithChoice (choose left right) left := by
  refine ⟨1, .rule (rule := chooseLeftRewrite)
    (initialBindings := [("right", right), ("left", left)])
    (by rw [probeWithChoice_rewrites]; simp) ?_ (.nil _) ?_⟩
  · simp [matchPatternForRule_eq_syntactic, chooseLeftRewrite, choose, matchPattern, matchArgs,
      mergeBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [chooseLeftRewrite, applyBindings]

/-- A choice reduces to its right branch. -/
theorem chooseRight_step (base : BasePremiseEvaluator) (left right : Pattern) :
    Step base probeWithChoice (choose left right) right := by
  refine ⟨1, .rule (rule := chooseRightRewrite)
    (initialBindings := [("right", right), ("left", left)])
    (by rw [probeWithChoice_rewrites]; simp) ?_ (.nil _) ?_⟩
  · simp [matchPatternForRule_eq_syntactic, chooseRightRewrite, choose, matchPattern, matchArgs,
      mergeBindings]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [chooseRightRewrite, applyBindings]

/-- The evaluation answer for the unit atom. -/
def answerPattern : Pattern := .apply "zero-evaluate-answer" [unitAtom]

/-- A tower of choices: `count` choices, each between a tower and an answer. -/
def choiceTower : Nat → Pattern
  | 0 => answerPattern
  | count + 1 => choose (choiceTower count) answerPattern

/-- Every tower is a closed process of the extension. -/
theorem choiceTower_wellSorted (count : Nat) :
    OpenPatternWellSorted probeWithChoice FreeTypeContext.empty [] (.base "Process")
      (choiceTower count) := by
  induction count with
  | zero => exact checkOpenPatternWellSorted_sound (by decide +kernel)
  | succ count ih =>
      have answer : OpenPatternWellSorted probeWithChoice FreeTypeContext.empty []
          (.base "Process") answerPattern := checkOpenPatternWellSorted_sound (by decide +kernel)
      obtain ⟨typed, canonical, object, scopeSafe⟩ := ih
      obtain ⟨answerTyped, answerCanonical, answerObject, answerScopeSafe⟩ := answer
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact .constructor (rule := chooseConstructor) (by decide)
          (fun bare => by
            have checked := (usesBareCollection?_eq_true_iff _).mpr bare
            revert checked
            decide)
          (.cons trivial rfl typed (.cons trivial rfl answerTyped .nil))
      · simpa [choiceTower, choose, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using ⟨canonical, answerCanonical⟩
      · simpa [choiceTower, choose, isObjectPattern, isObjectPatternList] using
          ⟨object, answerObject⟩
      · have here : (choiceTower count).isWellScopedAt 0 = true := scopeSafe
        have there : answerPattern.isWellScopedAt 0 = true := answerScopeSafe
        show (choiceTower (count + 1)).isWellScopedAt 0 = true
        simp [choiceTower, choose, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here, there]

/-- The interface of the closed processes of the extension. -/
def choiceClosedProcess : Contexts.Interface := ⟨.base "Process", []⟩

/-- A tower, as a term. -/
def choiceTowerTerm (count : Nat) : Contexts.Term probeWithChoice choiceClosedProcess :=
  ⟨choiceTower count, choiceTower_wellSorted count⟩

/-- **The extension has reductions of every length**: a tower of `count`
choices reduces to an answer in `count` steps. -/
theorem choiceTower_steps (base : BasePremiseEvaluator) (count : Nat) :
    (contextTheory base choicePresentation).Steps count (choiceTowerTerm count)
      (choiceTowerTerm 0) := by
  induction count with
  | zero => exact .zero _
  | succ count ih =>
      exact .succ ⟨choiceTowerTerm (count + 1), choiceTowerTerm count, Relation.EqvGen.refl _,
        chooseLeft_step base _ _, Relation.EqvGen.refl _⟩ ih

/-- **A choice has a transition to each branch**, and the two branches may be
apart: the extension generates the nondeterminism that the probe names. -/
theorem choice_branches (base : BasePremiseEvaluator) :
    ∃ term first second : (contextTheory base choicePresentation).Term choiceClosedProcess,
      (contextTheory base choicePresentation).rewrites term first ∧
        (contextTheory base choicePresentation).rewrites term second ∧
          ¬ ((contextTheory base choicePresentation).equations choiceClosedProcess).r first
            second := by
  refine ⟨choiceTowerTerm 2, choiceTowerTerm 1, choiceTowerTerm 0,
    ⟨choiceTowerTerm 2, choiceTowerTerm 1, Relation.EqvGen.refl _,
      chooseLeft_step base (choiceTower 1) answerPattern, Relation.EqvGen.refl _⟩,
    ⟨choiceTowerTerm 2, choiceTowerTerm 0, Relation.EqvGen.refl _,
      chooseRight_step base (choiceTower 1) answerPattern, Relation.EqvGen.refl _⟩, ?_⟩
  intro related
  have same := probeWithChoice_quoteDropOnly.contract_eq related
  revert same
  decide

#print axioms probeWithChoice_validate
#print axioms choice_step_cases
#print axioms choice_step_lowers
#print axioms choiceRank
#print axioms choice_terminating
#print axioms choiceLinearSize
#print axioms choiceTower_steps
#print axioms choice_branches

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
