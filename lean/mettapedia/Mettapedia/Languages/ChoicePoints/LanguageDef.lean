import Mettapedia.Languages.PartrecMachine.Rice
import Mettapedia.OSLF.Framework.GeneratedModalFamily
import Mettapedia.OSLF.Framework.RuleRestriction

/-!
# Choice points hosting machine agents

An authored language of choice points whose agents are programs of the authored
partial-recursive machine.  It extends `partrecMachine` — its constructors and
rewrites are included, not restated — with one sort of worlds:

* `Scene agent situation` — an agent facing a situation; the agent is a machine
  code and the situation a natural number;
* `Did action situation` — the outcome of an action taken in a situation;
* `Decide cfg situation` — deliberation in progress, `cfg` a machine
  configuration.

Its rewrites add, to the machine's:

* **actions as redex sites** — one rule `Choose j : Scene a s ⇝ Did j s` for each
  action `j < actionCount`, each a root redex site of the language
  (`actionSite_mem_redexSites`);
* **deliberation** — `Deliberate : Scene a s ⇝ Decide (Normal a halt [s]) s`, a
  congruence rule running the machine inside `Decide`, and
  `Decided : Decide (Halt (j :: rest)) s ⇝ Did j s`.

So an agent can take any action at a scene, and deliberation takes the action its
program computes.  `deliberation_reaches` proves the second: if the machine,
reduced as authored, returns `j` on `[s]`, the scene reduces through
deliberation to `Did j s`.  The congruence rule is load-bearing: without it
deliberation is stuck at its first machine configuration
(`withoutDeliberationStep_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ChoicePoints

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.GeneratedModalFamily
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec

/-! ## The language -/

def worldTerms : List GrammarRule := [
    { label := "Scene", category := "World",
      params := [.simple "agent" (.base "Code"), .simple "situation" (.base "Nat")],
      syntaxPattern := [.nonTerminal "agent", .nonTerminal "situation"] },
    { label := "Did", category := "World",
      params := [.simple "action" (.base "Nat"), .simple "situation" (.base "Nat")],
      syntaxPattern := [.nonTerminal "action", .nonTerminal "situation"] },
    { label := "Decide", category := "World",
      params := [.simple "cfg" (.base "Cfg"), .simple "situation" (.base "Nat")],
      syntaxPattern := [.nonTerminal "cfg", .nonTerminal "situation"] }
  ]

/-- Taking action `action` at a scene. -/
def chooseRule (action : ℕ) : RewriteRule :=
  { name := s!"Choose{action}"
    typeContext := [("agent", .base "Code"), ("situation", .base "Nat")]
    premises := []
    left := .apply "Scene" [.fvar "agent", .fvar "situation"]
    right := .apply "Did" [encNat action, .fvar "situation"] }

/-- Starting deliberation: run the agent on the one-element list `[situation]`. -/
def deliberateRule : RewriteRule :=
  { name := "Deliberate"
    typeContext := [("agent", .base "Code"), ("situation", .base "Nat")]
    premises := []
    left := .apply "Scene" [.fvar "agent", .fvar "situation"]
    right := .apply "Decide"
      [.apply "Normal" [.fvar "agent", .apply "HaltCont" [],
        .apply "Cons" [.fvar "situation", .apply "Nil" []]], .fvar "situation"] }

/-- Deliberation proceeds by a machine step of its configuration. -/
def deliberationStepRule : RewriteRule :=
  { name := "DeliberationStep"
    typeContext := [("cfg", .base "Cfg"), ("next", .base "Cfg"), ("situation", .base "Nat")]
    premises := [.congruence (.fvar "cfg") (.fvar "next")]
    left := .apply "Decide" [.fvar "cfg", .fvar "situation"]
    right := .apply "Decide" [.fvar "next", .fvar "situation"] }

/-- Deliberation ends by taking the action at the head of the halted output. -/
def decidedRule : RewriteRule :=
  { name := "Decided"
    typeContext := [("action", .base "Nat"), ("rest", .base "Nats"), ("situation", .base "Nat")]
    premises := []
    left := .apply "Decide" [.apply "Halt" [.apply "Cons" [.fvar "action", .fvar "rest"]],
      .fvar "situation"]
    right := .apply "Did" [.fvar "action", .fvar "situation"] }

def actionRules (actionCount : ℕ) : List RewriteRule :=
  (List.range actionCount).map chooseRule

def choiceRewrites (actionCount : ℕ) : List RewriteRule :=
  rewrites ++ actionRules actionCount ++ [deliberateRule, deliberationStepRule, decidedRule]

/-- Choice points with `actionCount` actions, hosting machine agents. -/
def choiceLanguage (actionCount : ℕ) : LanguageDef :=
  LanguageDef.ofCore s!"ChoicePoints{actionCount}" ["Nat", "Nats", "Code", "Cont", "Cfg", "World"]
    (terms ++ worldTerms) [] (choiceRewrites actionCount)

theorem choiceLanguage_rewrites (actionCount : ℕ) :
    (choiceLanguage actionCount).rewrites = choiceRewrites actionCount := rfl

/-! ## Worlds -/

def scene (agent : Code) (situation : ℕ) : Pattern :=
  .apply "Scene" [encCode agent, encNat situation]

def did (action situation : ℕ) : Pattern :=
  .apply "Did" [encNat action, encNat situation]

def deciding (cfg : Pattern) (situation : ℕ) : Pattern :=
  .apply "Decide" [cfg, encNat situation]

/-! ## Actions are redex sites -/

/-- The site of action `action`: its rule, at the root. -/
def actionSite (action : ℕ) : Site := (chooseRule action, [])

theorem chooseRule_mem {actionCount action : ℕ} (inRange : action < actionCount) :
    chooseRule action ∈ (choiceLanguage actionCount).rewrites := by
  simp only [choiceLanguage_rewrites, choiceRewrites, actionRules, List.mem_append, List.mem_map,
    List.mem_range]
  exact .inl (.inr ⟨action, inRange, rfl⟩)

theorem actionSite_mem_redexSites {actionCount action : ℕ} (inRange : action < actionCount) :
    actionSite action ∈ redexSites (choiceLanguage actionCount) :=
  root_site_mem _ (chooseRule_mem inRange)

/-! ## Base language -/

abbrev choiceBase : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

abbrev ChoiceStep (actionCount : ℕ) : Pattern → Pattern → Prop :=
  Step choiceBase (choiceLanguage actionCount)

theorem machine_rules_mem (actionCount : ℕ) :
    ∀ rule, rule ∈ partrecMachine.rewrites → rule ∈ (choiceLanguage actionCount).rewrites := by
  intro rule member
  simp only [choiceLanguage_rewrites, choiceRewrites, List.mem_append]
  exact .inl (.inl (by simpa [partrecMachine_rewrites] using member))

theorem machine_step_lifts {actionCount : ℕ} {source target : Pattern}
    (reduces : Reduces source target) : ChoiceStep actionCount source target :=
  Step.mono_rules (machine_rules_mem actionCount) reduces

/-! ## Rule application on first-order rules -/

theorem encNat_binderFree (n : ℕ) : binderFree (encNat n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encNat, binderFree, binderFreeList, ih]

theorem applyBindings_encNat (bindings : Bindings) (n : ℕ) :
    applyBindings bindings (encNat n) = encNat n := by
  induction n with
  | zero => simp [encNat, applyBindings]
  | succ n ih => simp [encNat, applyBindings, ih]

theorem applyBindingsForRule_eq_of_binderFree (lang : LanguageDef) (rule : RewriteRule)
    (bindings : Bindings) (left : binderFree rule.left = true) (right : binderFree rule.right = true) :
    applyBindingsForRule lang rule bindings = applyBindings bindings rule.right :=
  applyBindingsForRuleUsing_empty_eq_applyBindings _ _ (ruleDepthAligned_of_binderFree rule left right)

/-! ## Taking an action -/

theorem choose_steps {actionCount action : ℕ} (inRange : action < actionCount)
    (agent : Code) (situation : ℕ) :
    ChoiceStep actionCount (scene agent situation) (did action situation) := by
  refine step_of_rule (chooseRule_mem inRange) (initialBindings :=
      [("situation", encNat situation), ("agent", encCode agent)]) ?_ .nil
    (finalBindings := [("situation", encNat situation), ("agent", encCode agent)]) ?_ ?_
  · simp [chooseRule, scene, matchPattern, matchArgs, mergeBindings]
  · simp [applyPremisesWithEnv, chooseRule]
  · rw [applyBindingsForRule_eq_of_binderFree _ _ _ (by rfl)
      (by simp [chooseRule, binderFree, binderFreeList, encNat_binderFree])]
    simp [chooseRule, did, applyBindings, applyBindings_encNat]

/-! ## Deliberation -/

theorem deliberate_steps (actionCount : ℕ) (agent : Code) (situation : ℕ) :
    ChoiceStep actionCount (scene agent situation)
      (deciding (normalTerm agent .halt [situation]) situation) := by
  have member : deliberateRule ∈ (choiceLanguage actionCount).rewrites := by
    simp [choiceLanguage_rewrites, choiceRewrites]
  refine step_of_rule member (initialBindings :=
      [("situation", encNat situation), ("agent", encCode agent)]) ?_ .nil
    (finalBindings := [("situation", encNat situation), ("agent", encCode agent)]) ?_ ?_
  · simp [deliberateRule, scene, matchPattern, matchArgs, mergeBindings]
  · simp [applyPremisesWithEnv, deliberateRule]
  · rw [applyBindingsForRule_eq_of_binderFree _ _ _ rfl rfl]
    simp [deliberateRule, deciding, normalTerm, encCont, encNats, applyBindings]

theorem deliberation_step_lifts {actionCount : ℕ} {cfg next : Pattern} (situation : ℕ)
    (reduces : Reduces cfg next) :
    ChoiceStep actionCount (deciding cfg situation) (deciding next situation) := by
  have member : deliberationStepRule ∈ (choiceLanguage actionCount).rewrites := by
    simp [choiceLanguage_rewrites, choiceRewrites]
  refine step_of_single_congruence_rule member
    (initialBindings := [("situation", encNat situation), ("cfg", cfg)])
    (premiseBindings := [("next", next)])
    (finalBindings := [("next", next), ("situation", encNat situation), ("cfg", cfg)])
    (premiseSource := .fvar "cfg") (premiseTarget := .fvar "next") (candidate := next)
    ?_ rfl ?_ ?_ ?_ ?_
  · simp [deliberationStepRule, deciding, matchPattern, matchArgs,
      mergeBindings]
  · simpa [applyBindings] using machine_step_lifts reduces
  · simp [matchPattern]
  · simp [mergeBindings]
  · rw [applyBindingsForRule_eq_of_binderFree _ _ _ rfl rfl]
    simp [deliberationStepRule, deciding, applyBindings]

theorem deliberation_reduction_lifts {actionCount : ℕ} {cfg target : Pattern} (situation : ℕ)
    (reduces : Relation.ReflTransGen Reduces cfg target) :
    Relation.ReflTransGen (ChoiceStep actionCount) (deciding cfg situation)
      (deciding target situation) := by
  induction reduces with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (deliberation_step_lifts situation last)

theorem decided_steps (actionCount action : ℕ) (rest : List ℕ) (situation : ℕ) :
    ChoiceStep actionCount (deciding (encCfg (.halt (action :: rest))) situation)
      (did action situation) := by
  have member : decidedRule ∈ (choiceLanguage actionCount).rewrites := by
    simp [choiceLanguage_rewrites, choiceRewrites]
  refine step_of_rule member (initialBindings :=
      [("situation", encNat situation), ("rest", encNats rest), ("action", encNat action)])
    ?_ .nil
    (finalBindings :=
      [("situation", encNat situation), ("rest", encNats rest), ("action", encNat action)]) ?_ ?_
  · simp [decidedRule, deciding, encCfg, encNats, matchPattern, matchArgs,
      mergeBindings]
  · simp [applyPremisesWithEnv, decidedRule]
  · rw [applyBindingsForRule_eq_of_binderFree _ _ _ rfl rfl]
    simp [decidedRule, did, applyBindings]

/-- **Deliberation takes the action the agent computes.**  If the authored machine
returns `action` at the head of its output on `[situation]`, the scene reduces
through deliberation to that action's outcome. -/
theorem deliberation_reaches (actionCount : ℕ) {agent : Code} {situation action : ℕ}
    {rest : List ℕ} (computes : HaltsWith agent [situation] (action :: rest)) :
    Relation.ReflTransGen (ChoiceStep actionCount) (scene agent situation) (did action situation) :=
  (Relation.ReflTransGen.single (deliberate_steps actionCount agent situation)).trans
    ((deliberation_reduction_lifts situation computes).tail (decided_steps actionCount action rest situation))

/-! ## Structural admission of the two-action language -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
private theorem choiceRewrites_validate :
    ∀ rule ∈ (choiceLanguage 2).rewrites,
      LanguageDef.validateRewrite (choiceLanguage 2) rule = [] := by
  intro rule membership
  simp only [choiceLanguage_rewrites, choiceRewrites, List.mem_append, actionRules] at membership
  rcases membership with (inMachine | inActions) | inWorld
  · simp only [rewrites, List.mem_cons, List.mem_nil_iff, or_false] at inMachine
    rcases inMachine with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp +decide [LanguageDef.validateRewrite, choiceLanguage, LanguageDef.ofCore, terms,
        worldTerms, LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
        LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames, LanguageDef.typeNames]
  · simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.mem_cons,
      List.mem_nil_iff, or_false] at inActions
    rcases inActions with rfl | rfl
    all_goals
      simp +decide [LanguageDef.validateRewrite, choiceLanguage, LanguageDef.ofCore, terms,
        worldTerms, chooseRule, encNat, LanguageDef.validatePatternConstructors,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, Pattern.constructorRefs, Pattern.constructorRefsList,
        Pattern.freeFvarNames, LanguageDef.typeNames]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at inWorld
    rcases inWorld with rfl | rfl | rfl
    all_goals
      simp +decide [LanguageDef.validateRewrite, choiceLanguage, LanguageDef.ofCore, terms,
        worldTerms, deliberateRule, deliberationStepRule, decidedRule,
        LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
        LanguageDef.patternFvarNames, LanguageDef.premiseFvarNames,
        LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
        LanguageDef.premiseForAllParams, LanguageDef.patternBinderNames, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames, LanguageDef.typeNames]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- The two-action choice language passes the structural declaration gate. -/
theorem choiceLanguage_two_validate_eq_nil : (choiceLanguage 2).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  exact choiceRewrites_validate

/-! ## Rule-indexed modalities -/

open Mettapedia.OSLF.Framework.RuleRestriction

theorem choiceLanguage_equationFree (actionCount : ℕ) :
    (choiceLanguage actionCount).isEquationFree = true := by
  have same : (choiceLanguage actionCount).isEquationFree =
      (LanguageDef.ofCore "" ["Nat", "Nats", "Code", "Cont", "Cfg", "World"]
        (terms ++ worldTerms) [] []).isEquationFree := rfl
  rw [same]
  decide +kernel

theorem chooseRule_unconditional (action : ℕ) : IsUnconditionalAligned (chooseRule action) :=
  ⟨rfl, ruleDepthAligned_of_binderFree _ rfl
    (by simp [chooseRule, binderFree, binderFreeList, encNat_binderFree])⟩

theorem deliberateRule_unconditional : IsUnconditionalAligned deliberateRule :=
  ⟨rfl, by decide +kernel⟩

theorem chooseRule_injective {action action' : ℕ} (same : chooseRule action = chooseRule action') :
    action = action' := by
  have rights := congrArg RewriteRule.right same
  simp only [chooseRule, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at rights
  exact encNat_injective rights

/-- The machine's rules and the deliberation rules are not action rules. -/
theorem machine_rules_not_at_scene :
    ((rewrites ++ [deliberationStepRule, decidedRule]).all fun rule =>
      match rule.left with
      | .apply "Scene" _ => false
      | _ => true) = true := by
  decide +kernel

theorem chooseRule_mem_iff (actionCount action : ℕ) :
    chooseRule action ∈ (choiceLanguage actionCount).rewrites ↔ action < actionCount := by
  refine ⟨fun member => ?_, chooseRule_mem⟩
  simp only [choiceLanguage_rewrites, choiceRewrites, actionRules, List.mem_append, List.mem_map,
    List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at member
  have notScene := fun rule (inMachine : rule ∈ rewrites ++ [deliberationStepRule, decidedRule]) =>
    List.all_eq_true.mp machine_rules_not_at_scene rule inMachine
  rcases member with (inMachine | ⟨action', inRange, same⟩) | same | same | same
  · have := notScene _ (List.mem_append_left _ inMachine)
    simp [chooseRule] at this
  · exact chooseRule_injective same ▸ inRange
  · have := congrArg RewriteRule.right same
    simp [chooseRule, deliberateRule] at this
  · have := notScene deliberationStepRule (by simp)
    rw [← same] at this
    simp [chooseRule] at this
  · have := notScene decidedRule (by simp)
    rw [← same] at this
    simp [chooseRule] at this

/-- **Each action has its own generated modality**: at a scene it holds exactly
when the action is declared and its outcome satisfies the predicate. -/
theorem chooseDiamond_scene (actionCount action : ℕ) (predicate : Pattern → Prop) (agent : Code)
    (situation : ℕ) :
    ruleDiamond (choiceLanguage actionCount) (choiceLanguage_equationFree actionCount)
        (chooseRule action) predicate (scene agent situation) ↔
      action < actionCount ∧ predicate (did action situation) := by
  rw [ruleDiamond_iff _ _ (chooseRule_unconditional action), chooseRule_mem_iff]
  simp [chooseRule, scene, did, matchPattern, matchArgs, mergeBindings, applyBindings,
    applyBindings_encNat]

/-- **The deliberation modality sees the agent**: at a scene it holds exactly when
the agent's pending evaluation on the situation satisfies the predicate. -/
theorem deliberateDiamond_scene (actionCount : ℕ) (predicate : Pattern → Prop) (agent : Code)
    (situation : ℕ) :
    ruleDiamond (choiceLanguage actionCount) (choiceLanguage_equationFree actionCount)
        deliberateRule predicate (scene agent situation) ↔
      predicate (deciding (normalTerm agent .halt [situation]) situation) := by
  have member : deliberateRule ∈ (choiceLanguage actionCount).rewrites := by
    simp [choiceLanguage_rewrites, choiceRewrites]
  rw [ruleDiamond_iff _ _ deliberateRule_unconditional, and_iff_right member]
  simp [deliberateRule, scene, deciding, normalTerm, encCont, encNats, matchPattern, matchArgs,
    mergeBindings, applyBindings]

/-! ## Controls -/

/-- The agent `zero'` returns `0 :: [situation]`, so it deliberates to action `0`. -/
theorem zero'_deliberates_to_zero (actionCount situation : ℕ) :
    Relation.ReflTransGen (ChoiceStep actionCount) (scene .zero' situation) (did 0 situation) :=
  deliberation_reaches actionCount (rest := [situation]) (haltsWith_iff.mpr (by simp))

/-- The two-action language without the deliberation congruence rule. -/
def withoutDeliberationStep : LanguageDef :=
  (choiceLanguage 2).restrictRewrites fun rule => rule.name != "DeliberationStep"

/-- **The congruence rule is load-bearing.**  Without it, deliberation cannot
advance past its first machine configuration. -/
theorem withoutDeliberationStep_stuck (target : Pattern) :
    ¬ Step choiceBase withoutDeliberationStep
      (deciding (normalTerm .zero' .halt [0]) 0) target := by
  apply not_step_of_matchPatternForRule_eq_nil
  have none : withoutDeliberationStep.rewrites.all (fun rule =>
      matchPatternForRule withoutDeliberationStep rule
        (deciding (normalTerm .zero' .halt [0]) 0) == []) = true := by
    decide +kernel
  intro rule member
  exact beq_iff_eq.mp (List.all_eq_true.mp none rule member)

#print axioms actionSite_mem_redexSites
#print axioms choose_steps
#print axioms deliberation_reaches
#print axioms zero'_deliberates_to_zero
#print axioms withoutDeliberationStep_stuck
#print axioms chooseDiamond_scene
#print axioms deliberateDiamond_scene

end Mettapedia.Languages.ChoicePoints
