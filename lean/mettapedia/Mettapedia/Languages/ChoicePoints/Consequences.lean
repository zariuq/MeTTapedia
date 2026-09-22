import Mettapedia.Languages.ChoicePoints.LanguageDef

/-!
# Consequences computed by a world program

In the choice-point language an outcome `Did action situation` is where reduction
stops.  Consequences are then labels on outcomes, supplied from outside the
language.  This module lets a machine program compute them.

`consequenceLanguage actionCount world` extends the choice language with two world
constructors and three rules:

* `Evolve cfg` — the world program running on an outcome;
* `Outcome outcome` — the consequence it computes;
* `Unfold` — `Did action situation` starts `world` on `[action, situation]`;
* `EvolveStep` — the world advances by a machine step (a congruence rule);
* `Evolved` — the world halts with `outcome :: rest` and yields `Outcome outcome`.

The world program is part of the language, so what doing an act leads to is read
off reduction.

* **Consequences are reached** (`did_reaches_outcome`, `scene_reaches_outcome`):
  when `world` halts on `[action, situation]` with `outcome` at the head, doing
  the action reaches that outcome.
* **And only those** (`did_reaches_outcome_iff`): reduction from doing an action
  reaches an outcome exactly when the world program computes it.
* **Whether an act can lead to an ideal outcome is undecidable in the world**
  (`idealReachable_not_computable`), for any ideal that some outcome satisfies.
  The set of worlds in which it can depends only on what the world program
  computes, so Rice's theorem for the machine applies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ChoicePoints

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.PartrecMachine
open Mettapedia.Computability
open Turing.ToPartrec

/-! ## The language -/

def consequenceTerms : List GrammarRule := [
    { label := "Evolve", category := "World",
      params := [.simple "cfg" (.base "Cfg")],
      syntaxPattern := [.nonTerminal "cfg"] },
    { label := "Outcome", category := "World",
      params := [.simple "outcome" (.base "Nat")],
      syntaxPattern := [.nonTerminal "outcome"] }
  ]

/-- Doing an action starts the world program on `[action, situation]`. -/
def unfoldRule (world : Code) : RewriteRule :=
  { name := "Unfold"
    typeContext := [("action", .base "Nat"), ("situation", .base "Nat")]
    premises := []
    left := .apply "Did" [.fvar "action", .fvar "situation"]
    right := .apply "Evolve"
      [.apply "Normal" [encCode world, .apply "HaltCont" [],
        .apply "Cons" [.fvar "action", .apply "Cons" [.fvar "situation", .apply "Nil" []]]]] }

/-- The world advances by a machine step of its configuration. -/
def evolveStepRule : RewriteRule :=
  { name := "EvolveStep"
    typeContext := [("cfg", .base "Cfg"), ("next", .base "Cfg")]
    premises := [.congruence (.fvar "cfg") (.fvar "next")]
    left := .apply "Evolve" [.fvar "cfg"]
    right := .apply "Evolve" [.fvar "next"] }

/-- The world halts, and the head of its output is the outcome. -/
def evolvedRule : RewriteRule :=
  { name := "Evolved"
    typeContext := [("outcome", .base "Nat"), ("rest", .base "Nats")]
    premises := []
    left := .apply "Evolve" [.apply "Halt" [.apply "Cons" [.fvar "outcome", .fvar "rest"]]]
    right := .apply "Outcome" [.fvar "outcome"] }

def consequenceRewrites (actionCount : ℕ) (world : Code) : List RewriteRule :=
  choiceRewrites actionCount ++ [unfoldRule world, evolveStepRule, evolvedRule]

/-- Choice points whose outcomes a world program evolves into consequences. -/
def consequenceLanguage (actionCount : ℕ) (world : Code) : LanguageDef :=
  LanguageDef.ofCore s!"Consequences{actionCount}" ["Nat", "Nats", "Code", "Cont", "Cfg", "World"]
    (terms ++ worldTerms ++ consequenceTerms) [] (consequenceRewrites actionCount world)

theorem consequenceLanguage_rewrites (actionCount : ℕ) (world : Code) :
    (consequenceLanguage actionCount world).rewrites = consequenceRewrites actionCount world := rfl

abbrev ConsequenceStep (actionCount : ℕ) (world : Code) : Pattern → Pattern → Prop :=
  Step choiceBase (consequenceLanguage actionCount world)

def evolving (cfg : Pattern) : Pattern := .apply "Evolve" [cfg]

def outcome (value : ℕ) : Pattern := .apply "Outcome" [encNat value]

/-! ## Forward: consequences are reached -/

theorem encCode_binderFree (c : Code) : binderFree (encCode c) = true := by
  induction c <;> simp_all [encCode, binderFree, binderFreeList]

theorem applyBindings_encCode (bindings : Bindings) (c : Code) :
    applyBindings bindings (encCode c) = encCode c := by
  induction c <;> simp_all [encCode, applyBindings]

theorem choiceRules_mem_consequence {actionCount : ℕ} {world : Code} :
    ∀ rule, rule ∈ (choiceLanguage actionCount).rewrites →
      rule ∈ (consequenceLanguage actionCount world).rewrites := by
  intro rule member
  simp only [consequenceLanguage_rewrites, consequenceRewrites, List.mem_append]
  exact .inl member

theorem choice_step_lifts {actionCount : ℕ} {world : Code} {source target : Pattern}
    (step : ChoiceStep actionCount source target) :
    ConsequenceStep actionCount world source target :=
  Step.mono_rules choiceRules_mem_consequence step

theorem unfold_steps (actionCount : ℕ) (world : Code) (action situation : ℕ) :
    ConsequenceStep actionCount world (did action situation)
      (evolving (normalTerm world .halt [action, situation])) := by
  have member : unfoldRule world ∈ (consequenceLanguage actionCount world).rewrites := by
    simp [consequenceLanguage_rewrites, consequenceRewrites]
  refine step_of_rule member (initialBindings :=
      [("situation", encNat situation), ("action", encNat action)]) ?_ .nil
    (finalBindings := [("situation", encNat situation), ("action", encNat action)]) ?_ ?_
  · simp [unfoldRule, did, matchPattern, matchArgs, mergeBindings]
  · simp [applyPremisesWithEnv, unfoldRule]
  · rw [applyBindingsForRule_eq_of_binderFree _ _ _ rfl
      (by simp [unfoldRule, binderFree, binderFreeList, encCode_binderFree])]
    simp [unfoldRule, evolving, normalTerm, encCont, encNats, applyBindings, applyBindings_encCode]

theorem evolve_step_lifts {actionCount : ℕ} {world : Code} {cfg next : Pattern}
    (reduces : Reduces cfg next) :
    ConsequenceStep actionCount world (evolving cfg) (evolving next) := by
  have member : evolveStepRule ∈ (consequenceLanguage actionCount world).rewrites := by
    simp [consequenceLanguage_rewrites, consequenceRewrites]
  refine step_of_single_congruence_rule member
    (initialBindings := [("cfg", cfg)])
    (premiseBindings := [("next", next)])
    (finalBindings := [("next", next), ("cfg", cfg)])
    (premiseSource := .fvar "cfg") (premiseTarget := .fvar "next") (candidate := next)
    ?_ rfl ?_ ?_ ?_ ?_
  · simp [evolveStepRule, evolving, matchPattern, matchArgs, mergeBindings]
  · simpa [applyBindings] using choice_step_lifts (world := world) (machine_step_lifts reduces)
  · simp [matchPattern]
  · simp [mergeBindings]
  · rw [applyBindingsForRule_eq_of_binderFree _ _ _ rfl rfl]
    simp [evolveStepRule, evolving, applyBindings]

theorem evolve_reduction_lifts {actionCount : ℕ} {world : Code} {cfg target : Pattern}
    (reduces : Relation.ReflTransGen Reduces cfg target) :
    Relation.ReflTransGen (ConsequenceStep actionCount world) (evolving cfg) (evolving target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (evolve_step_lifts last)

theorem evolved_steps (actionCount : ℕ) (world : Code) (value : ℕ) (rest : List ℕ) :
    ConsequenceStep actionCount world (evolving (encCfg (.halt (value :: rest)))) (outcome value) := by
  have member : evolvedRule ∈ (consequenceLanguage actionCount world).rewrites := by
    simp [consequenceLanguage_rewrites, consequenceRewrites]
  refine step_of_rule member (initialBindings :=
      [("rest", encNats rest), ("outcome", encNat value)]) ?_ .nil
    (finalBindings := [("rest", encNats rest), ("outcome", encNat value)]) ?_ ?_
  · simp [evolvedRule, evolving, encCfg, encNats, matchPattern, matchArgs, mergeBindings]
  · simp [applyPremisesWithEnv, evolvedRule]
  · rw [applyBindingsForRule_eq_of_binderFree _ _ _ rfl rfl]
    simp [evolvedRule, outcome, applyBindings]

/-- **Doing an action reaches the consequence the world computes.** -/
theorem did_reaches_outcome (actionCount : ℕ) {world : Code} {action situation value : ℕ}
    {rest : List ℕ} (computes : HaltsWith world [action, situation] (value :: rest)) :
    Relation.ReflTransGen (ConsequenceStep actionCount world) (did action situation) (outcome value) :=
  (Relation.ReflTransGen.single (unfold_steps actionCount world action situation)).trans
    ((evolve_reduction_lifts computes).tail (evolved_steps actionCount world value rest))

/-- **Taking a declared action at a scene reaches the consequence the world
computes.** -/
theorem scene_reaches_outcome {actionCount : ℕ} {world : Code} (agent : Code)
    {action situation value : ℕ} {rest : List ℕ} (inRange : action < actionCount)
    (computes : HaltsWith world [action, situation] (value :: rest)) :
    Relation.ReflTransGen (ConsequenceStep actionCount world) (scene agent situation)
      (outcome value) :=
  (Relation.ReflTransGen.single (choice_step_lifts (choose_steps inRange agent situation))).trans
    (did_reaches_outcome actionCount computes)

/-! ## Backward: only computed consequences are reached -/

/-- The constructor at the root of a pattern, if any. -/
def rootConstructor : Pattern → Option String
  | .apply constructor _ => some constructor
  | _ => none

theorem matchPattern_eq_nil_of_root_ne {left : Pattern} {constructor head : String}
    (root : rootConstructor left = some constructor) (different : constructor ≠ head)
    (args : List Pattern) : matchPattern left (.apply head args) = [] := by
  cases left <;> simp_all [rootConstructor, matchPattern]

theorem machine_rules_heads :
    (rewrites.all fun rule => rootConstructor rule.left == some "Normal" ||
      rootConstructor rule.left == some "Ret") = true := by
  decide +kernel

/-- A step, read off the rule that produced it. -/
theorem step_cases {actionCount : ℕ} {world : Code} {source target : Pattern}
    (step : ConsequenceStep actionCount world source target) :
    ∃ fuel rule initial final, rule ∈ consequenceRewrites actionCount world ∧
      initial ∈ matchPattern rule.left source ∧
      PremisesAt choiceBase (consequenceLanguage actionCount world) fuel initial rule.premises final ∧
      applyBindingsForRule (consequenceLanguage actionCount world) rule final = target := by
  obtain ⟨_, stepAt⟩ := step
  cases stepAt with
  | @rule fuel _ _ rule initial final member matched premises targetEq =>
      refine ⟨fuel, rule, initial, final, member, ?_, premises, targetEq⟩
      simpa [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations
        (rfl : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty.presentations = [])]
        using matched

theorem premisesAt_nil {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : ℕ}
    {initial final : Bindings} (premises : PremisesAt base lang fuel initial [] final) :
    final = initial := by
  cases premises
  rfl

/-- The rules whose left side can match a term with root constructor `head`, other
than the machine's. -/
theorem nonmachine_rule_cases {actionCount : ℕ} {world : Code} {rule : RewriteRule}
    (member : rule ∈ consequenceRewrites actionCount world) :
    rule ∈ rewrites ∨ (∃ action, rule = chooseRule action) ∨ rule = deliberateRule ∨
      rule = deliberationStepRule ∨ rule = decidedRule ∨ rule = unfoldRule world ∨
      rule = evolveStepRule ∨ rule = evolvedRule := by
  simp only [consequenceRewrites, choiceRewrites, actionRules, List.mem_append, List.mem_map,
    List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with ((inMachine | ⟨action, -, rfl⟩) | rfl | rfl | rfl) | rfl | rfl | rfl
  · exact .inl inMachine
  · exact .inr (.inl ⟨action, rfl⟩)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr (.inl rfl))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))

theorem matchPattern_machine_eq_nil {rule : RewriteRule} (inMachine : rule ∈ rewrites)
    {head : String} (notNormal : head ≠ "Normal") (notRet : head ≠ "Ret") (args : List Pattern) :
    matchPattern rule.left (.apply head args) = [] := by
  have certified := List.all_eq_true.mp machine_rules_heads rule inMachine
  simp only [Bool.or_eq_true, beq_iff_eq] at certified
  rcases certified with root | root
  · exact matchPattern_eq_nil_of_root_ne root (Ne.symm notNormal) args
  · exact matchPattern_eq_nil_of_root_ne root (Ne.symm notRet) args

/-- **On machine configurations the extended language is the machine.** -/
theorem consequenceStep_machine_iff {actionCount : ℕ} {world : Code} {term target : Pattern}
    (image : InImage term) : ConsequenceStep actionCount world term target ↔ Reduces term target := by
  refine ⟨fun step => ?_, fun reduces => choice_step_lifts (machine_step_lifts reduces)⟩
  obtain ⟨fuel, rule, initial, final, member, matched, premises, targetEq⟩ := step_cases step
  rcases nonmachine_rule_cases member with inMachine | ⟨action, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  · have unconditional := List.all_eq_true.mp partrecMachine_unconditional rule
      (by simpa [partrecMachine_rewrites] using inMachine)
    simp only [Bool.and_eq_true, List.isEmpty_iff] at unconditional
    rw [unconditional.1] at premises
    obtain rfl := premisesAt_nil premises
    refine ⟨fuel + 1, .rule (initialBindings := final)
      (by simpa [partrecMachine_rewrites] using inMachine) ?_ ?_ targetEq⟩
    · simpa [matchPatternForRule, matchPatternForRule_eq_syntactic_of_no_presentations
        (rfl : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty.presentations = [])]
        using matched
    · rw [unconditional.1]
      exact .nil _
  all_goals
    rcases image with ⟨c, k, v, rfl⟩ | ⟨cfg, rfl⟩
    · simp [chooseRule, deliberateRule, deliberationStepRule, decidedRule, unfoldRule, evolveStepRule,
        evolvedRule, normalTerm, matchPattern] at matched
    · cases cfg <;>
        simp [chooseRule, deliberateRule, deliberationStepRule, decidedRule, unfoldRule, evolveStepRule,
          evolvedRule, encCfg, matchPattern] at matched

/-- **A running world either advances by a machine step or yields its outcome.** -/
theorem consequenceStep_evolving {actionCount : ℕ} {world : Code} {cfg target : Pattern}
    (image : InImage cfg) (step : ConsequenceStep actionCount world (evolving cfg) target) :
    (∃ next, Reduces cfg next ∧ target = evolving next) ∨
      ∃ value rest, cfg = encCfg (.halt (value :: rest)) ∧ target = outcome value := by
  obtain ⟨fuel, rule, initial, final, member, matched, premises, targetEq⟩ := step_cases step
  rcases nonmachine_rule_cases member with inMachine | ⟨action, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [evolving, matchPattern_machine_eq_nil inMachine] at matched
  · simp [chooseRule, evolving, matchPattern] at matched
  · simp [deliberateRule, evolving, matchPattern] at matched
  · simp [deliberationStepRule, evolving, matchPattern] at matched
  · simp [decidedRule, evolving, matchPattern] at matched
  · simp [unfoldRule, evolving, matchPattern] at matched
  · -- the congruence rule
    simp [evolveStepRule, evolving, matchPattern, matchArgs, mergeBindings] at matched
    subst matched
    simp only [evolveStepRule] at premises
    cases premises with
    | cons premise rest =>
        obtain rfl := premisesAt_nil rest
        cases premise with
        | @congruence _ _ premiseBindings _ _ _ candidate recursive premiseMatched merged =>
            rw [show matchPattern (.fvar "next") candidate = [[("next", candidate)]] by
              simp [matchPattern], List.mem_singleton] at premiseMatched
            subst premiseMatched
            simp [mergeBindings] at merged
            subst merged
            rw [show applyBindings [("cfg", cfg)] (.fvar "cfg") = cfg by simp [applyBindings]]
              at recursive
            refine .inl ⟨candidate, (consequenceStep_machine_iff image).mp ⟨fuel, recursive⟩, ?_⟩
            rw [← targetEq, applyBindingsForRule_eq_of_binderFree _ _ _ rfl rfl]
            simp [evolveStepRule, evolving, applyBindings]
  · -- the halting rule
    obtain rfl := premisesAt_nil premises
    rcases image with ⟨c, k, v, rfl⟩ | ⟨cfg, rfl⟩
    · simp [evolvedRule, evolving, normalTerm, matchPattern, matchArgs] at matched
    · cases cfg with
      | ret k v => simp [evolvedRule, evolving, encCfg, matchPattern, matchArgs] at matched
      | halt v =>
          cases v with
          | nil => simp [evolvedRule, evolving, encCfg, encNats, matchPattern, matchArgs] at matched
          | cons value rest =>
              simp [evolvedRule, evolving, encCfg, encNats, matchPattern, matchArgs, mergeBindings]
                at matched
              subst matched
              refine .inr ⟨value, rest, rfl, ?_⟩
              rw [← targetEq, applyBindingsForRule_eq_of_binderFree _ _ _ rfl rfl]
              simp [evolvedRule, outcome, applyBindings]

/-- **Doing an action has one step: starting the world.** -/
theorem consequenceStep_did {actionCount : ℕ} {world : Code} {action situation : ℕ} {target : Pattern}
    (step : ConsequenceStep actionCount world (did action situation) target) :
    target = evolving (normalTerm world .halt [action, situation]) := by
  obtain ⟨fuel, rule, initial, final, member, matched, premises, targetEq⟩ := step_cases step
  rcases nonmachine_rule_cases member with inMachine | ⟨action', rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [did, matchPattern_machine_eq_nil inMachine] at matched
  · simp [chooseRule, did, matchPattern] at matched
  · simp [deliberateRule, did, matchPattern] at matched
  · simp [deliberationStepRule, did, matchPattern] at matched
  · simp [decidedRule, did, matchPattern] at matched
  · obtain rfl := premisesAt_nil premises
    simp [unfoldRule, did, matchPattern, matchArgs, mergeBindings] at matched
    subst matched
    rw [← targetEq, applyBindingsForRule_eq_of_binderFree _ _ _ rfl
      (by simp [unfoldRule, binderFree, binderFreeList, encCode_binderFree])]
    simp [unfoldRule, evolving, normalTerm, encCont, encNats, applyBindings, applyBindings_encCode]
  · simp [evolveStepRule, did, matchPattern] at matched
  · simp [evolvedRule, did, matchPattern] at matched

/-- **An outcome is final.** -/
theorem outcome_irreducible {actionCount : ℕ} {world : Code} (value : ℕ) (target : Pattern) :
    ¬ ConsequenceStep actionCount world (outcome value) target := by
  intro step
  obtain ⟨fuel, rule, initial, final, member, matched, premises, targetEq⟩ := step_cases step
  rcases nonmachine_rule_cases member with inMachine | ⟨action', rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [outcome, matchPattern_machine_eq_nil inMachine] at matched
  all_goals
    simp [chooseRule, deliberateRule, deliberationStepRule, decidedRule, unfoldRule, evolveStepRule,
      evolvedRule, outcome, matchPattern] at matched

theorem outcome_of_evolving {actionCount : ℕ} {world : Code} {value : ℕ} {start : Pattern}
    (reaches : Relation.ReflTransGen (ConsequenceStep actionCount world) start (outcome value)) :
    ∀ cfg, InImage cfg → start = evolving cfg →
      ∃ rest, Relation.ReflTransGen Reduces cfg (encCfg (.halt (value :: rest))) := by
  induction reaches using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro cfg _ same
      simp [outcome, evolving] at same
  | head step rest ih =>
      intro cfg image same
      subst same
      rcases consequenceStep_evolving image step with ⟨next, reduces, rfl⟩ | ⟨produced, tail, rfl, rfl⟩
      · obtain ⟨tail, reaches⟩ := ih next (reduct_inImage image reduces) rfl
        exact ⟨tail, .head reduces reaches⟩
      · rcases Relation.ReflTransGen.cases_head rest with same | ⟨next, stepped, _⟩
        · have := encNat_injective (by simpa [outcome] using same)
          subst this
          exact ⟨tail, .refl⟩
        · exact absurd stepped (outcome_irreducible produced next)

/-- **Doing an action reaches exactly the consequences the world computes.** -/
theorem did_reaches_outcome_iff {actionCount : ℕ} {world : Code} {action situation value : ℕ} :
    Relation.ReflTransGen (ConsequenceStep actionCount world) (did action situation) (outcome value) ↔
      ∃ rest, HaltsWith world [action, situation] (value :: rest) := by
  refine ⟨fun reaches => ?_, fun ⟨_, computes⟩ => did_reaches_outcome actionCount computes⟩
  rcases Relation.ReflTransGen.cases_head reaches with same | ⟨next, stepped, rest⟩
  · simp [did, outcome] at same
  · rw [consequenceStep_did stepped] at rest
    exact outcome_of_evolving rest _ (.inl ⟨world, .halt, [action, situation], rfl⟩) rfl

/-! ## Consequence reachability is undecidable in the world -/

/-- The world programs in which doing `action` in `situation` can lead to an
outcome satisfying `ideal`. -/
def IdealReachable (actionCount : ℕ) (ideal : ℕ → Prop) (action situation : ℕ) : Set Code :=
  {world | ∃ value, ideal value ∧
    Relation.ReflTransGen (ConsequenceStep actionCount world) (did action situation) (outcome value)}

theorem mem_idealReachable_iff {actionCount : ℕ} {ideal : ℕ → Prop} {action situation : ℕ}
    {world : Code} :
    world ∈ IdealReachable actionCount ideal action situation ↔
      ∃ value rest, ideal value ∧ HaltsWith world [action, situation] (value :: rest) := by
  simp only [IdealReachable, Set.mem_ofPred_eq, did_reaches_outcome_iff]
  constructor
  · rintro ⟨value, isIdeal, rest, computes⟩
    exact ⟨value, rest, isIdeal, computes⟩
  · rintro ⟨value, rest, isIdeal, computes⟩
    exact ⟨value, isIdeal, rest, computes⟩

theorem idealReachable_invariant (actionCount : ℕ) (ideal : ℕ → Prop) (action situation : ℕ) :
    ObservationInvariant HaltsWith (IdealReachable actionCount ideal action situation) := by
  intro first second same
  simp only [mem_idealReachable_iff, same]

/-- **Whether an act can lead to an ideal outcome is undecidable in the world
program.** -/
theorem idealReachable_not_computable (actionCount : ℕ) {ideal : ℕ → Prop} (action situation : ℕ)
    (someIdeal : ∃ value, ideal value) :
    ¬ ComputablePred (· ∈ IdealReachable actionCount ideal action situation) := by
  obtain ⟨value, isIdeal⟩ := someIdeal
  refine rice (idealReachable_invariant actionCount ideal action situation)
    ⟨⟨compile (Nat.Partrec.Code.const value), mem_idealReachable_iff.mpr ⟨value, [], isIdeal, ?_⟩⟩,
      ⟨silent, fun member => ?_⟩⟩
  · exact haltsWith_iff.mpr (by rw [compile_eval]; simp)
  · obtain ⟨_, _, _, computes⟩ := mem_idealReachable_iff.mp member
    have := haltsWith_iff.mp computes
    simp [silent_eval] at this

#print axioms did_reaches_outcome
#print axioms scene_reaches_outcome
#print axioms did_reaches_outcome_iff
#print axioms idealReachable_not_computable

end Mettapedia.Languages.ChoicePoints
