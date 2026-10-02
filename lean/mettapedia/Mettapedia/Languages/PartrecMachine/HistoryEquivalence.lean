import Mettapedia.Languages.PartrecMachine.HistoryCarrier
import Mettapedia.OSLF.MeTTaIL.RuleInstances
import Mettapedia.OSLF.MeTTaIL.MatchBindingExtension

/-!
# The static equivalence of the history machine is halting

For an encoded configuration `c` of the partial-recursive machine, the
histories `Now(c)` and `Flag(c)` are equal in the interacting fibre of the
history theory exactly when `c` reduces to a halted configuration
(`now_equivalent_flag_iff`).

* If `c` halts, the equations record the run step by step, mark its last
  configuration as finished, and carry the mark back to the start.
* Conversely, read a history as a claim: `Now(c)` claims that `c` halts,
  `Flag(c)` claims nothing, `Then(c, h)` and a prefixed history claim what the
  history under them claims, and a contact claims what both of its sides
  claim.  Every equation step between history terms preserves the truth of the
  claim, because the machine is deterministic on encoded configurations.
  `Flag(c)` is true, so anything equal to it is true, and `Now(c)` is true
  only if `c` halts.

The claim is preserved for arbitrary history terms, not only for the two in
the statement, and the fibre contains nothing but history terms; that is what
makes the argument a statement about the equivalence and not about one chain
of equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.MatchBindingExtension
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Turing.ToPartrec

/-! ## Matching a constructor application -/

/-- A unary application schema matches exactly the unary applications of the
same constructor whose argument the inner schema matches. -/
theorem mem_matchPattern_apply_one {label : String} {schema source : Pattern}
    {bindings : Bindings} :
    bindings ∈ matchPattern (.apply label [schema]) source ↔
      ∃ term, source = .apply label [term] ∧ bindings ∈ matchPattern schema term := by
  constructor
  · intro matched
    have relation := matchPattern_sound matched
    cases relation with
    | apply arguments _ =>
        cases arguments with
        | cons head tail merged =>
            cases tail with
            | nil =>
                obtain rfl : _ = bindings := by simpa [mergeBindings] using merged
                exact ⟨_, rfl, matchRel_complete head⟩
  · rintro ⟨term, rfl, matched⟩
    exact matchRel_complete
      (.apply (.cons (matchPattern_sound matched) .nil rfl) rfl)

/-- A binary application schema matches only binary applications of the same
constructor, with the two arguments matched separately and the two binding
lists merged. -/
theorem mem_matchPattern_apply_two {label : String} {first second source : Pattern}
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern (.apply label [first, second]) source) :
    ∃ left right leftBindings rightBindings,
      source = .apply label [left, right] ∧
        leftBindings ∈ matchPattern first left ∧
          rightBindings ∈ matchPattern second right ∧
            mergeBindings leftBindings rightBindings = some bindings := by
  have relation := matchPattern_sound matched
  cases relation with
  | apply arguments _ =>
      cases arguments with
      | cons head tail merged =>
          cases tail with
          | cons inner rest innerMerged =>
              cases rest with
              | nil =>
                  obtain rfl : _ = _ := by simpa [mergeBindings] using innerMerged
                  exact ⟨_, _, _, _, rfl, matchRel_complete head, matchRel_complete inner,
                    merged⟩

/-! ## Instantiating the history constructors -/

@[simp] theorem applyBindings_now (bindings : Bindings) (configuration : Pattern) :
    applyBindings bindings (now configuration) = now (applyBindings bindings configuration) := by
  simp [now, applyBindings]

@[simp] theorem applyBindings_flag (bindings : Bindings) (configuration : Pattern) :
    applyBindings bindings (flag configuration) =
      flag (applyBindings bindings configuration) := by
  simp [flag, applyBindings]

@[simp] theorem applyBindings_andThen (bindings : Bindings) (configuration history : Pattern) :
    applyBindings bindings (andThen configuration history) =
      andThen (applyBindings bindings configuration) (applyBindings bindings history) := by
  simp [andThen, applyBindings]

theorem now_injective {first second : Pattern} (same : now first = now second) :
    first = second := by
  simpa [now] using same

theorem andThen_injective {first second firstHistory secondHistory : Pattern}
    (same : andThen first firstHistory = andThen second secondHistory) :
    first = second ∧ firstHistory = secondHistory := by
  simpa [andThen] using same

/-! ## Reduction of the machine, rule by rule -/

/-- Every machine rule is premise-free, moves no variable across a binder,
and has both sides matched exactly. -/
theorem rewrites_plain :
    rewrites.all (fun rule =>
      rule.premises.isEmpty && ruleDepthAligned rule &&
        Pattern.isMatchCorrect rule.left && Pattern.isMatchCorrect rule.right) = true := by
  decide +kernel

theorem partrecMachine_plainRules : PlainRules partrecMachine := by
  intro rule membership
  have plain := List.all_eq_true.mp rewrites_plain rule membership
  simp only [Bool.and_eq_true, List.isEmpty_iff] at plain
  exact ⟨plain.1.1.1, plain.1.1.2⟩

theorem rule_left_matchCorrect {rule : RewriteRule} (membership : rule ∈ rewrites) :
    Pattern.isMatchCorrect rule.left = true := by
  have plain := List.all_eq_true.mp rewrites_plain rule membership
  simp only [Bool.and_eq_true] at plain
  exact plain.1.2

theorem rule_right_matchCorrect {rule : RewriteRule} (membership : rule ∈ rewrites) :
    Pattern.isMatchCorrect rule.right = true := by
  have plain := List.all_eq_true.mp rewrites_plain rule membership
  simp only [Bool.and_eq_true] at plain
  exact plain.2

/-- A rule whose left side matches a term reduces it to the instance of its
right side. -/
theorem reduces_of_match {rule : RewriteRule} (membership : rule ∈ rewrites)
    {term : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern rule.left term) :
    Reduces term (applyBindings bindings rule.right) :=
  (step_iff_exists_match partrecMachine_plainRules).mpr
    ⟨rule, membership, bindings, matched, rfl⟩

/-- A reduction is an instance of a rule. -/
theorem exists_match_of_reduces {source target : Pattern} (step : Reduces source target) :
    ∃ rule ∈ rewrites, ∃ bindings ∈ matchPattern rule.left source,
      applyBindings bindings rule.right = target :=
  (step_iff_exists_match partrecMachine_plainRules).mp step

/-! ## Halting -/

/-- The configuration reduces to a halted configuration. -/
def Halts (configuration : Pattern) : Prop :=
  ∃ output : List ℕ, Relation.ReflTransGen Reduces configuration (encCfg (.halt output))

/-- On an encoded configuration, halting is invariant under one step: the
machine is deterministic there. -/
theorem halts_iff_of_reduces {source target : Pattern} (image : InImage source)
    (step : Reduces source target) : Halts source ↔ Halts target := by
  constructor
  · rintro ⟨output, path⟩
    rcases Relation.ReflTransGen.cases_head path with same | ⟨middle, first, rest⟩
    · rw [same] at step
      exact absurd step (halt_irreducible output target)
    · rw [reduces_deterministic image step first]
      exact ⟨output, rest⟩
  · rintro ⟨output, path⟩
    exact ⟨output, .head step path⟩

/-- An encoded configuration headed by `Halt` is halted. -/
theorem halts_of_halted {values : Pattern} (image : InImage (.apply "Halt" [values])) :
    Halts (.apply "Halt" [values]) := by
  rcases image with ⟨code, continuation, input, same⟩ | ⟨cfg, same⟩
  · simp [normalTerm] at same
  · cases cfg with
    | halt output =>
        rw [same]
        exact ⟨output, .refl⟩
    | ret continuation output => simp [encCfg] at same

/-! ## What a history claims -/

/-- The claim a history makes: every `Now` in it, outside the configurations,
is on a configuration that halts. -/
inductive Holds : Pattern → Prop where
  | ofNow {configuration : Pattern} : Halts configuration → Holds (now configuration)
  | ofThen {configuration history : Pattern} :
      Holds history → Holds (andThen configuration history)
  | ofFlag (configuration : Pattern) : Holds (flag configuration)
  | ofMeet {left right : Pattern} : Holds left → Holds right → Holds (meet left right)
  | ofWait {history : Pattern} : Holds history → Holds (wait history)
  | ofGive {history : Pattern} : Holds history → Holds (give history)

theorem holds_now_iff {configuration : Pattern} :
    Holds (now configuration) ↔ Halts configuration := by
  constructor
  · intro holds
    generalize shape : now configuration = pattern at holds
    cases holds with
    | ofNow halts =>
        obtain rfl := now_injective shape
        exact halts
    | ofThen _ => simp [now, andThen] at shape
    | ofFlag _ => simp [now, flag] at shape
    | ofMeet _ _ => simp [now, meet] at shape
    | ofWait _ => simp [now, wait] at shape
    | ofGive _ => simp [now, give] at shape
  · exact Holds.ofNow

theorem holds_andThen_iff {configuration history : Pattern} :
    Holds (andThen configuration history) ↔ Holds history := by
  constructor
  · intro holds
    generalize shape : andThen configuration history = pattern at holds
    cases holds with
    | ofNow _ => simp [now, andThen] at shape
    | ofThen inner =>
        obtain ⟨-, rfl⟩ := andThen_injective shape
        exact inner
    | ofFlag _ => simp [andThen, flag] at shape
    | ofMeet _ _ => simp [andThen, meet] at shape
    | ofWait _ => simp [andThen, wait] at shape
    | ofGive _ => simp [andThen, give] at shape
  · exact Holds.ofThen

theorem holds_meet_iff {left right : Pattern} :
    Holds (meet left right) ↔ Holds left ∧ Holds right := by
  constructor
  · intro holds
    generalize shape : meet left right = pattern at holds
    cases holds with
    | ofNow _ => simp [now, meet] at shape
    | ofThen _ => simp [andThen, meet] at shape
    | ofFlag _ => simp [meet, flag] at shape
    | ofMeet first second =>
        simp only [meet, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain ⟨rfl, rfl⟩ := shape
        exact ⟨first, second⟩
    | ofWait _ => simp [meet, wait] at shape
    | ofGive _ => simp [meet, give] at shape
  · rintro ⟨first, second⟩
    exact Holds.ofMeet first second

theorem holds_wait_iff {history : Pattern} : Holds (wait history) ↔ Holds history := by
  constructor
  · intro holds
    generalize shape : wait history = pattern at holds
    cases holds with
    | ofNow _ => simp [now, wait] at shape
    | ofThen _ => simp [andThen, wait] at shape
    | ofFlag _ => simp [wait, flag] at shape
    | ofMeet _ _ => simp [meet, wait] at shape
    | ofWait inner =>
        simp only [wait, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain rfl := shape
        exact inner
    | ofGive _ => simp [wait, give] at shape
  · exact Holds.ofWait

theorem holds_give_iff {history : Pattern} : Holds (give history) ↔ Holds history := by
  constructor
  · intro holds
    generalize shape : give history = pattern at holds
    cases holds with
    | ofNow _ => simp [now, give] at shape
    | ofThen _ => simp [andThen, give] at shape
    | ofFlag _ => simp [give, flag] at shape
    | ofMeet _ _ => simp [meet, give] at shape
    | ofWait _ => simp [wait, give] at shape
    | ofGive inner =>
        simp only [give, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain rfl := shape
        exact inner
  · exact Holds.ofGive

/-! ## Equation instances preserve the claim -/

/-- The weight of a pattern does not decrease when it is placed in a
context. -/
theorem weigh_le_fill (weight : String → Nat) :
    ∀ (context : OneHoleContext) (pattern : Pattern),
      pattern.weigh weight ≤ (context.fill pattern).weigh weight
  | .hole, _ => Nat.le_refl _
  | .apply label before inner after, pattern => by
      have recurse := weigh_le_fill weight inner pattern
      simp only [OneHoleContext.fill, Pattern.weigh, Pattern.weighList_append,
        Pattern.weighList]
      omega
  | .lambda _ inner, pattern => by
      simpa [OneHoleContext.fill, Pattern.weigh] using weigh_le_fill weight inner pattern
  | .multiLambda _ _ inner, pattern => by
      simpa [OneHoleContext.fill, Pattern.weigh] using weigh_le_fill weight inner pattern
  | .substBody inner replacement, pattern => by
      have recurse := weigh_le_fill weight inner pattern
      simp only [OneHoleContext.fill, Pattern.weigh]
      omega
  | .substReplacement body inner, pattern => by
      have recurse := weigh_le_fill weight inner pattern
      simp only [OneHoleContext.fill, Pattern.weigh]
      omega
  | .collection _ before inner after _, pattern => by
      have recurse := weigh_le_fill weight inner pattern
      simp only [OneHoleContext.fill, Pattern.weigh, Pattern.weighList_append,
        Pattern.weighList]
      omega

theorem one_le_weigh_now (configuration : Pattern) :
    1 ≤ (now configuration).weigh histWeight := by
  simp [now, Pattern.weigh, histWeight]

theorem one_le_weigh_flag (configuration : Pattern) :
    1 ≤ (flag configuration).weigh histWeight := by
  simp [flag, Pattern.weigh, histWeight]

theorem one_le_weigh_andThen (configuration history : Pattern) :
    1 ≤ (andThen configuration history).weigh histWeight := by
  simp [andThen, Pattern.weigh, histWeight]

/-- What the analysis of one equation instance provides: both sides are
headed by a history constructor, and between history terms the claim is
preserved. -/
def PreservesClaim (redex contractum : Pattern) : Prop :=
  1 ≤ redex.weigh histWeight ∧ 1 ≤ contractum.weigh histWeight ∧
    (HistTerm redex → HistTerm contractum → (Holds redex ↔ Holds contractum))

/-- The equations of the history machine, by family. -/
theorem mem_historyEquations {equation : Equation}
    (membership : List.Mem equation historyMachine.equations) :
    equation = haltLaw ∨ (∃ rule, rule ∈ rewrites ∧ equation = nowLaw rule) ∨
      ∃ rule, rule ∈ rewrites ∧ equation = flagLaw rule := by
  have listed : equation ∈ historyEquations := membership
  simp only [historyEquations, List.mem_cons, List.mem_append, List.mem_map] at listed
  rcases listed with rfl | ⟨rule, inRules, rfl⟩ | ⟨rule, inRules, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨rule, inRules, rfl⟩)
  · exact .inr (.inr ⟨rule, inRules, rfl⟩)

/-- The halting law, read from left to right. -/
theorem haltLaw_forward {redex contractum : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern haltLaw.left redex)
    (applied : applyBindings bindings haltLaw.right = contractum) :
    PreservesClaim redex contractum := by
  obtain ⟨term, rfl, inner⟩ := mem_matchPattern_apply_one.mp matched
  obtain ⟨values, rfl, -⟩ := mem_matchPattern_apply_one.mp inner
  have shape : contractum = flag (applyBindings bindings (.apply "Halt" [.fvar "w"])) := by
    rw [← applied]
    exact applyBindings_flag bindings _
  subst shape
  refine ⟨one_le_weigh_now _, one_le_weigh_flag _, fun source _ => ?_⟩
  exact ⟨fun _ => Holds.ofFlag _,
    fun _ => holds_now_iff.mpr (halts_of_halted (HistTerm.now_inv source))⟩

/-- The halting law, read from right to left. -/
theorem haltLaw_reverse {redex contractum : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern haltLaw.right redex)
    (applied : applyBindings bindings haltLaw.left = contractum) :
    PreservesClaim redex contractum := by
  obtain ⟨term, rfl, -⟩ := mem_matchPattern_apply_one.mp matched
  have shape : contractum =
      now (.apply "Halt" [applyBindings bindings (.fvar "w")]) := by
    rw [← applied]
    simp [haltLaw, applyBindings]
  subst shape
  refine ⟨one_le_weigh_flag _, one_le_weigh_now _, fun _ target => ?_⟩
  exact ⟨fun _ => holds_now_iff.mpr (halts_of_halted (HistTerm.now_inv target)),
    fun _ => Holds.ofFlag _⟩

/-- A step law, read from left to right: `Now(l)` becomes `Then(l, Now(r))`. -/
theorem nowLaw_forward {rule : RewriteRule} (inRules : rule ∈ rewrites)
    {redex contractum : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (nowLaw rule).left redex)
    (applied : applyBindings bindings (nowLaw rule).right = contractum) :
    PreservesClaim redex contractum := by
  obtain ⟨term, rfl, inner⟩ := mem_matchPattern_apply_one.mp matched
  have left : applyBindings bindings rule.left = term :=
    matchPattern_correct inner (rule_left_matchCorrect inRules)
  have shape : contractum = andThen term (now (applyBindings bindings rule.right)) := by
    rw [← applied]
    show applyBindings bindings (andThen rule.left (now rule.right)) = _
    rw [applyBindings_andThen, applyBindings_now, left]
  subst shape
  have step : Reduces term (applyBindings bindings rule.right) := reduces_of_match inRules inner
  refine ⟨one_le_weigh_now _, one_le_weigh_andThen _ _, fun source _ => ?_⟩
  show Holds (now term) ↔ Holds (andThen term (now (applyBindings bindings rule.right)))
  rw [holds_now_iff, holds_andThen_iff, holds_now_iff]
  exact halts_iff_of_reduces (HistTerm.now_inv source) step

/-- A step law, read from right to left: `Then(l, Now(r))` becomes `Now(l)`. -/
theorem nowLaw_reverse {rule : RewriteRule} (inRules : rule ∈ rewrites)
    {redex contractum : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (nowLaw rule).right redex)
    (applied : applyBindings bindings (nowLaw rule).left = contractum) :
    PreservesClaim redex contractum := by
  obtain ⟨first, rest, leftBindings, rightBindings, rfl, leftMatched, rightMatched, merged⟩ :=
    mem_matchPattern_apply_two matched
  obtain ⟨second, rfl, -⟩ := mem_matchPattern_apply_one.mp rightMatched
  have whole : applyBindings bindings (andThen rule.left (now rule.right)) =
      andThen first (now second) :=
    matchPattern_correct matched (by
      simp [andThen, now, Pattern.isMatchCorrect, isMatchCorrectAux, isMatchCorrectListAux]
      exact ⟨rule_left_matchCorrect inRules, rule_right_matchCorrect inRules⟩)
  rw [applyBindings_andThen, applyBindings_now] at whole
  obtain ⟨left, right⟩ := andThen_injective whole
  have right' : applyBindings bindings rule.right = second := now_injective right
  have shape : contractum = now first := by
    rw [← applied]
    show applyBindings bindings (now rule.left) = _
    rw [applyBindings_now, left]
  subst shape
  refine ⟨one_le_weigh_andThen _ _, one_le_weigh_now _, fun source _ => ?_⟩
  obtain ⟨image, -⟩ := HistTerm.andThen_inv source
  have step : Reduces first (applyBindings leftBindings rule.right) :=
    reduces_of_match inRules leftMatched
  have ground : (applyBindings leftBindings rule.right).isGround = true :=
    inImage_isGround (reduct_inImage image step)
  have same : applyBindings bindings rule.right = applyBindings leftBindings rule.right :=
    applyBindings_eq_of_extends_of_ground (rule_right_matchCorrect inRules)
      (fun _ _ found => mergeBindings_subsumed_left merged found) ground
  rw [← same, right'] at step
  show Holds (andThen first (now second)) ↔ Holds (now first)
  rw [holds_andThen_iff, holds_now_iff, holds_now_iff]
  exact (halts_iff_of_reduces image step).symm

/-- A carrying law, read from left to right: both sides claim nothing false. -/
theorem flagLaw_forward {rule : RewriteRule}
    {redex contractum : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (flagLaw rule).left redex)
    (applied : applyBindings bindings (flagLaw rule).right = contractum) :
    PreservesClaim redex contractum := by
  obtain ⟨first, rest, leftBindings, rightBindings, rfl, -, rightMatched, -⟩ :=
    mem_matchPattern_apply_two matched
  obtain ⟨second, rfl, -⟩ := mem_matchPattern_apply_one.mp rightMatched
  have shape : contractum = flag (applyBindings bindings rule.left) := by
    rw [← applied]
    exact applyBindings_flag bindings _
  subst shape
  exact ⟨one_le_weigh_andThen _ _, one_le_weigh_flag _, fun _ _ =>
    ⟨fun _ => Holds.ofFlag _, fun _ => Holds.ofThen (Holds.ofFlag _)⟩⟩

/-- A carrying law, read from right to left. -/
theorem flagLaw_reverse {rule : RewriteRule}
    {redex contractum : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (flagLaw rule).right redex)
    (applied : applyBindings bindings (flagLaw rule).left = contractum) :
    PreservesClaim redex contractum := by
  obtain ⟨term, rfl, -⟩ := mem_matchPattern_apply_one.mp matched
  have shape : contractum =
      andThen (applyBindings bindings rule.left) (flag (applyBindings bindings rule.right)) := by
    rw [← applied]
    show applyBindings bindings (andThen rule.left (flag rule.right)) = _
    rw [applyBindings_andThen, applyBindings_flag]
  subst shape
  exact ⟨one_le_weigh_flag _, one_le_weigh_andThen _ _, fun _ _ =>
    ⟨fun _ => Holds.ofThen (Holds.ofFlag _), fun _ => Holds.ofFlag _⟩⟩

/-- **Every instance of an authored equation preserves the claim** between
history terms, and both of its sides are headed by a history constructor. -/
theorem equationInstance_preservesClaim {base : BasePremiseEvaluator}
    {redex contractum : Pattern}
    (authored : EquationInstance base historyMachine redex contractum) :
    PreservesClaim redex contractum := by
  obtain ⟨fuel, located⟩ := authored
  cases located with
  | @forward equation _ _ initial final membership matched premises applied =>
      rcases mem_historyEquations membership with rfl | ⟨rule, inRules, rfl⟩ |
        ⟨rule, inRules, rfl⟩
      · cases premises
        exact haltLaw_forward matched applied
      · cases premises
        exact nowLaw_forward inRules matched applied
      · cases premises
        exact flagLaw_forward matched applied
  | @reverse equation _ _ initial final membership matched premises applied =>
      rcases mem_historyEquations membership with rfl | ⟨rule, inRules, rfl⟩ |
        ⟨rule, inRules, rfl⟩
      · cases premises
        exact haltLaw_reverse matched applied
      · cases premises
        exact nowLaw_reverse inRules matched applied
      · cases premises
        exact flagLaw_reverse matched applied

/-! ## Equation steps in context preserve the claim -/

/-- A one-element list split around an element. -/
theorem append_cons_eq_singleton {α : Type*} {before after : List α} {middle only : α}
    (same : before ++ middle :: after = [only]) :
    before = [] ∧ middle = only ∧ after = [] := by
  cases before with
  | nil => simpa using same
  | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at same
      exact absurd same.2 (by simp)

/-- A two-element list split around an element. -/
theorem append_cons_eq_pair {α : Type*} {before after : List α} {middle first second : α}
    (same : before ++ middle :: after = [first, second]) :
    (before = [] ∧ middle = first ∧ after = [second]) ∨
      (before = [first] ∧ middle = second ∧ after = []) := by
  cases before with
  | nil => exact .inl (by simpa using same)
  | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at same
      obtain ⟨rfl, rest⟩ := same
      obtain ⟨rfl, rfl, rfl⟩ := append_cons_eq_singleton rest
      exact .inr ⟨rfl, rfl, rfl⟩

/-- An encoded configuration contains no term headed by a history
constructor. -/
theorem not_inImage_fill {inner : OneHoleContext} {redex : Pattern}
    (heavy : 1 ≤ redex.weigh histWeight) : ¬ InImage (inner.fill redex) := by
  intro image
  have weightless := (inImage_machineTerm image).2.2.2
  have bound := weigh_le_fill histWeight inner redex
  omega

/-- **The claim is preserved in context.**  If replacing a term headed by a
history constructor by another one preserves the claim, then doing so inside
a history term preserves the claim of the whole. -/
theorem holds_fill_iff :
    ∀ (context : OneHoleContext) {redex contractum : Pattern},
      HistTerm (context.fill redex) → HistTerm (context.fill contractum) →
        PreservesClaim redex contractum →
          (Holds (context.fill redex) ↔ Holds (context.fill contractum))
  | .hole, _, _, source, target, preserves => preserves.2.2 source target
  | .apply label before inner after, redex, contractum, source, target, preserves => by
      simp only [OneHoleContext.fill] at source target ⊢
      rcases HistTerm.apply_inv source with
        ⟨rfl, configuration, shape, image⟩ |
        ⟨rfl, configuration, history, shape, image, historyTerm⟩ |
        ⟨rfl, configuration, shape, image⟩ |
        ⟨rfl, left, right, shape, leftTerm, rightTerm⟩ |
        ⟨rfl, history, shape, historyTerm⟩ |
        ⟨rfl, history, shape, historyTerm⟩
      · obtain ⟨rfl, rfl, rfl⟩ := append_cons_eq_singleton shape
        exact absurd image (not_inImage_fill preserves.1)
      · rcases append_cons_eq_pair shape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact absurd image (not_inImage_fill preserves.1)
        · have target' : HistTerm (andThen configuration (inner.fill contractum)) := target
          have recurse := holds_fill_iff inner historyTerm (HistTerm.andThen_inv target').2
            preserves
          show Holds (andThen configuration (inner.fill redex)) ↔
            Holds (andThen configuration (inner.fill contractum))
          rw [holds_andThen_iff, holds_andThen_iff]
          exact recurse
      · obtain ⟨rfl, rfl, rfl⟩ := append_cons_eq_singleton shape
        exact absurd image (not_inImage_fill preserves.1)
      · rcases append_cons_eq_pair shape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · have target' : HistTerm (meet (inner.fill contractum) right) := target
          have recurse := holds_fill_iff inner leftTerm (HistTerm.meet_inv target').1 preserves
          show Holds (meet (inner.fill redex) right) ↔ Holds (meet (inner.fill contractum) right)
          rw [holds_meet_iff, holds_meet_iff, recurse]
        · have target' : HistTerm (meet left (inner.fill contractum)) := target
          have recurse := holds_fill_iff inner rightTerm (HistTerm.meet_inv target').2 preserves
          show Holds (meet left (inner.fill redex)) ↔ Holds (meet left (inner.fill contractum))
          rw [holds_meet_iff, holds_meet_iff, recurse]
      · obtain ⟨rfl, rfl, rfl⟩ := append_cons_eq_singleton shape
        have target' : HistTerm (wait (inner.fill contractum)) := target
        have recurse := holds_fill_iff inner historyTerm (HistTerm.wait_inv target') preserves
        show Holds (wait (inner.fill redex)) ↔ Holds (wait (inner.fill contractum))
        rw [holds_wait_iff, holds_wait_iff]
        exact recurse
      · obtain ⟨rfl, rfl, rfl⟩ := append_cons_eq_singleton shape
        have target' : HistTerm (give (inner.fill contractum)) := target
        have recurse := holds_fill_iff inner historyTerm (HistTerm.give_inv target') preserves
        show Holds (give (inner.fill redex)) ↔ Holds (give (inner.fill contractum))
        rw [holds_give_iff, holds_give_iff]
        exact recurse
  | .lambda _ _, _, _, source, _, _ => by
      obtain ⟨label, arguments, shape⟩ := source.exists_apply
      simp [OneHoleContext.fill] at shape
  | .multiLambda _ _ _, _, _, source, _, _ => by
      obtain ⟨label, arguments, shape⟩ := source.exists_apply
      simp [OneHoleContext.fill] at shape
  | .substBody _ _, _, _, source, _, _ => by
      obtain ⟨label, arguments, shape⟩ := source.exists_apply
      simp [OneHoleContext.fill] at shape
  | .substReplacement _ _, _, _, source, _, _ => by
      obtain ⟨label, arguments, shape⟩ := source.exists_apply
      simp [OneHoleContext.fill] at shape
  | .collection _ _ _ _ _, _, _, source, _, _ => by
      obtain ⟨label, arguments, shape⟩ := source.exists_apply
      simp [OneHoleContext.fill] at shape

/-- The history language has no collection and no collection algebra, so its
static equivalence is generated by the authored equations alone. -/
theorem historyMachine_no_derivedInstance (source target : Pattern) :
    ¬ DerivedInstance historyMachine source target :=
  no_derivedInstance_of_no_derived_laws (by decide +kernel) (by decide +kernel)
    (by decide +kernel) source target

/-- **One equation step between history terms preserves the claim.** -/
theorem holds_iff_of_contextStep {base : BasePremiseEvaluator} {source target : Pattern}
    (sourceTerm : HistTerm source) (targetTerm : HistTerm target)
    (step : EquationContextStep base historyMachine source target) :
    Holds source ↔ Holds target := by
  cases step with
  | inContext context generator =>
      rcases generator with authored | derived
      · exact holds_fill_iff context sourceTerm targetTerm
          (equationInstance_preservesClaim authored)
      · exact absurd derived (historyMachine_no_derivedInstance _ _)

/-! ## The equations record a halting run -/

/-- The history terms, as a carrier. -/
abbrev History := { pattern : Pattern // HistTerm pattern }

/-- One equation step between history terms. -/
def historyStep (base : BasePremiseEvaluator) (left right : History) : Prop :=
  EquationContextStep base historyMachine left.1 right.1

/-- A machine step is recorded by one equation: `Now(c) = Then(c, Now(c'))`. -/
theorem historyStep_now (base : BasePremiseEvaluator) {configuration next : Pattern}
    (image : InImage configuration) (step : Reduces configuration next) :
    historyStep base ⟨now configuration, .ofNow image⟩
      ⟨andThen configuration (now next),
        .ofThen image (.ofNow (reduct_inImage image step))⟩ := by
  obtain ⟨rule, inRules, bindings, matched, applied⟩ := exists_match_of_reduces step
  have left : applyBindings bindings rule.left = configuration :=
    matchPattern_correct matched (rule_left_matchCorrect inRules)
  refine EquationContextStep.inContext .hole (Or.inl ⟨0, ?_⟩)
  exact EquationInstanceAt.forward (equation := nowLaw rule) (initialBindings := bindings)
    (finalBindings := bindings)
    (List.Mem.tail _ (List.mem_append_left _ (List.mem_map_of_mem inRules)))
    (mem_matchPattern_apply_one.mpr ⟨configuration, rfl, matched⟩)
    (PremisesAt.nil bindings)
    (by
      show applyBindings bindings (andThen rule.left (now rule.right)) = _
      rw [applyBindings_andThen, applyBindings_now, left, applied])

/-- A finished run is carried back one machine step:
`Flag(c) = Then(c, Flag(c'))`. -/
theorem historyStep_flag (base : BasePremiseEvaluator) {configuration next : Pattern}
    (image : InImage configuration) (step : Reduces configuration next) :
    historyStep base ⟨flag configuration, .ofFlag image⟩
      ⟨andThen configuration (flag next),
        .ofThen image (.ofFlag (reduct_inImage image step))⟩ := by
  obtain ⟨rule, inRules, bindings, matched, applied⟩ := exists_match_of_reduces step
  have left : applyBindings bindings rule.left = configuration :=
    matchPattern_correct matched (rule_left_matchCorrect inRules)
  refine EquationContextStep.inContext .hole (Or.inl ⟨0, ?_⟩)
  exact EquationInstanceAt.reverse (equation := flagLaw rule) (initialBindings := bindings)
    (finalBindings := bindings)
    (List.Mem.tail _ (List.mem_append_right _ (List.mem_map_of_mem inRules)))
    (mem_matchPattern_apply_one.mpr ⟨configuration, rfl, matched⟩)
    (PremisesAt.nil bindings)
    (by
      show applyBindings bindings (andThen rule.left (flag rule.right)) = _
      rw [applyBindings_andThen, applyBindings_flag, left, applied])

/-- A halted configuration is finished: `Now(Halt(w)) = Flag(Halt(w))`. -/
theorem historyStep_halted (base : BasePremiseEvaluator) (output : List ℕ) :
    historyStep base
      ⟨now (encCfg (.halt output)), .ofNow (.inr ⟨.halt output, rfl⟩)⟩
      ⟨flag (encCfg (.halt output)), .ofFlag (.inr ⟨.halt output, rfl⟩)⟩ := by
  refine EquationContextStep.inContext .hole (Or.inl ⟨0, ?_⟩)
  exact EquationInstanceAt.forward (equation := haltLaw)
    (initialBindings := [("w", encNats output)]) (finalBindings := [("w", encNats output)])
    (List.Mem.head _)
    (mem_matchPattern_apply_one.mpr ⟨_, rfl,
      mem_matchPattern_apply_one.mpr ⟨_, rfl, matchRel_complete MatchRel.fvar⟩⟩)
    (PremisesAt.nil _)
    (by simp [haltLaw, flag, encCfg, applyBindings])

/-- The equivalence of history terms is closed under prefixing by a
configuration. -/
theorem eqvGen_andThen (base : BasePremiseEvaluator) {configuration : Pattern}
    (image : InImage configuration) {left right : History}
    (equivalent : Relation.EqvGen (historyStep base) left right) :
    Relation.EqvGen (historyStep base)
      ⟨andThen configuration left.1, .ofThen image left.2⟩
      ⟨andThen configuration right.1, .ofThen image right.2⟩ := by
  induction equivalent with
  | rel left right step =>
      exact Relation.EqvGen.rel _ _
        (equationContextStep_fill (.apply "Then" [configuration] .hole []) step)
  | refl history => exact Relation.EqvGen.refl _
  | symm left right _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans left middle right _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- **A halting run is recorded by the equations.**  From an encoded
configuration that halts, `Now` and `Flag` are equal through history terms
alone. -/
theorem now_equivalent_flag_of_halts (base : BasePremiseEvaluator) {configuration : Pattern}
    (image : InImage configuration) (halts : Halts configuration) :
    Relation.EqvGen (historyStep base)
      ⟨now configuration, .ofNow image⟩ ⟨flag configuration, .ofFlag image⟩ := by
  obtain ⟨output, path⟩ := halts
  revert image
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro image
      exact Relation.EqvGen.rel _ _ (historyStep_halted base output)
  | head step _ recurse =>
      intro image
      have next := reduct_inImage image step
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.rel _ _ (historyStep_now base image step))
        (Relation.EqvGen.trans _ _ _ (eqvGen_andThen base image (recurse next))
          (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ (historyStep_flag base image step))))

/-! ## The interacting fibre -/

/-- A history term as a member of the interacting fibre. -/
def History.toTerm (history : History) : historyPresentation.Term :=
  ⟨history.1, history.2.closed⟩

/-- An equivalence through history terms is an equivalence in the fibre. -/
theorem presented_of_historyEquivalent {left right : History}
    (equivalent : Relation.EqvGen (historyStep defaultBasePremises) left right) :
    (presentedEquationSetoid defaultBasePremises historyPresentation).r
      left.toTerm right.toTerm := by
  induction equivalent with
  | rel left right step => exact Relation.EqvGen.rel _ _ step
  | refl history => exact Relation.EqvGen.refl _
  | symm left right _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans left middle right _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- **Equal members of the fibre make claims of equal truth.** -/
theorem holds_iff_of_presented {left right : historyPresentation.Term}
    (equivalent :
      (presentedEquationSetoid defaultBasePremises historyPresentation).r left right) :
    Holds left.1 ↔ Holds right.1 := by
  induction equivalent with
  | rel left right step =>
      exact holds_iff_of_contextStep (histTerm_of_closed left.2) (histTerm_of_closed right.2)
        step
  | refl term => exact Iff.rfl
  | symm left right _ recurse => exact recurse.symm
  | trans left middle right _ _ first second => exact first.trans second

/-- `Now(c)` as a member of the fibre. -/
def nowTerm (configuration : Pattern) (image : InImage configuration) :
    historyPresentation.Term :=
  History.toTerm ⟨now configuration, .ofNow image⟩

/-- `Flag(c)` as a member of the fibre. -/
def flagTerm (configuration : Pattern) (image : InImage configuration) :
    historyPresentation.Term :=
  History.toTerm ⟨flag configuration, .ofFlag image⟩

/-- **The static equivalence of the history theory is halting.**  For an
encoded configuration, `Now` and `Flag` are equal in the interacting fibre
exactly when the configuration reduces to a halted one. -/
theorem now_equivalent_flag_iff {configuration : Pattern} (image : InImage configuration) :
    historyTheory.toGSLT.equations.r (nowTerm configuration image)
        (flagTerm configuration image) ↔
      Halts configuration := by
  constructor
  · intro equivalent
    exact holds_now_iff.mp ((holds_iff_of_presented equivalent).mpr (Holds.ofFlag _))
  · intro halts
    exact presented_of_historyEquivalent
      (now_equivalent_flag_of_halts defaultBasePremises image halts)

/-- A configuration that never halts separates `Now` from `Flag`: the two
histories are different members of the quotient. -/
theorem now_not_equivalent_flag_of_diverges {configuration : Pattern}
    (image : InImage configuration) (diverges : ¬ Halts configuration) :
    ¬ historyTheory.toGSLT.equations.r (nowTerm configuration image)
      (flagTerm configuration image) :=
  fun equivalent => diverges ((now_equivalent_flag_iff image).mp equivalent)

end Mettapedia.Languages.PartrecMachine
