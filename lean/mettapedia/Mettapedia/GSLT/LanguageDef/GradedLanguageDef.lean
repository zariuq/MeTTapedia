import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Core.WeightedMuScheduler

/-!
# Graded languages, built from the generic constructors

A five-field `LanguageDef` says which terms and steps *exist*.  This module
attaches an authored weight table and produces its semantics **by applying
the generic GSLT constructors to the base language's own GSLT** — nothing
here is a parallel hand-built system:

```
languageGSLT base laws            the five-field denotation
      │  GSLT.spendLift           (enrichment: carrier Pattern × V)
      ▼
toFreeGSLT / toInertGSLT          the graded language, one per policy
      │  GSLT.restrict             (policy: prune to maximal grades)
      ▼
toFreeResolvedGSLT                the explicitly free-policy resolver
```

Each arrow owes exactly the comparison theorem its constructor owes:
erasure for the lift (`toFreeGSLT_erase_step`, and reflection under the
grading's totality), simulation only for the restriction
(`freeResolvedStep_simulation`, strict by
`freeResolvedStep_prunes_dominated`).

**No silent defaults.**  The primitive is the *partial* grade table
`ruleGrade?`; a rule the table does not mention has **no** grade.  Three
named policies interpret partiality, each with its own theorem:

* **free** (`freeRuleGrade`, `toFreeGSLT`): unmentioned rules weigh the unit.
  A deliberate commitment — stated, not assumed — under which the empty
  table is exactly the plain language (`toFreeGSLT_step_of_no_weights`);
* **inert** (`toInertGSLT`): an ungraded rule contributes no step at all —
  no grade, no authority (`toInertGSLT_not_step_of_ungraded`).  Erasure
  still preserves; it reflects only what is covered;
* **gated** (`Covers`, `toInertGSLT_lift_step`): totality is an explicit
  admission obligation — the table must cover the rewrite list — and the
  full erasure theorem is earned by discharging it.

The inert language embeds in the free one with agreeing grades
(`toInertGSLT_step_le_toFreeGSLT`), so the policies form a ladder rather than
three unrelated semantics.

The authored syntax is `WeightedRuleDecl` rows through the compositional
layer machinery (`gradedLayer`, `toExtended`), exactly as the proof
calculus enters through `calculusLayer`.  A concrete spelling for weighted
rules is deliberately not ratified here; this module is the semantic
parent any such syntax must elaborate into.  The framing of grades as the
value dial of an observation discipline follows Meredith's *Observation
Disciplines*, read against this project's five-field core.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.Core.WeightedMuScheduler

/-! ## Authored weight rows and their compositional layer -/

/-- One authored weight row: a grade attached to a named rewrite rule.
This is the payload any weighted-rule syntax elaborates into. -/
structure WeightedRuleDecl (V : Type) where
  rule : String
  grade : V

/-- Weight rows are their own exact declaration syntax. -/
def weightedRuleCodec (V : Type) :
    ExactDeclarationCodec (WeightedRuleDecl V) (WeightedRuleDecl V) where
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

/-- The graded compositional layer over the five-field base: its fiber is
the authored weight table, with concatenation laws supplied by the generic
declaration machinery. -/
def gradedLayer (V : Type) : CompositionalLayer.{0, 0} LanguageDef :=
  .ofCodec LanguageDef (weightedRuleCodec V)

@[simp] theorem gradedLayer_fiber (V : Type) (language : LanguageDef) :
    (gradedLayer V).Fiber language = List (WeightedRuleDecl V) := rfl

/-! ## The graded language -/

/-- A five-field language together with an authored, deliberately
*partial* weight table. -/
structure GradedLanguageDef (V : Type) extends LanguageDef where
  weights : List (WeightedRuleDecl V) := []

namespace GradedLanguageDef

variable {V : Type} (graded : GradedLanguageDef V)

/-- The flat record is the graded specialization of the general
layer-indexed definition, exactly as the calculus record specializes the
calculus layer. -/
def toExtended : ExtendedLanguageDef (gradedLayer V) where
  toLanguageDef := graded.toLanguageDef
  extension := graded.weights

/-- **The primitive**: the partial grade of a rule — the first table row
naming it, if any.  No default is applied here. -/
def ruleGrade? (rule : RewriteRule) : Option V :=
  (graded.weights.find? fun row => row.rule == rule.name).map
    WeightedRuleDecl.grade

/-- A rule the table does not mention has no grade. -/
theorem ruleGrade?_eq_none_of_not_mentioned {rule : RewriteRule}
    (absent : ∀ row ∈ graded.weights, row.rule ≠ rule.name) :
    graded.ruleGrade? rule = none := by
  unfold ruleGrade?
  rw [List.find?_eq_none.mpr]
  · rfl
  · intro row membership
    simp [absent row membership]

/-- The *free* policy: unmentioned rules weigh the unit.  This is a named
commitment, not a silent default; use `toInertGSLT` to refuse it. -/
def freeRuleGrade [One V] (rule : RewriteRule) : V :=
  (graded.ruleGrade? rule).getD 1

theorem freeRuleGrade_of_not_mentioned [One V] {rule : RewriteRule}
    (absent : ∀ row ∈ graded.weights, row.rule ≠ rule.name) :
    graded.freeRuleGrade rule = 1 := by
  unfold freeRuleGrade
  rw [graded.ruleGrade?_eq_none_of_not_mentioned absent]
  rfl

theorem freeRuleGrade_of_no_weights [One V] (empty : graded.weights = [])
    (rule : RewriteRule) : graded.freeRuleGrade rule = 1 := by
  apply graded.freeRuleGrade_of_not_mentioned
  rw [empty]
  intro row membership
  cases membership

/-- The *gated* policy's obligation: the table covers the rewrite list. -/
def Covers : Prop :=
  ∀ rule ∈ graded.toLanguageDef.rewrites, (graded.ruleGrade? rule).isSome

/-- Plumbing to the scheduler's clause language: the free grade table is a
one-state graded clause, evaluated per candidate rule with no temporal
memory. -/
theorem freeRuleGrade_oneStateGrade [CommSemiring V] :
    WeighClause.oneStateGrade (.observe graded.freeRuleGrade) =
      graded.freeRuleGrade := rfl

end GradedLanguageDef

/-! ## Rule provenance for the authored step relation -/

/-- One authored contextual step together with the root rule that fired.
`StepAt` has exactly one constructor, so this is its inversion image with
the rule exposed for grading. -/
def RootRuleStep (base : BasePremiseEvaluator) (language : LanguageDef)
    (rule : RewriteRule) (source target : Pattern) : Prop :=
  ∃ (fuel : Nat) (initialBindings finalBindings : Bindings),
    rule ∈ language.rewrites ∧
    initialBindings ∈ matchPatternForRule language rule source ∧
    PremisesAt base language fuel initialBindings rule.premises
      finalBindings ∧
    applyBindingsForRule language rule finalBindings = target

/-- Every root-rule step names a listed rewrite rule. -/
theorem RootRuleStep.rule_mem {base : BasePremiseEvaluator}
    {language : LanguageDef} {rule : RewriteRule} {source target : Pattern}
    (root : RootRuleStep base language rule source target) :
    rule ∈ language.rewrites := by
  obtain ⟨_, _, _, membership, _⟩ := root
  exact membership

/-- The authored step relation is exactly the rule-indexed relation with
the rule existentially closed. -/
theorem step_iff_exists_rootRuleStep (base : BasePremiseEvaluator)
    (language : LanguageDef) (source target : Pattern) :
    Step base language source target ↔
      ∃ rule, RootRuleStep base language rule source target := by
  constructor
  · rintro ⟨fuel, stepAt⟩
    cases stepAt with
    | @rule fuelAt sourceAt targetAt ruleAt initialBindings finalBindings
        membership matched premises applied =>
        exact ⟨ruleAt, fuelAt, initialBindings, finalBindings, membership,
          matched, premises, applied⟩
  · rintro ⟨rule, fuel, initialBindings, finalBindings, membership, matched,
      premises, applied⟩
    exact ⟨fuel + 1, .rule membership matched premises applied⟩

/-! ## Rule-stable equation respect

A weighted language is well-defined on equivalence classes only when the
equations preserve each rule's applicability individually: the grade is a
function of the rule, so `∃ some rule fires` is no longer enough. -/

/-- Equation compatibility, per rule.  Strictly stronger than
`ReductionRespectsEquationsUsing`, and exactly what grading forces. -/
structure GradedReductionRespectsEquationsUsing
    (relations : RelationEnv) (language : LanguageDef) : Prop where
  source : ∀ (rule : RewriteRule) {term term' result},
    EquationEquiv (engineBasePremises relations) language term term' →
    RootRuleStep (engineBasePremises relations) language rule term result →
    ∃ result',
      RootRuleStep (engineBasePremises relations) language rule term'
        result' ∧
      EquationEquiv (engineBasePremises relations) language result result'
  target : ∀ (rule : RewriteRule) {term result result'},
    RootRuleStep (engineBasePremises relations) language rule term result →
    EquationEquiv (engineBasePremises relations) language result result' →
    RootRuleStep (engineBasePremises relations) language rule term result'

namespace GradedReductionRespectsEquationsUsing

/-- Rule-stable respect forgets to plain respect. -/
def toBase {relations : RelationEnv} {language : LanguageDef}
    (laws : GradedReductionRespectsEquationsUsing relations language) :
    ReductionRespectsEquationsUsing relations language where
  source := by
    intro term term' result equivalent reduction
    obtain ⟨rule, root⟩ :=
      (step_iff_exists_rootRuleStep _ language term result).mp reduction
    obtain ⟨result', root', resultEq⟩ := laws.source rule equivalent root
    exact ⟨result',
      (step_iff_exists_rootRuleStep _ language term' result').mpr
        ⟨rule, root'⟩,
      resultEq⟩
  target := by
    intro term result result' reduction equivalent
    obtain ⟨rule, root⟩ :=
      (step_iff_exists_rootRuleStep _ language term result).mp reduction
    exact (step_iff_exists_rootRuleStep _ language term result').mpr
      ⟨rule, laws.target rule root equivalent⟩

/-- For an equation-free presentation the generated equivalence is syntactic
equality, so rule-stable respect is free. -/
def of_equation_free (relations : RelationEnv) {language : LanguageDef}
    (free : language.isEquationFree = true) :
    GradedReductionRespectsEquationsUsing relations language where
  source := by
    intro rule term term' result equivalent root
    have equal :=
      (equationEquiv_iff_eq_of_no_generators free term term').mp equivalent
    subst term'
    exact ⟨result, root, Relation.EqvGen.refl result⟩
  target := by
    intro rule term result result' root equivalent
    have equal :=
      (equationEquiv_iff_eq_of_no_generators free result result').mp
        equivalent
    subst result'
    exact root

end GradedReductionRespectsEquationsUsing

/-- The closed-world specialization with no external relation rows. -/
abbrev GradedReductionRespectsEquations (language : LanguageDef) :=
  GradedReductionRespectsEquationsUsing RelationEnv.empty language

namespace GradedReductionRespectsEquations

def of_equation_free {language : LanguageDef}
    (free : language.isEquationFree = true) :
    GradedReductionRespectsEquations language :=
  GradedReductionRespectsEquationsUsing.of_equation_free RelationEnv.empty
    free

end GradedReductionRespectsEquations

/-! ## From table to grading: the two policy gradings -/

namespace GradedLanguageDef

variable {V : Type} (graded : GradedLanguageDef V)
variable (laws : GradedReductionRespectsEquations graded.toLanguageDef)

/-- The base language's own GSLT — the object everything below is
constructed from. -/
def baseGSLT : GSLT := languageGSLT graded.toLanguageDef laws.toBase

@[simp] theorem baseGSLT_step_iff (source target : Pattern) :
    (graded.baseGSLT laws).Step source target ↔
      langReducesUsing RelationEnv.empty graded.toLanguageDef source target :=
  languageGSLT_step graded.toLanguageDef laws.toBase source target

/-- The *inert* grading: a step is graded only through a rule the table
mentions, at exactly the authored grade.  Deliberately partial. -/
def inertSpend : GSLT.StepSpend (graded.baseGSLT laws) V where
  graded := fun source target grade =>
    ∃ rule,
      RootRuleStep (engineBasePremises RelationEnv.empty)
        graded.toLanguageDef rule source target ∧
      graded.ruleGrade? rule = some grade
  sound := by
    rintro source target grade ⟨rule, root, _⟩
    apply (graded.baseGSLT_step_iff laws source target).2
    exact (step_iff_exists_rootRuleStep _ _ _ _).mpr ⟨rule, root⟩
  resp_left := by
    rintro source source' target grade equivalent ⟨rule, root, gradeEq⟩
    obtain ⟨target', root', targetEq⟩ := laws.source rule equivalent root
    exact ⟨target', ⟨rule, root', gradeEq⟩, targetEq⟩
  resp_right := by
    rintro source target target' grade ⟨rule, root, gradeEq⟩ equivalent
    exact ⟨rule, laws.target rule root equivalent, gradeEq⟩

/-- The *free* grading: every firing rule is graded, unmentioned rules at
the unit.  Total by construction. -/
def freeSpend [One V] : GSLT.StepSpend (graded.baseGSLT laws) V where
  graded := fun source target grade =>
    ∃ rule,
      RootRuleStep (engineBasePremises RelationEnv.empty)
        graded.toLanguageDef rule source target ∧
      grade = graded.freeRuleGrade rule
  sound := by
    rintro source target grade ⟨rule, root, _⟩
    apply (graded.baseGSLT_step_iff laws source target).2
    exact (step_iff_exists_rootRuleStep _ _ _ _).mpr ⟨rule, root⟩
  resp_left := by
    rintro source source' target grade equivalent ⟨rule, root, gradeEq⟩
    obtain ⟨target', root', targetEq⟩ := laws.source rule equivalent root
    exact ⟨target', ⟨rule, root', gradeEq⟩, targetEq⟩
  resp_right := by
    rintro source target target' grade ⟨rule, root, gradeEq⟩ equivalent
    exact ⟨rule, laws.target rule root equivalent, gradeEq⟩

theorem freeGrading_total [One V] : (graded.freeSpend laws).Total := by
  intro source target step
  have authored := (graded.baseGSLT_step_iff laws source target).1 step
  obtain ⟨rule, root⟩ :=
    (step_iff_exists_rootRuleStep _ _ _ _).mp authored
  exact ⟨graded.freeRuleGrade rule, rule, root, rfl⟩

/-- Coverage discharges totality for the inert grading: the gated policy. -/
theorem inertGrading_total_of_covers (covers : graded.Covers) :
    (graded.inertSpend laws).Total := by
  intro source target step
  have authored := (graded.baseGSLT_step_iff laws source target).1 step
  obtain ⟨rule, root⟩ :=
    (step_iff_exists_rootRuleStep _ _ _ _).mp authored
  obtain ⟨grade, gradeEq⟩ :=
    Option.isSome_iff_exists.mp (covers rule root.rule_mem)
  exact ⟨grade, rule, root, gradeEq⟩

/-! ## The graded GSLTs: generic lift, per policy -/

/-- The free-policy graded language: the generic graded lift of the base
language's GSLT along the free grading. -/
def toFreeGSLT [Monoid V] : GSLT :=
  (graded.baseGSLT laws).spendLift (graded.freeSpend laws)

/-- The inert-policy graded language: the same generic lift along the
partial grading. -/
def toInertGSLT [Monoid V] : GSLT :=
  (graded.baseGSLT laws).spendLift (graded.inertSpend laws)

section Policies

variable [Monoid V]

@[simp] theorem toFreeGSLT_Term :
    (graded.toFreeGSLT laws).Term = (Pattern × V) :=
  rfl

theorem toFreeGSLT_step_iff {source target : Pattern × V} :
    (graded.toFreeGSLT laws).Step source target ↔
      ∃ rule,
        RootRuleStep (engineBasePremises RelationEnv.empty)
          graded.toLanguageDef rule source.1 target.1 ∧
        target.2 = source.2 * graded.freeRuleGrade rule := by
  constructor
  · rintro ⟨grade, ⟨rule, root, gradeEq⟩, accumulated⟩
    exact ⟨rule, root, gradeEq ▸ accumulated⟩
  · rintro ⟨rule, root, accumulated⟩
    exact ⟨graded.freeRuleGrade rule, ⟨rule, root, rfl⟩, accumulated⟩

theorem toInertGSLT_step_iff {source target : Pattern × V} :
    (graded.toInertGSLT laws).Step source target ↔
      ∃ rule,
        RootRuleStep (engineBasePremises RelationEnv.empty)
          graded.toLanguageDef rule source.1 target.1 ∧
        graded.ruleGrade? rule = some (graded.freeRuleGrade rule) ∧
        target.2 = source.2 * graded.freeRuleGrade rule := by
  constructor
  · rintro ⟨grade, ⟨rule, root, gradeEq⟩, accumulated⟩
    have free : graded.freeRuleGrade rule = grade := by
      unfold freeRuleGrade
      rw [gradeEq]
      rfl
    exact ⟨rule, root, free ▸ gradeEq, free ▸ accumulated⟩
  · rintro ⟨rule, root, gradeEq, accumulated⟩
    exact ⟨graded.freeRuleGrade rule, ⟨rule, root, gradeEq⟩, accumulated⟩

/-! ### Erasure, per policy -/

/-- Erasure preserves: both policies project onto authored base steps. -/
theorem toFreeGSLT_erase_step {source target : Pattern × V}
    (step : (graded.toFreeGSLT laws).Step source target) :
    langReducesUsing RelationEnv.empty graded.toLanguageDef source.1
      target.1 :=
  (graded.baseGSLT_step_iff laws source.1 target.1).1
    (GSLT.spendLift_erase_step _ step)

theorem toInertGSLT_erase_step {source target : Pattern × V}
    (step : (graded.toInertGSLT laws).Step source target) :
    langReducesUsing RelationEnv.empty graded.toLanguageDef source.1
      target.1 :=
  (graded.baseGSLT_step_iff laws source.1 target.1).1
    (GSLT.spendLift_erase_step _ step)

/-- Erasure reflects for the free policy, unconditionally. -/
theorem toFreeGSLT_lift_step {source target : Pattern}
    (step : langReducesUsing RelationEnv.empty graded.toLanguageDef source
      target) (accumulator : V) :
    ∃ value,
      (graded.toFreeGSLT laws).Step (source, accumulator) (target, value) :=
  GSLT.spendLift_lift_step _ (graded.freeGrading_total laws)
    ((graded.baseGSLT_step_iff laws source target).2 step)
    accumulator

/-- Erasure reflects for the inert policy exactly under coverage: the
gated erasure theorem. -/
theorem toInertGSLT_lift_step (covers : graded.Covers)
    {source target : Pattern}
    (step : langReducesUsing RelationEnv.empty graded.toLanguageDef source
      target) (accumulator : V) :
    ∃ value,
      (graded.toInertGSLT laws).Step (source, accumulator)
        (target, value) :=
  GSLT.spendLift_lift_step _
    (graded.inertGrading_total_of_covers laws covers)
    ((graded.baseGSLT_step_iff laws source target).2 step) accumulator

/-- An ungraded firing has no inert step: no grade, no authority. -/
theorem toInertGSLT_not_step_of_ungraded {source target : Pattern}
    (ungraded : ∀ rule,
      RootRuleStep (engineBasePremises RelationEnv.empty)
        graded.toLanguageDef rule source target →
      graded.ruleGrade? rule = none)
    (accumulator value : V) :
    ¬ (graded.toInertGSLT laws).Step (source, accumulator)
      (target, value) := by
  rintro ⟨grade, ⟨rule, root, gradeEq⟩, _⟩
  rw [ungraded rule root] at gradeEq
  cases gradeEq

/-- The policy ladder: every inert step is a free step, grade and all. -/
theorem toInertGSLT_step_le_toFreeGSLT {source target : Pattern × V}
    (step : (graded.toInertGSLT laws).Step source target) :
    (graded.toFreeGSLT laws).Step source target := by
  obtain ⟨grade, ⟨rule, root, gradeEq⟩, accumulated⟩ := step
  refine ⟨grade, ⟨rule, root, ?_⟩, accumulated⟩
  unfold freeRuleGrade
  rw [gradeEq]
  rfl

/-! ### The free-policy laws -/

/-- The empty table degenerates to the plain language, step for step. -/
theorem toFreeGSLT_step_of_no_weights (empty : graded.weights = [])
    {source target : Pattern} {before after : V} :
    (graded.toFreeGSLT laws).Step (source, before) (target, after) ↔
      langReducesUsing RelationEnv.empty graded.toLanguageDef source
          target ∧
        after = before := by
  rw [graded.toFreeGSLT_step_iff laws]
  constructor
  · rintro ⟨rule, root, accumulated⟩
    dsimp only at accumulated
    refine ⟨(step_iff_exists_rootRuleStep _ _ _ _).mpr ⟨rule, root⟩, ?_⟩
    rw [accumulated, graded.freeRuleGrade_of_no_weights empty rule, mul_one]
  · rintro ⟨step, rfl⟩
    obtain ⟨rule, root⟩ := (step_iff_exists_rootRuleStep _ _ _ _).mp step
    refine ⟨rule, root, ?_⟩
    dsimp only
    rw [graded.freeRuleGrade_of_no_weights empty rule, mul_one]

/-- Grades act by left translation. -/
theorem toFreeGSLT_step_action {source target : Pattern} {before after : V} :
    (graded.toFreeGSLT laws).Step (source, before) (target, after) ↔
      ∃ weight,
        (graded.toFreeGSLT laws).Step (source, 1) (target, weight) ∧
        after = before * weight :=
  GSLT.spendLift_step_action _

/-- Every graded run factors through its accumulated weight. -/
theorem toFreeGSLT_multiStep_factors {source target : Pattern × V}
    (path : (graded.toFreeGSLT laws).MultiStep source target) :
    ∃ weight, target.2 = source.2 * weight :=
  GSLT.spendLift_multiStep_factors _ path

end Policies

/-! ## The resolver: spend and choose, two independent algebras

The lift **spends** in `V`; the filter **chooses** by a preference
algebra `P` that need not be `V`.  Choosing by the very grade the lift
spends — the historical single-algebra resolver — is the *diagonal*
instance `freeMaximalFilter`, a named commitment rather than a silent
identification of the two axes.  `GSLT.spendLift_restrict_comm` and
`GSLT.budget_filter_not_base_expressible` are the generic separation
theorems this design answers to. -/

section Resolver

variable [Monoid V]

variable {P : Type} [PartialOrder P]

/-- The two-algebra resolver filter: keep a spend-lifted step exactly
when its firing rule is `prefer`-maximal among all rules applicable at
the source.  The preference algebra is independent of the spend. -/
def preferenceMaximalFilter (prefer : RewriteRule → P) :
    GSLT.StepFilter (graded.toFreeGSLT laws) where
  keep := fun source target =>
    ∃ rule,
      RootRuleStep (engineBasePremises RelationEnv.empty)
        graded.toLanguageDef rule source.1 target.1 ∧
      target.2 = source.2 * graded.freeRuleGrade rule ∧
      ∀ (competitor : RewriteRule) (other : Pattern),
        RootRuleStep (engineBasePremises RelationEnv.empty)
          graded.toLanguageDef competitor source.1 other →
        prefer competitor ≤ prefer rule
  keep_sound := by
    rintro source target ⟨rule, root, accumulated, _⟩
    exact (graded.toFreeGSLT_step_iff laws).mpr ⟨rule, root, accumulated⟩
  resp_left := by
    rintro source source' target ⟨stateEq, accumulatorEq⟩
      ⟨rule, root, accumulated, maximal⟩
    obtain ⟨result', root', resultEq⟩ := laws.source rule stateEq root
    refine ⟨(result', source'.2 * graded.freeRuleGrade rule),
      ⟨rule, root', rfl, ?_⟩, resultEq, ?_⟩
    · intro competitor other rootCompetitor
      obtain ⟨otherBack, rootBack, _⟩ := laws.source competitor
        (Relation.EqvGen.symm _ _ stateEq) rootCompetitor
      exact maximal competitor otherBack rootBack
    · rw [accumulated, accumulatorEq]
  resp_right := by
    rintro source target target' ⟨rule, root, accumulated, maximal⟩
      ⟨stateEq, accumulatorEq⟩
    exact ⟨rule, laws.target rule root stateEq,
      accumulatorEq ▸ accumulated, maximal⟩

/-- The resolved language over an independent preference algebra. -/
def toPreferenceResolvedGSLT (prefer : RewriteRule → P) : GSLT :=
  (graded.toFreeGSLT laws).restrict
    (graded.preferenceMaximalFilter laws prefer)

/-- Simulation for the two-algebra resolver. -/
theorem preferenceResolvedStep_simulation (prefer : RewriteRule → P)
    {source target : Pattern × V}
    (resolved :
      (graded.toPreferenceResolvedGSLT laws prefer).Step source target) :
    (graded.toFreeGSLT laws).Step source target :=
  GSLT.restrict_simulation _ resolved

variable [PartialOrder V]

/-- **The diagonal**: choose by the very grade the lift spends.  This is
the historical single-algebra resolver, now an explicit instance. -/
def freeMaximalFilter : GSLT.StepFilter (graded.toFreeGSLT laws) :=
  graded.preferenceMaximalFilter laws graded.freeRuleGrade

/-- The resolved language: the generic restriction of the free-policy
lift along the diagonal maximal-grade filter. -/
def toFreeResolvedGSLT : GSLT :=
  (graded.toFreeGSLT laws).restrict (graded.freeMaximalFilter laws)

/-- Simulation — the only comparison theorem the resolver rung can owe. -/
theorem freeResolvedStep_simulation {source target : Pattern × V}
    (resolved : (graded.toFreeResolvedGSLT laws).Step source target) :
    (graded.toFreeGSLT laws).Step source target :=
  GSLT.restrict_simulation _ resolved

/-- Resolved steps erase to authored base steps. -/
theorem freeResolvedStep_erase {source target : Pattern × V}
    (resolved : (graded.toFreeResolvedGSLT laws).Step source target) :
    langReducesUsing RelationEnv.empty graded.toLanguageDef source.1
      target.1 :=
  graded.toFreeGSLT_erase_step laws
    (graded.freeResolvedStep_simulation laws resolved)

/-- **Pruning.**  If some applicable rule strictly outweighs every rule
reaching a given target, the graded step to that target exists and no
resolved step reaches it: the simulation is strict. -/
theorem freeResolvedStep_prunes_dominated
    {source lowTarget highTarget : Pattern} {lowRule highRule : RewriteRule}
    (lowRoot : RootRuleStep (engineBasePremises RelationEnv.empty)
      graded.toLanguageDef lowRule source lowTarget)
    (highRoot : RootRuleStep (engineBasePremises RelationEnv.empty)
      graded.toLanguageDef highRule source highTarget)
    (dominated : ∀ rule,
      RootRuleStep (engineBasePremises RelationEnv.empty)
        graded.toLanguageDef rule source lowTarget →
      graded.freeRuleGrade rule ≤ graded.freeRuleGrade lowRule)
    (outweighed :
      graded.freeRuleGrade lowRule < graded.freeRuleGrade highRule)
    (accumulator : V) :
    (graded.toFreeGSLT laws).Step (source, accumulator)
        (lowTarget, accumulator * graded.freeRuleGrade lowRule) ∧
      ∀ value, ¬ (graded.toFreeResolvedGSLT laws).Step (source, accumulator)
        (lowTarget, value) := by
  refine ⟨(graded.toFreeGSLT_step_iff laws).mpr ⟨lowRule, lowRoot, rfl⟩, ?_⟩
  rintro value ⟨rule, root, _, maximal⟩
  have ruleLow : graded.freeRuleGrade rule ≤ graded.freeRuleGrade lowRule :=
    dominated rule root
  have highLow :
      graded.freeRuleGrade highRule ≤ graded.freeRuleGrade rule :=
    maximal highRule highTarget highRoot
  exact lt_irrefl _ (lt_of_lt_of_le outweighed (highLow.trans ruleLow))

end Resolver

/-! ## The inert resolver: absence is not silently interpreted -/

section InertResolver

variable [Monoid V] [PartialOrder V]

/-- The maximal-grade filter over the inert language.  Only rules with an
authored grade participate, so an absent grade grants neither a step nor a
vote in resolution. -/
def inertMaximalFilter : GSLT.StepFilter (graded.toInertGSLT laws) where
  keep := fun source target =>
    ∃ (rule : RewriteRule) (grade : V),
      RootRuleStep (engineBasePremises RelationEnv.empty)
        graded.toLanguageDef rule source.1 target.1 ∧
      graded.ruleGrade? rule = some grade ∧
      target.2 = source.2 * grade ∧
      ∀ (competitor : RewriteRule) (other : Pattern) (competitorGrade : V),
        RootRuleStep (engineBasePremises RelationEnv.empty)
          graded.toLanguageDef competitor source.1 other →
        graded.ruleGrade? competitor = some competitorGrade →
        competitorGrade ≤ grade
  keep_sound := by
    rintro source target ⟨rule, grade, root, gradeEq, accumulated, _⟩
    exact ⟨grade, ⟨rule, root, gradeEq⟩, accumulated⟩
  resp_left := by
    rintro source source' target ⟨stateEq, accumulatorEq⟩
      ⟨rule, grade, root, gradeEq, accumulated, maximal⟩
    obtain ⟨result', root', resultEq⟩ := laws.source rule stateEq root
    refine ⟨(result', source'.2 * grade),
      ⟨rule, grade, root', gradeEq, rfl, ?_⟩, resultEq, ?_⟩
    · intro competitor other competitorGrade rootCompetitor competitorGradeEq
      obtain ⟨otherBack, rootBack, _⟩ := laws.source competitor
        (Relation.EqvGen.symm _ _ stateEq) rootCompetitor
      exact maximal competitor otherBack competitorGrade rootBack
        competitorGradeEq
    · rw [accumulated, accumulatorEq]
  resp_right := by
    rintro source target target'
      ⟨rule, grade, root, gradeEq, accumulated, maximal⟩
      ⟨stateEq, accumulatorEq⟩
    exact ⟨rule, grade, laws.target rule root stateEq, gradeEq,
      accumulatorEq ▸ accumulated, maximal⟩

/-- Resolution over the inert policy: the generic restriction of the inert
lift, with no unit default anywhere in its definition. -/
def toInertResolvedGSLT : GSLT :=
  (graded.toInertGSLT laws).restrict (graded.inertMaximalFilter laws)

/-- Every inert resolved step is an inert graded step. -/
theorem inertResolvedStep_simulation {source target : Pattern × V}
    (resolved : (graded.toInertResolvedGSLT laws).Step source target) :
    (graded.toInertGSLT laws).Step source target :=
  GSLT.restrict_simulation _ resolved

/-- Every inert resolved step erases to an authored base step. -/
theorem inertResolvedStep_erase {source target : Pattern × V}
    (resolved : (graded.toInertResolvedGSLT laws).Step source target) :
    langReducesUsing RelationEnv.empty graded.toLanguageDef source.1
      target.1 :=
  graded.toInertGSLT_erase_step laws
    (graded.inertResolvedStep_simulation laws resolved)

end InertResolver

end GradedLanguageDef

/-! ## Validated graded languages

The raw declaration record is useful while a language is being assembled.
Semantic consumers should receive one of the bundles below so equation
compatibility and, for production gating, grade coverage cannot be forgotten
at a call site. -/

namespace GradedLanguageDef

/-- A graded declaration together with the rule-stable equation law required
by every graded denotation. -/
structure Lawful (V : Type) where
  definition : GradedLanguageDef V
  respectsEquations :
    GradedReductionRespectsEquations definition.toLanguageDef

/-- A lawful declaration whose partial table covers every authored rewrite.
This is the production bundle for the inert interpretation: absence remains
absence in the raw declaration, while coverage proves that no executable rule
is accidentally omitted. -/
structure Covered (V : Type) extends Lawful V where
  coverage : definition.Covers

namespace Lawful

variable {V : Type} (lawful : Lawful V)

/-- The partial/inert denotation of a lawful graded declaration. -/
def toInertGSLT [Monoid V] : GSLT :=
  lawful.definition.toInertGSLT lawful.respectsEquations

/-- The explicitly unit-completed denotation remains available as a named
policy, but is not the production default. -/
def toFreeGSLT [Monoid V] : GSLT :=
  lawful.definition.toFreeGSLT lawful.respectsEquations

end Lawful

namespace Covered

variable {V : Type} (covered : Covered V)

/-- The production denotation: an inert lift whose totality is earned by the
bundle's coverage proof. -/
def toGSLT [Monoid V] : GSLT :=
  covered.definition.toInertGSLT covered.respectsEquations

/-- Production erasure preserves every graded step. -/
theorem erase_step [Monoid V] {source target : Pattern × V}
    (step : covered.toGSLT.Step source target) :
    langReducesUsing RelationEnv.empty covered.definition.toLanguageDef
      source.1 target.1 :=
  covered.definition.toInertGSLT_erase_step covered.respectsEquations step

/-- Coverage supplies the reflection half: every authored base step lifts
from every accumulator value. -/
theorem lift_step [Monoid V] {source target : Pattern}
    (step : langReducesUsing RelationEnv.empty
      covered.definition.toLanguageDef source target)
    (accumulator : V) :
    ∃ value, covered.toGSLT.Step (source, accumulator) (target, value) :=
  covered.definition.toInertGSLT_lift_step covered.respectsEquations
    covered.coverage step accumulator

end Covered

end GradedLanguageDef

/-! ## Positive and negative examples -/

section Examples

/-- A weight table over natural-number grades, naming one rule. -/
private def exampleGraded : GradedLanguageDef ℕ where
  toLanguageDef := .empty "example"
  weights := [⟨"communicate", 3⟩]

/-- A concrete rule named by the example table. -/
private def exampleRule : RewriteRule where
  name := "communicate"
  typeContext := []
  premises := []
  left := .fvar "x"
  right := .fvar "x"

/-- A concrete rule the table does not mention. -/
private def exampleSilentRule : RewriteRule where
  name := "administrate"
  typeContext := []
  premises := []
  left := .fvar "x"
  right := .fvar "x"

/-- A covered production bundle with one executable, explicitly graded
rule. -/
private def coveredExample : GradedLanguageDef.Covered ℕ where
  definition :=
    { toLanguageDef :=
        { LanguageDef.empty "covered" with rewrites := [exampleRule] }
      weights := [⟨"communicate", 3⟩] }
  respectsEquations :=
    GradedReductionRespectsEquations.of_equation_free rfl
  coverage := by
    intro rule membership
    simp only [List.mem_singleton] at membership
    subst rule
    rfl

/-- The covered bundle denotes the inert graded lift; the authored grade is
retained without invoking a default policy. -/
example : coveredExample.definition.ruleGrade? exampleRule = some 3 := by
  rfl

/-- A declaration with one executable rule and no grade row. -/
private def uncoveredGraded : GradedLanguageDef ℕ where
  toLanguageDef :=
    { LanguageDef.empty "uncovered" with rewrites := [exampleSilentRule] }
  weights := []

/-- The missing grade is visible as failure of the production coverage
obligation. -/
theorem uncoveredGraded_not_covers : ¬ uncoveredGraded.Covers := by
  intro covers
  have covered := covers exampleSilentRule (by simp [uncoveredGraded])
  simp [GradedLanguageDef.ruleGrade?, uncoveredGraded] at covered

/-- Consequently no covered production bundle can claim that exact raw
declaration. -/
theorem uncoveredGraded_has_no_covered_bundle :
    ¬ ∃ covered : GradedLanguageDef.Covered ℕ,
      covered.definition = uncoveredGraded := by
  rintro ⟨covered, equal⟩
  apply uncoveredGraded_not_covers
  rw [← equal]
  exact covered.coverage

-- Positive: the authored row is read back by the partial table.
example : exampleGraded.ruleGrade? exampleRule = some 3 := by
  unfold GradedLanguageDef.ruleGrade? exampleGraded exampleRule
  simp

-- Negative: an unmentioned rule has NO grade — partiality is explicit.
example : exampleGraded.ruleGrade? exampleSilentRule = none := by
  apply GradedLanguageDef.ruleGrade?_eq_none_of_not_mentioned
  intro row membership
  simp only [exampleGraded, List.mem_singleton] at membership
  subst membership
  simp [exampleSilentRule]

-- Positive: the free policy interprets that absence as the unit — an
-- explicit, named commitment.
example : exampleGraded.freeRuleGrade exampleSilentRule = 1 := by
  unfold GradedLanguageDef.freeRuleGrade
  rw [show exampleGraded.ruleGrade? exampleSilentRule = none from by
    apply GradedLanguageDef.ruleGrade?_eq_none_of_not_mentioned
    intro row membership
    simp only [exampleGraded, List.mem_singleton] at membership
    subst membership
    simp [exampleSilentRule]]
  rfl

-- Negative: the two policies genuinely differ — the free grade of the
-- mentioned rule is its authored value, not the default.
example : exampleGraded.freeRuleGrade exampleRule = 3 := by
  unfold GradedLanguageDef.freeRuleGrade GradedLanguageDef.ruleGrade?
    exampleGraded exampleRule
  simp

end Examples

end Mettapedia.GSLT.LanguageDef
