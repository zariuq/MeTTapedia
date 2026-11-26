import Mettapedia.GSLT.Compilation.ContextualReferenceOnTheStep
import Mettapedia.GSLT.Compilation.Uniform.QueryRulesOnTheStep

/-!
# Hosting through a black box

A compiler can emit a single rule whose condition is a new built-in relation
computing the source's successors. Such a host exists for every finitely
branching theory whose terms have an encoding, so its existence is a property
of the source alone and says nothing about the target rule language
(`blackBoxHosted_iff`).

It is also not compositional. The steps of a union of rule lists need not be
the union of the steps of the parts, because a premise of a rule in one part
may need a rule of the other part. In the example below the union rewrites
`Wrap(A)` to `Wrap(B)`, while neither part has any step from `Wrap(A)`. The
black boxes of the two parts together cannot fire at `Wrap(A)`; the black box of
the union can (`parts_box_stuck`, `union_box_fires`).

A compiler that translates each authored rule into target rules has no such
defect at the level of programs: the uniform compiler maps a union of rule lists
to the concatenation of the compiled programs (`compile_union`), and its
conditions ask only the relations the presentation itself declares.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.BlackBoxHosting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines (rowRule row_of_singleton)
open RuleSyntax.ComputedConditions
open RootRewritesOnTheStep (encode)
open OSLFReferenceOnTheStep (Encoding builtins schema mem_successors patternEncoding)

universe u

/-! ## A black-box host exists exactly for finitely branching sources -/

/-- Some program, with built-in relations of the compiler's choice, computes
exactly the encoded successors of every term. -/
def BlackBoxHosted (G : GSLT.{u}) : Prop :=
  ∃ (E : Encoding G.Term) (relations : Executable.Builtins) (program : List Executable.Schema),
    ∀ s t, E.store t ∈ Executable.successors relations program (E.store s) ↔ G.Step s t

/-- A function lists exactly the successors of each term. -/
def FinitelyBranching (G : GSLT.{u}) : Prop :=
  ∃ next : G.Term → List G.Term, ∀ s t, t ∈ next s ↔ G.Step s t

/-- Read back the rows that are encodings of states. -/
def decodeRows {State : Type u} (E : Encoding State) (rows : List Expr) : List State :=
  rows.filterMap fun row =>
    match E.read row with
    | some s => if E.store s = row then some s else none
    | none => none

theorem mem_decodeRows {State : Type u} (E : Encoding State) (rows : List Expr) (s : State) :
    s ∈ decodeRows E rows ↔ E.store s ∈ rows := by
  unfold decodeRows
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨row, member, found⟩
    split at found
    · split at found
      · rename_i stored
        cases found
        rw [stored]
        exact member
      · cases found
    · cases found
  · intro member
    exact ⟨E.store s, member, by simp [E.read_store]⟩

/-- Black-box hosting holds exactly for finitely branching theories whose terms
have an encoding. -/
theorem blackBoxHosted_iff (G : GSLT.{u}) :
    BlackBoxHosted G ↔ Nonempty (Encoding G.Term) ∧ FinitelyBranching G := by
  constructor
  · rintro ⟨E, relations, program, hosted⟩
    refine ⟨⟨E⟩, fun s => decodeRows E (Executable.successors relations program (E.store s)), ?_⟩
    intro s t
    rw [mem_decodeRows]
    exact hosted s t
  · rintro ⟨⟨E⟩, next, listed⟩
    refine ⟨E, builtins E next, [schema], fun s t => ?_⟩
    rw [mem_successors]
    constructor
    · rintro ⟨other, member, same⟩
      rw [E.injective same]
      exact (listed s other).mp member
    · intro step
      exact ⟨t, (listed s t).mpr step, rfl⟩

/-! ## One rule that asks a relation for the successor -/

/-- The condition `R_name(x, y)` on the taken row `x` and the made row `y`. -/
def call (name : ℕ) : Condition ℕ Tm := { name := name, arguments := [.var 0], value := .var 1 }

/-- Take a row, ask the relation `name` for a successor, and make it. -/
def box (name : ℕ) : Executable.Schema := ⟨.var 0, [call name], .var 1⟩

theorem box_step (R : Relations) (name : ℕ) (x : Expr) (after : Multiset Expr) :
    RelationStep R (box name).rule {x} after ↔ ∃ y, R name [x] y ∧ after = {y} := by
  constructor
  · rintro ⟨θ, rest, split, _, _, asked, output⟩
    have head : θ 0 = x ∧ rest = 0 := by
      apply row_of_singleton
      exact split
    have answered := asked (call name) (List.mem_singleton_self _)
    refine ⟨θ 1, by simpa [call, inst, head.1] using answered, ?_⟩
    simpa [box, Executable.Schema.rule, rowRule, inst, head.2] using output
  · rintro ⟨y, related, rfl⟩
    let θ : ℕ → Expr := fun index => if index = 0 then x else y
    refine ⟨θ, 0, ?_, ?_, ?_, ?_, ?_⟩
    · simp [box, Executable.Schema.rule, rowRule, θ, inst]
    · simp [box, Executable.Schema.rule, rowRule]
    · simp [box, Executable.Schema.rule, rowRule, equationsOf]
    · intro c member
      have equal : c = call name := List.mem_singleton.mp member
      subst c
      simpa [call, θ, inst] using related
    · simp [box, Executable.Schema.rule, rowRule, θ, inst]

/-! ## The steps of a union are not the union of the steps -/

namespace Union

open ContextualReferenceOnTheStep.Controls (a b wrap nodeSort language)

abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- `A` rewrites to `B`. -/
def root : RewriteRule := { name := "root", typeContext := [], premises := [], left := a, right := b }

/-- `Wrap(old)` rewrites to `Wrap(new)` when `old` rewrites to `new`. -/
def descend : RewriteRule :=
  { name := "descend", typeContext := [("old", nodeSort), ("new", nodeSort)],
    premises := [.congruence (.fvar "old") (.fvar "new")],
    left := wrap (.fvar "old"), right := wrap (.fvar "new") }

/-- The presentation of the contextual example with the given rules. -/
def withRules (rules : List RewriteRule) : LanguageDef := { language with rewrites := rules }

theorem union_is_example : withRules ([root] ++ [descend]) = language := rfl

/-- In the union, `Wrap(A)` rewrites to `Wrap(B)`. -/
theorem union_step : Step base (withRules ([root] ++ [descend])) (wrap a) (wrap b) :=
  ⟨2, mem_rewriteAt_iff_stepAt.mp (by decide +kernel)⟩

/-- The rule for `A` alone has no step from `Wrap(A)`. -/
theorem root_part_stuck (t : Pattern) : ¬ Step base (withRules [root]) (wrap a) t :=
  not_step_of_matchPatternForRule_eq_nil fun rule member => by
    rw [List.mem_singleton.mp member]
    decide +kernel

/-- The rule for `Wrap` alone has no step from `Wrap(A)`: its premise needs a
step from `A`, and no rule of this part applies to `A`. -/
theorem descend_part_stuck (t : Pattern) : ¬ Step base (withRules [descend]) (wrap a) t := by
  have inner : ∀ fuel candidate, ¬ StepAt base (withRules [descend]) fuel a candidate :=
    fun fuel _ step => not_step_of_matchPatternForRule_eq_nil (fun rule member => by
      rw [List.mem_singleton.mp member]
      decide +kernel) ⟨fuel, step⟩
  have bound : ∀ bindings ∈ matchPatternForRule (withRules [descend]) descend (wrap a),
      applyBindings bindings (.fvar "old") = a := by
    decide +kernel
  rintro ⟨_, step⟩
  cases step with
  | @rule fuel _ _ rule initial final member matched premises _ =>
      obtain rfl : rule = descend := List.mem_singleton.mp member
      change PremisesAt base (withRules [descend]) fuel initial
        [.congruence (.fvar "old") (.fvar "new")] final at premises
      cases premises with
      | cons first _ =>
          cases first with
          | congruence first _ _ =>
              rw [bound initial matched] at first
              exact inner _ _ first

/-- The step relation of the union is not the union of the parts' step relations. -/
theorem steps_of_union_not_union :
    ¬ ∀ s t, Step base (withRules ([root] ++ [descend])) s t ↔
      Step base (withRules [root]) s t ∨ Step base (withRules [descend]) s t := by
  intro split
  rcases (split (wrap a) (wrap b)).mp union_step with stuck | stuck
  · exact root_part_stuck _ stuck
  · exact descend_part_stuck _ stuck

/-- The black box of part `i` relates encoded terms by the steps of that part. -/
def boxRelations (parts : List LanguageDef) : Relations :=
  fun name arguments value => ∃ language ∈ parts[name]?, ∃ s t,
    arguments = [encode s] ∧ value = encode t ∧ Step base language s t

/-- The black box of the union fires at `Wrap(A)` and makes `Wrap(B)`. -/
theorem union_box_fires :
    RelationStep (boxRelations [withRules ([root] ++ [descend])]) (box 0).rule
      {encode (wrap a)} {encode (wrap b)} :=
  (box_step _ 0 _ _).mpr ⟨encode (wrap b), ⟨_, rfl, wrap a, wrap b, rfl, rfl, union_step⟩, rfl⟩

/-- **Negative**: the black boxes of the two parts, as one program, have no
firing at `Wrap(A)`. -/
theorem parts_box_stuck (name : ℕ) (after : Multiset Expr) :
    ¬ RelationStep (boxRelations [withRules [root], withRules [descend]]) (box name).rule
      {encode (wrap a)} after := by
  rw [box_step]
  rintro ⟨_, ⟨language, part, s, t, same, -, step⟩, -⟩
  have source : wrap a = s := patternEncoding.injective (List.singleton_inj.mp same)
  subst source
  rcases name with _ | _ | name
  · simp only [List.getElem?_cons_zero, Option.mem_def, Option.some.injEq] at part
    subst part
    exact root_part_stuck _ step
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.mem_def,
      Option.some.injEq] at part
    subst part
    exact descend_part_stuck _ step
  · simp at part

end Union

/-! ## Rule-by-rule compilation maps unions to concatenations -/

open Uniform.QueryRulesOnTheStep (lowerRules compile)

theorem lowerRules_append (inputs : String → ℕ → Bool) {first second : List RewriteRule}
    {firstRules secondRules : List (RuleWithCondition ℕ Tm)}
    (one : lowerRules inputs first = .ok firstRules) (two : lowerRules inputs second = .ok secondRules) :
    lowerRules inputs (first ++ second) = .ok (firstRules ++ secondRules) := by
  induction first generalizing firstRules with
  | nil =>
      simp only [lowerRules, Except.ok.injEq] at one
      subst one
      simpa using two
  | cons rule rules ih =>
      cases lowered : Uniform.QueryRulesOnTheStep.lowerRule inputs rule with
      | error reason => simp [lowerRules, lowered] at one
      | ok compiled =>
          cases others : lowerRules inputs rules with
          | error reason => simp [lowerRules, lowered, others] at one
          | ok rest =>
              simp only [lowerRules, lowered, others, Except.ok.injEq] at one
              subst one
              simp [lowerRules, lowered, ih others]

/-- Compiling the union of two rule lists over one presentation gives the
concatenation of the two compiled programs. -/
theorem compile_union (inputs : String → ℕ → Bool) (language : LanguageDef)
    {first second : List RewriteRule} {firstRules secondRules : List (RuleWithCondition ℕ Tm)}
    (one : compile inputs { language with rewrites := first } = .ok firstRules)
    (two : compile inputs { language with rewrites := second } = .ok secondRules) :
    compile inputs { language with rewrites := first ++ second } = .ok (firstRules ++ secondRules) := by
  unfold compile at one two ⊢
  by_cases guard : (language.equations.isEmpty && !language.hasAlgebraDeclarations) = true
  · simp only [LanguageDef.hasAlgebraDeclarations] at guard
    simp only [LanguageDef.hasAlgebraDeclarations, guard, if_true] at one two ⊢
    exact lowerRules_append inputs one two
  · simp only [LanguageDef.hasAlgebraDeclarations] at guard
    simp only [LanguageDef.hasAlgebraDeclarations, guard] at one
    cases one

end Mettapedia.GSLT.Compilation.BlackBoxHosting

#print axioms Mettapedia.GSLT.Compilation.BlackBoxHosting.blackBoxHosted_iff
#print axioms Mettapedia.GSLT.Compilation.BlackBoxHosting.box_step
#print axioms Mettapedia.GSLT.Compilation.BlackBoxHosting.Union.steps_of_union_not_union
#print axioms Mettapedia.GSLT.Compilation.BlackBoxHosting.Union.union_box_fires
#print axioms Mettapedia.GSLT.Compilation.BlackBoxHosting.Union.parts_box_stuck
#print axioms Mettapedia.GSLT.Compilation.BlackBoxHosting.compile_union
