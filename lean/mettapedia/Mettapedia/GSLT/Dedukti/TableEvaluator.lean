import Mettapedia.GSLT.Dedukti.ConfluenceExamples
import Mathlib.Data.Finset.Lattice.Basic

/-!
# A rule-table evaluator: the declared rules as data in the term

A theory of the λΠ-calculus modulo has its declared rules in its definition:
a different set of rules is a different theory.  The evaluator defined here
is one theory.  A term of it is a pair of a finite rule table and a λΠ term.
It has one fixed rule, beta, and its other steps apply a rule of the table
that the term carries, at any position.  The table is not changed by a step.

This follows the universal Turing-machine theory
(`Mettapedia.Languages.TuringMachine.universalTheory`), where the transition
table is a part of the term and the rules of the theory mention no table.

## What is proved

* `tableEvaluator` is a theory presented through its contexts.  A context is
  a term with holes together with a table of its own; filling takes the union
  of the tables.  Its reduction is closed under contexts
  (`tableEvaluator_contextClosed`).
* **It hosts the running presentation of every theory with finitely many
  declared rules and no transparent definition** (`loadMap_hosting`).  The
  class is `Theory.Tabular`; the map loads the table of the theory next to
  each term.  Members: every finite signature without definitions and with a
  list of rules (`ofSig_tabular`), in particular the theory of the
  Cousineau–Dowek embedding of every pure type system (`cdTheory_tabular`).
* It is a host for theories that no confluent theory hosts: a table may hold
  two rules for one left side (`tableEvaluator_hosts_choice`,
  `tableEvaluator_not_confluent`), so it is not hosted by any orthogonal
  theory (`tableEvaluator_not_hosted_by_orthogonal`).

## What is not hosted

* A theory with a transparent definition, or with infinitely many declared
  rules, is not in the class.
* A mutable space is not hosted: no context of the evaluator withdraws a rule
  (`space_not_hosted_by_tableEvaluator`).
* The map is not exhausting (`loadMap_not_exhausting`): the evaluator has the
  same term under every other table.

## First-order rules, and what binders need

The rules of a table are instantiated by the existing `inst`.

* For a rule without binder, instantiation is first-order substitution:
  replace each variable, with no adjustment (`inst_eq_substitute`).  A table
  of such rules (`FirstOrderTable`) needs nothing else from the evaluator
  than matching and substitution.
* A rule whose right side binds needs more: the assigned terms are lifted
  over the binders they pass.  First-order substitution captures
  (`substitute_captures`).
* Beta is not a rule of any table.  It is the fixed rule of the evaluator:
  with the empty table the evaluator is the pure calculus
  (`emptyTable_hosts_beta`).
* A pattern variable beneath a binder of a left side cannot stand for a term
  that mentions the bound variable (`instantiate_ne_bound`): higher-order
  patterns are outside `inst`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig lookupBody lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Tables -/

/-- A finite table of rewrite rules. -/
abbrev RuleTable : Type := Finset RewriteRule

/-- The theory that a table declares: its rules, no constant and no
definition. -/
def Theory.ofTable (table : RuleTable) : Theory where
  constType := fun _ => none
  body := fun _ => none
  rule := fun rule => rule ∈ table

/-- **A theory given by a table**: its declared rules are the rules of the
table, and it has no transparent definition. -/
structure Theory.Tabular (theory : Theory) (table : RuleTable) : Prop where
  rules : ∀ rule, theory.rule rule ↔ rule ∈ table
  undefined : ∀ name, theory.body name = none

theorem Theory.ofTable_tabular (table : RuleTable) : (Theory.ofTable table).Tabular table :=
  ⟨fun _ => Iff.rfl, fun _ => rfl⟩

/-- Two theories with the same definitions and the same rules have the same
root contractions. -/
theorem RootStep.congr {first second : Theory}
    (bodies : ∀ name, first.body name = second.body name)
    (rules : ∀ rule, first.rule rule → second.rule rule) {source target : Term}
    (step : RootStep first source target) : RootStep second source target := by
  cases step with
  | beta domain body argument => exact .beta domain body argument
  | delta defined => exact .delta ((bodies _).symm.trans defined)
  | rule assignment member => exact .rule assignment (rules _ member)

theorem Step.congr {first second : Theory}
    (bodies : ∀ name, first.body name = second.body name)
    (rules : ∀ rule, first.rule rule → second.rule rule) {source target : Term}
    (step : Step first source target) : Step second source target := by
  cases step with
  | inContext context root => exact .inContext context (root.congr bodies rules)

/-- **The steps of a theory given by a table are the steps of the table.** -/
theorem Theory.Tabular.step_iff {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) {source target : Term} :
    Step theory source target ↔ Step (Theory.ofTable table) source target :=
  ⟨Step.congr (fun name => tabular.undefined name) fun rule member => (tabular.rules rule).mp member,
    Step.congr (fun name => (tabular.undefined name).symm) fun rule member =>
      (tabular.rules rule).mpr member⟩

/-- A larger table has at least the steps of a smaller one. -/
theorem Step.ofTable_mono {small large : RuleTable} (contained : small ⊆ large)
    {source target : Term} (step : Step (Theory.ofTable small) source target) :
    Step (Theory.ofTable large) source target :=
  Step.congr (first := Theory.ofTable small) (second := Theory.ofTable large) (fun _ => rfl)
    (fun _ member => contained member) step

/-! ## Terms and contexts that carry a table -/

/-- **A term of the evaluator**: a table and a term. -/
structure Tabled where
  table : RuleTable
  term : Term
  deriving DecidableEq

/-- The tables of the terms that fill the holes of a context, each as often
as its hole occurs. -/
def TermContext.tables {slots : Type} (assigned : slots → RuleTable) :
    TermContext slots → RuleTable
  | .hole slot => assigned slot
  | .srt _ => ∅
  | .con _ => ∅
  | .var _ => ∅
  | .pi domain body => domain.tables assigned ∪ body.tables assigned
  | .lam domain body => domain.tables assigned ∪ body.tables assigned
  | .app function argument => function.tables assigned ∪ argument.tables assigned

theorem TermContext.tables_ofTerm {slots : Type} (assigned : slots → RuleTable) (term : Term) :
    (TermContext.ofTerm term : TermContext slots).tables assigned = ∅ := by
  induction term with
  | srt sort => rfl
  | con name => rfl
  | var index => rfl
  | pi domain body ihDomain ihBody => simp [TermContext.ofTerm, TermContext.tables, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      simp [TermContext.ofTerm, TermContext.tables, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [TermContext.ofTerm, TermContext.tables, ihFunction, ihArgument]

theorem TermContext.tables_union {slots : Type} (first second : slots → RuleTable)
    (context : TermContext slots) :
    context.tables (fun slot => first slot ∪ second slot) =
      context.tables first ∪ context.tables second := by
  induction context with
  | hole slot => rfl
  | srt sort => simp [TermContext.tables]
  | con name => simp [TermContext.tables]
  | var index => simp [TermContext.tables]
  | pi domain body ihDomain ihBody =>
      simp only [TermContext.tables, ihDomain, ihBody]
      exact Finset.union_union_union_comm _ _ _ _
  | lam domain body ihDomain ihBody =>
      simp only [TermContext.tables, ihDomain, ihBody]
      exact Finset.union_union_union_comm _ _ _ _
  | app function argument ihFunction ihArgument =>
      simp only [TermContext.tables, ihFunction, ihArgument]
      exact Finset.union_union_union_comm _ _ _ _

theorem TermContext.tables_bind {slots inner : Type} (assigned : inner → RuleTable)
    (plugged : slots → TermContext inner) (context : TermContext slots) :
    (context.bind plugged).tables assigned =
      context.tables fun slot => (plugged slot).tables assigned := by
  induction context with
  | hole slot => rfl
  | srt sort => rfl
  | con name => rfl
  | var index => rfl
  | pi domain body ihDomain ihBody => simp [TermContext.bind, TermContext.tables, ihDomain, ihBody]
  | lam domain body ihDomain ihBody => simp [TermContext.bind, TermContext.tables, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [TermContext.bind, TermContext.tables, ihFunction, ihArgument]

/-- The holes of a context all filled from one table add nothing to it. -/
theorem TermContext.tables_const_subset {slots : Type} (table : RuleTable)
    (context : TermContext slots) : context.tables (fun _ => table) ⊆ table := by
  induction context with
  | hole slot => exact Finset.Subset.refl _
  | srt sort => exact Finset.empty_subset _
  | con name => exact Finset.empty_subset _
  | var index => exact Finset.empty_subset _
  | pi domain body ihDomain ihBody => exact Finset.union_subset ihDomain ihBody
  | lam domain body ihDomain ihBody => exact Finset.union_subset ihDomain ihBody
  | app function argument ihFunction ihArgument => exact Finset.union_subset ihFunction ihArgument

/-- A context of the evaluator: a term with holes, and a table of its own. -/
structure TabledContext (slots : Type) where
  table : RuleTable
  context : TermContext slots

namespace TabledContext

variable {slots inner : Type}

/-- Fill the holes: the term is filled, and the tables are joined. -/
def fill (filling : slots → Tabled) (context : TabledContext slots) : Tabled :=
  ⟨context.table ∪ context.context.tables (fun slot => (filling slot).table),
    context.context.fill fun slot => (filling slot).term⟩

/-- Plug contexts into the holes. -/
def bind (plugged : slots → TabledContext inner) (context : TabledContext slots) :
    TabledContext inner :=
  ⟨context.table ∪ context.context.tables (fun slot => (plugged slot).table),
    context.context.bind fun slot => (plugged slot).context⟩

theorem fill_bind (filling : inner → Tabled) (plugged : slots → TabledContext inner)
    (context : TabledContext slots) :
    (context.bind plugged).fill filling = context.fill fun slot => (plugged slot).fill filling := by
  simp only [fill, bind, TermContext.fill_bind, TermContext.tables_bind, TermContext.tables_union,
    Finset.union_assoc]

end TabledContext

/-- The terms that carry a table, as a syntax with holes. -/
def tabledShape : HoleSyntax Tabled where
  Hole := TabledContext
  fill := TabledContext.fill
  bind := TabledContext.bind
  hole := fun slot => ⟨∅, .hole slot⟩
  constant := fun term => ⟨term.table, TermContext.ofTerm term.term⟩
  fill_bind := TabledContext.fill_bind
  fill_hole := fun filling slot => by
    simp [TabledContext.fill, TermContext.tables, TermContext.fill]
  fill_constant := fun filling term => by
    simp [TabledContext.fill, TermContext.tables_ofTerm, TermContext.fill_ofTerm]

/-! ## The evaluator -/

/-- **One step of the evaluator**: a beta step, or a rule of the table that
the term carries, at one position.  The table stays. -/
def TableStep (source target : Tabled) : Prop :=
  target.table = source.table ∧ Step (Theory.ofTable source.table) source.term target.term

/-- **The rule-table evaluator.** -/
def tableEvaluator : ContextTheory.{0} :=
  tabledShape.theory
    ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
    TableStep
    (fun context _ _ same =>
      congrArg (fun filling => TabledContext.fill filling context) (funext same))
    (fun same step => ⟨_, same ▸ step, rfl⟩)
    (fun step same => same ▸ step)

@[simp] theorem tableEvaluator_rewrites {source target : Tabled} :
    tableEvaluator.rewrites (interface := ()) source target ↔ TableStep source target :=
  Iff.rfl

/-- Reduction keeps the table. -/
theorem tableEvaluator_reaches {source target : Tabled}
    (reaches : tableEvaluator.Reaches (interface := ()) source target) :
    target.table = source.table ∧
      Reduces (Theory.ofTable source.table) source.term target.term := by
  induction reaches with
  | refl => exact ⟨rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨sameTable, reduces⟩ := ih
      obtain ⟨stepTable, stepTerm⟩ := step
      rw [sameTable] at stepTable stepTerm
      exact ⟨stepTable, reduces.tail stepTerm⟩

theorem Reduces.ofTable_mono {small large : RuleTable} (contained : small ⊆ large)
    {source target : Term} (reduces : Reduces (Theory.ofTable small) source target) :
    Reduces (Theory.ofTable large) source target := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.ofTable_mono contained)

/-- Reduction under the tables of the holes is reduction of the filled
context under any table that contains them. -/
theorem Reduces.fill_tabled {slots : Type} (context : TermContext slots)
    {assigned : slots → RuleTable} {large : RuleTable}
    (contained : context.tables assigned ⊆ large) {first second : slots → Term}
    (steps : ∀ slot, Reduces (Theory.ofTable (assigned slot)) (first slot) (second slot)) :
    Reduces (Theory.ofTable large) (context.fill first) (context.fill second) := by
  induction context with
  | hole slot => exact (steps slot).ofTable_mono contained
  | srt sort => exact .refl
  | con name => exact .refl
  | var index => exact .refl
  | pi domain body ihDomain ihBody =>
      obtain ⟨left, right⟩ := Finset.union_subset_iff.mp contained
      exact Reduces.pi (ihDomain left) (ihBody right)
  | lam domain body ihDomain ihBody =>
      obtain ⟨left, right⟩ := Finset.union_subset_iff.mp contained
      exact Reduces.lam (ihDomain left) (ihBody right)
  | app function argument ihFunction ihArgument =>
      obtain ⟨left, right⟩ := Finset.union_subset_iff.mp contained
      exact Reduces.app (ihFunction left) (ihArgument right)

/-- A reduction of the term under its table is a reduction of the
evaluator. -/
theorem tableEvaluator_reaches_of_reduces {table : RuleTable} {source target : Term}
    (reduces : Reduces (Theory.ofTable table) source target) :
    tableEvaluator.Reaches (interface := ()) (⟨table, source⟩ : Tabled) ⟨table, target⟩ := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail ⟨rfl, step⟩

/-- **The reduction of the evaluator is closed under contexts**: a context
may add rules, and it withdraws none. -/
theorem tableEvaluator_contextClosed : tableEvaluator.ContextClosed := by
  intro _ _ label term next step
  obtain ⟨sameTable, stepTerm⟩ := step
  refine ⟨tableEvaluator.apply label next, ?_, rfl⟩
  have reduces : Reduces
      (Theory.ofTable (label.table ∪ label.context.tables fun _ => term.table))
      (label.context.fill fun _ => term.term) (label.context.fill fun _ => next.term) :=
    Reduces.fill_tabled label.context (assigned := fun _ => term.table)
      Finset.subset_union_right fun _ => Relation.ReflTransGen.single stepTerm
  have reaches := tableEvaluator_reaches_of_reduces reduces
  have target : tableEvaluator.apply label next =
      (⟨label.table ∪ label.context.tables fun _ => term.table,
        label.context.fill fun _ => next.term⟩ : Tabled) := by
    show (⟨label.table ∪ label.context.tables fun _ => next.table,
      label.context.fill fun _ => next.term⟩ : Tabled) = _
    rw [sameTable]
  rw [target]
  exact reaches

/-! ## Loading a theory -/

/-- **Load a table next to every term.** -/
def loadMap (theory : Theory) (table : RuleTable) :
    ContextMap (rewritingTheory theory) tableEvaluator where
  interface := fun _ => ()
  term := fun term => ⟨table, term⟩
  context := fun context => ⟨table, context⟩
  term_resp := fun same => congrArg (Tabled.mk table) same
  equivariant := fun context filling => by
    show (⟨table, TermContext.fill filling context⟩ : Tabled) =
      ⟨table ∪ TermContext.tables (fun _ => table) context, TermContext.fill filling context⟩
    rw [Finset.union_eq_left.mpr (TermContext.tables_const_subset table context)]

/-- **The evaluator hosts the running presentation of every theory given by a
table.** -/
theorem loadMap_hosting {theory : Theory} {table : RuleTable} (tabular : theory.Tabular table) :
    (loadMap theory table).Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  refine ⟨fun same => congrArg Tabled.term same, fun step => ⟨rfl, tabular.step_iff.mp step⟩,
    fun {_ term next} step => ?_⟩
  obtain ⟨sameTable, stepTerm⟩ := step
  have shape : next = (⟨table, next.term⟩ : Tabled) := by
    cases next with
    | mk nextTable nextTerm =>
        have equal : nextTable = table := sameTable
        rw [equal]
  exact ⟨next.term, tabular.step_iff.mpr stepTerm, shape⟩

/-- A finite signature without definitions and a list of rules: a theory given
by a table. -/
theorem ofSig_tabular (signature : Sig) (rules : List RewriteRule)
    (undefined : ∀ name, lookupBody signature name = none) :
    (Theory.ofSig signature rules).Tabular rules.toFinset :=
  ⟨fun _ => List.mem_toFinset.symm, undefined⟩

/-- **The theory of the Cousineau–Dowek embedding of every pure type system
is given by a table.** -/
theorem cdTheory_tabular (profile : Profile) : ∃ table, (cdTheory profile).Tabular table := by
  classical
  refine ⟨universeRuleList.toFinset.filter (UniverseRule profile), fun rule => ?_, fun _ => rfl⟩
  exact ⟨fun member => Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (universeRule_mem member), member⟩,
    fun member => (Finset.mem_filter.mp member).2⟩

/-- The pure calculus is the case of the empty table: beta is the fixed rule
of the evaluator. -/
theorem empty_tabular : Theory.empty.Tabular ∅ :=
  ⟨fun _ => by simp [Theory.empty], fun _ => rfl⟩

theorem emptyTable_hosts_beta : (loadMap Theory.empty ∅).Hosting :=
  loadMap_hosting empty_tabular

/-- **Negative**: a theory with a transparent definition is given by no
table. -/
theorem not_tabular_of_defined {theory : Theory} {name : String} {body : Term}
    (defined : theory.body name = some body) (table : RuleTable) : ¬ theory.Tabular table := by
  intro tabular
  rw [tabular.undefined name] at defined
  cases defined

theorem openDefinition_not_tabular (table : RuleTable) :
    ¬ ConfluenceExamples.openDefinition.Tabular table :=
  not_tabular_of_defined (name := "c") (body := .var 0) rfl table

/-! ## Where the evaluator stands -/

/-- The table of the two rules of choice. -/
def choiceTable : RuleTable := {chooseLeft, chooseRight}

theorem withChoice_empty_tabular : (withChoice Theory.empty).Tabular choiceTable :=
  ⟨fun rule => by simp [withChoice, Theory.empty, choiceTable], fun _ => rfl⟩

/-- **The evaluator hosts a theory with choice.** -/
theorem tableEvaluator_hosts_choice : (loadMap (withChoice Theory.empty) choiceTable).Hosting :=
  loadMap_hosting withChoice_empty_tabular

/-- So the evaluator is not confluent. -/
theorem tableEvaluator_not_confluent : ¬ tableEvaluator.ConfluentUpTo :=
  fun confluent => withChoice_not_hosted_by_confluent Theory.empty_headed confluent
    (loadMap (withChoice Theory.empty) choiceTable) tableEvaluator_hosts_choice

/-- **No orthogonal theory hosts the evaluator.** -/
theorem tableEvaluator_not_hosted_by_orthogonal {host : Theory} (orthogonal : host.Orthogonal)
    (map : ContextMap tableEvaluator (rewritingTheory host)) : ¬ map.Hosting :=
  fun hosting => withChoice_not_hosted_by_orthogonal Theory.empty_headed orthogonal
    (map.comp (loadMap (withChoice Theory.empty) choiceTable))
    (hosting.comp tableEvaluator_hosts_choice)

/-- **An orthogonal theory given by a table is strictly below the evaluator**
in the hosting preorder. -/
theorem orthogonal_strictly_below {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) (orthogonal : theory.Orthogonal) :
    (∃ map : ContextMap (rewritingTheory theory) tableEvaluator, map.Hosting) ∧
      ¬ ∃ map : ContextMap tableEvaluator (rewritingTheory theory), map.Hosting :=
  ⟨⟨loadMap theory table, loadMap_hosting tabular⟩,
    fun ⟨map, hosting⟩ => tableEvaluator_not_hosted_by_orthogonal orthogonal map hosting⟩

/-- **Negative**: the evaluator does not host a mutable space. -/
theorem space_not_hosted_by_tableEvaluator (map : ContextMap spaceTheory tableEvaluator) :
    ¬ map.Hosting :=
  space_not_hosted_by_contextClosed tableEvaluator_contextClosed map

/-- **Negative**: loading is not exhausting.  The evaluator has every term
under every other table. -/
theorem loadMap_not_exhausting (theory : Theory) (table : RuleTable) :
    ¬ (loadMap theory table).Exhausting := by
  intro exhausting
  by_cases empty : table = ∅
  · obtain ⟨preimage, same⟩ := ContextMap.Exhausting.term_surjective _ exhausting (origin := ())
      (⟨{⟨.srt .type, .srt .type⟩}, .srt .type⟩ : Tabled)
    have tables : ({⟨.srt .type, .srt .type⟩} : RuleTable) = table := congrArg Tabled.table same
    rw [empty] at tables
    exact Finset.singleton_ne_empty _ tables
  · obtain ⟨preimage, same⟩ := ContextMap.Exhausting.term_surjective _ exhausting (origin := ())
      (⟨∅, .srt .type⟩ : Tabled)
    have tables : (∅ : RuleTable) = table := congrArg Tabled.table same
    exact empty tables.symm

/-! ## First-order rules, and what binders need -/

/-- First-order substitution: replace each variable, with no adjustment
beneath a binder. -/
def substitute (assignment : Nat → Term) : Term → Term
  | .var index => assignment index
  | .srt sort => .srt sort
  | .con name => .con name
  | .pi domain body => .pi (substitute assignment domain) (substitute assignment body)
  | .lam domain body => .lam (substitute assignment domain) (substitute assignment body)
  | .app function argument =>
      .app (substitute assignment function) (substitute assignment argument)

/-- A term without binder. -/
def binderFree : Term → Bool
  | .pi _ _ => false
  | .lam _ _ => false
  | .app function argument => binderFree function && binderFree argument
  | _ => true

/-- **Without binder, instantiation is first-order substitution.** -/
theorem inst_eq_substitute (assignment : Nat → Term) :
    ∀ {term : Term}, binderFree term = true → inst assignment term = substitute assignment term := by
  intro term
  induction term with
  | var index => intro _; exact inst_var assignment index
  | srt sort => intro _; rfl
  | con name => intro _; rfl
  | pi domain body _ _ => intro free; simp [binderFree] at free
  | lam domain body _ _ => intro free; simp [binderFree] at free
  | app function argument ihFunction ihArgument =>
      intro free
      simp only [binderFree, Bool.and_eq_true] at free
      rw [inst_app, ihFunction free.1, ihArgument free.2]
      rfl

/-- A table of first-order rules: no side of a rule binds. -/
def FirstOrderTable (table : RuleTable) : Prop :=
  ∀ rule ∈ table, binderFree rule.lhs = true ∧ binderFree rule.rhs = true

/-- **For a table of first-order rules, a root contraction is beta or a
first-order instance of a rule of the table.** -/
theorem rootStep_firstOrder_iff {table : RuleTable} (firstOrder : FirstOrderTable table)
    {source target : Term} :
    RootStep (Theory.ofTable table) source target ↔
      (∃ domain body argument, source = .app (.lam domain body) argument ∧
        target = subst0 argument body) ∨
      ∃ rule ∈ table, ∃ assignment : Nat → Term,
        source = substitute assignment rule.lhs ∧ target = substitute assignment rule.rhs := by
  constructor
  · intro step
    cases step with
    | beta domain body argument => exact Or.inl ⟨domain, body, argument, rfl, rfl⟩
    | delta defined => cases defined
    | @rule rule assignment member =>
        obtain ⟨left, right⟩ := firstOrder rule member
        exact Or.inr ⟨rule, member, assignment, inst_eq_substitute assignment left,
          inst_eq_substitute assignment right⟩
  · rintro (⟨domain, body, argument, rfl, rfl⟩ | ⟨rule, member, assignment, rfl, rfl⟩)
    · exact .beta domain body argument
    · obtain ⟨left, right⟩ := firstOrder rule member
      rw [← inst_eq_substitute assignment left, ← inst_eq_substitute assignment right]
      exact .rule assignment member

/-- `k x ⟶ λ y : Type. x`: a rule whose right side binds. -/
def constantFunctionRule : RewriteRule :=
  ⟨.app (.con "k") (.var 0), .lam (.srt .type) (.var 1)⟩

/-- **A right side that binds needs lifting.**  At the free variable `z` the
instance is `λ y. z`; first-order substitution gives `λ y. y`, where the
variable is captured. -/
theorem substitute_captures :
    inst (fun _ => .var 0) constantFunctionRule.rhs = .lam (.srt .type) (.var 1) ∧
      substitute (fun _ => .var 0) constantFunctionRule.rhs = .lam (.srt .type) (.var 0) := by
  decide

/-- The rule is not first-order, and the two readings of it differ. -/
theorem constantFunctionRule_not_firstOrder :
    binderFree constantFunctionRule.rhs = false ∧
      inst (fun _ => .var 0) constantFunctionRule.rhs ≠
        substitute (fun _ => .var 0) constantFunctionRule.rhs := by
  decide

/-- **A pattern variable beneath a binder stands for no term that mentions
the bound variable.**  The left side `f (λ y. X)` matches no `f (λ y. y)`:
higher-order patterns are outside instantiation. -/
theorem instantiate_ne_bound (assignment : Nat → Term) (index : Nat) :
    instantiate assignment 1 (.var (index + 1)) ≠ .var 0 := by
  have unfolded : instantiate assignment 1 (.var (index + 1)) = lift 1 0 (assignment index) := by
    simp [instantiate]
  rw [unfolded]
  cases assignment index <;> simp [lift]

#print axioms tableEvaluator
#print axioms tableEvaluator_contextClosed
#print axioms loadMap_hosting
#print axioms cdTheory_tabular
#print axioms tableEvaluator_not_confluent
#print axioms tableEvaluator_not_hosted_by_orthogonal
#print axioms orthogonal_strictly_below
#print axioms space_not_hosted_by_tableEvaluator
#print axioms loadMap_not_exhausting
#print axioms rootStep_firstOrder_iff
#print axioms substitute_captures
#print axioms instantiate_ne_bound

end Mettapedia.GSLT.Dedukti
