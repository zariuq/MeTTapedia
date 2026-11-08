import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSymbolicCountQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalCountQueries

/-!
# A count invariant over a genuinely nonprincipal contextual constraint

The unknown two-parameter context satisfies F(0,1)=0. Its image must be
the constant 0 or the first parameter. Consequently F(1,0) matches exactly
one of two stored literals, although the matching occurrence differs.
The equation cannot have a completed principal update. The native guard
still admits a firing with its unresolved information retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNonprincipalCountControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalGuards ContextualPredicateQueryAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

abbrev base : Signature where
  Srt := Unit
  Op _ := Nat
  arity _ := []

abbrev locals (impossible : Empty) : MetaArity base := nomatch impossible
abbrev functions (_ : Unit) : MetaArity base := ([(), ()], ())

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Nat)

def literal {V : Type} {declaration : V → MetaArity base} {Γ : Ctx base} (number : Nat) :
    Term (signature base declaration) Γ () := .op (.inl number) .nil

def call (left right : Term (signature base functions) [] ()) : Term (signature base functions) [] () :=
  .op (.inr (.mk ())) (.cons left (.cons right .nil))

def runBody {V : Type} {declaration : V → MetaArity base}
    (body : Term (signature base declaration) [(), ()] ())
    (left right : Term (signature base declaration) [] ()) : Term (signature base declaration) [] () :=
  bind (argsToSub (.cons left (.cons right .nil))) body

/-- Head discrimination includes every future metavariable family, rather
than testing only the two displayed assignments. -/
theorem body_choices {V : Type} {declaration : V → MetaArity base}
    (body : Term (signature base declaration) [(), ()] ())
    (equation : runBody body (literal 0) (literal 1) = literal 0) :
    body = literal 0 ∨ body = .var .zero := by
  cases body with
  | var index =>
      cases index with
      | zero => exact .inr rfl
      | succ index =>
          cases index with
          | zero =>
              change literal (declaration := declaration) (Γ := []) 1 = literal 0 at equation
              have impossible : (1 : Nat) = 0 := Sum.inl.inj (Term.op.inj equation).1
              omega
          | succ impossible => exact nomatch impossible
  | op operator arguments =>
      cases operator with
      | inl number =>
          cases arguments
          change literal (declaration := declaration) (Γ := []) number = literal 0 at equation
          have same : number = 0 := Sum.inl.inj (Term.op.inj equation).1
          subst number
          exact .inl rfl
      | inr name =>
          change Term.op (S := signature base declaration) (.inr name) (bindArgs _ arguments) = literal 0 at equation
          have impossible := (Term.op.inj equation).1
          cases impossible

def problem : ContextualResidual.Problem functions :=
  [(observe (call (literal 0) (literal 1)), observe (literal (Γ := []) 0))]

abbrev before : ContextualConditionalExecution.State locals Nat [] () :=
  ⟨Unit, inferInstance, functions, ∅, problem, {0, 1}, fun occurrence =>
    ofStored locals functions (.shared (if occurrence = 0 then literal 0 else literal 1))⟩

abbrev active := ContextualActivatedStep.target locals functions

def nativeCall (left right : Term (signature base active) [] ()) : Term (signature base active) [] () :=
  .op (.inr (.mk (.inr ()))) (.cons left (.cons right .nil))

def rule : RuleInstance (Term (signature base (ContextualActivatedStep.source locals functions)) [] ()) :=
  ⟨[], [], [], [.count (instantiate (ContextualSelectionViews.capturedSource locals functions)
    (call (literal 1) (literal 0))) 1], [literal 7]⟩

def picked : Selection Nat := ⟨[], [], [2]⟩
def outputs (_ : Nat) : Term (signature base active) [] () := literal 7

def information := ContextualConditionalExecution.information locals functions ∅ picked rule before.rows problem
def rows := ContextualConditionalExecution.guardRows locals functions before.rows
def pattern : Term (signature base active) [] () := nativeCall (literal 1) (literal 0)

theorem information_explicit : information =
    [(observe (nativeCall (literal 0) (literal 1)), observe (literal (Γ := []) 0))] := by
  with_unfolding_all rfl

def model {V : Type} (declaration : V → MetaArity base)
    (body : Term (signature base declaration) [(), ()] ()) : Assignment active declaration
  | .inl name => nomatch name.name
  | .inr () => body

theorem constant_model {V : Type} (declaration : V → MetaArity base) :
    ContextualResidual.Models (model declaration (literal 0)) information := by
  rw [information_explicit]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem projection_model {V : Type} (declaration : V → MetaArity base) :
    ContextualResidual.Models (model declaration (.var .zero)) information := by
  rw [information_explicit]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem value_cases {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment active declaration) (solved : ContextualResidual.Models candidate information) :
    instantiate candidate pattern = literal 0 ∨ instantiate candidate pattern = literal 1 := by
  have equation := solved (observe (nativeCall (literal 0) (literal 1)), observe (literal (Γ := []) 0))
    (by rw [information_explicit]; exact List.mem_singleton_self _)
  change observe (instantiate candidate (nativeCall (literal 0) (literal 1))) =
    observe (literal (declaration := declaration) (Γ := []) 0) at equation
  have bodyEquation := observe_injective equation
  change runBody (candidate (.inr ())) (literal 0) (literal 1) = literal 0 at bodyEquation
  rcases body_choices _ bodyEquation with constant | projection
  · left
    change runBody (candidate (.inr ())) (literal 1) (literal 0) = literal 0
    rw [constant]
    rfl
  · right
    change runBody (candidate (.inr ())) (literal 1) (literal 0) = literal 1
    rw [projection]
    rfl

private theorem row_at (occurrence : Nat) (present : occurrence ∈ before.present) :
    rows occurrence = ofStored locals active (.shared (literal occurrence)) := by
  rcases Finset.mem_insert.mp present with zero | one
  · subst occurrence
    rfl
  · have same := Finset.mem_singleton.mp one
    subst occurrence
    rfl

theorem region_at_literal {V : Type} (declaration : V → MetaArity base) (candidate : Assignment active declaration)
    (number : Nat) (present : number = 0 ∨ number = 1)
    (value : instantiate candidate pattern = literal number) :
    region locals candidate rows before.present pattern = {number} := by
  classical
  ext occurrence
  constructor
  · intro member
    obtain ⟨inside, matched⟩ := (mem_region _ _ _ _ _ _).mp member
    rw [row_at occurrence inside, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff] at matched
    rw [value] at matched
    change literal (declaration := declaration) (Γ := []) number = literal occurrence at matched
    have same : number = occurrence := Sum.inl.inj (Term.op.inj matched).1
    exact Finset.mem_singleton.mpr same.symm
  · intro member
    have same : occurrence = number := Finset.mem_singleton.mp member
    subst occurrence
    have inside : number ∈ before.present := by
      rcases present with rfl | rfl <;> decide +kernel
    apply (mem_region _ _ _ _ _ _).mpr
    refine ⟨inside, ?_⟩
    rw [row_at number inside, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
    exact value

theorem count_guard : Ask locals information rows before.present (.count pattern 1) := by
  intro Future future candidate solved
  rcases value_cases future candidate solved with zero | one
  · change (region locals candidate rows before.present pattern).card = 1
    rw [region_at_literal future candidate 0 (.inl rfl) zero]
    rfl
  · change (region locals candidate rows before.present pattern).card = 1
    rw [region_at_literal future candidate 1 (.inr rfl) one]
    rfl

/-- A fixed successful-match set loses one of the two genuine source models. -/
theorem no_fixed_matching_table (seen : Finset Nat) :
    ¬ AskData information (matchingQuery locals pattern seen) (fun occurrence => (occurrence, rows occurrence)) before.present := by
  intro observed
  have zero := (matching_holds_iff locals pattern seen rows before.present
    ⟨Empty, locals, model locals (literal 0)⟩).mp
      (observed Empty locals (model locals (literal 0)) (constant_model locals))
  have one := (matching_holds_iff locals pattern seen rows before.present
    ⟨Empty, locals, model locals (.var .zero)⟩).mp
      (observed Empty locals (model locals (.var .zero)) (projection_model locals))
  rw [region_at_literal locals (model locals (literal 0)) 0 (.inl rfl) rfl] at zero
  rw [region_at_literal locals (model locals (.var .zero)) 1 (.inr rfl) rfl] at one
  have clash : ({0} : Finset Nat) = {1} := zero.trans one.symm
  have member : (0 : Nat) ∈ ({1} : Finset Nat) := clash ▸ Finset.mem_singleton_self 0
  have impossible : (0 : Nat) = 1 := Finset.mem_singleton.mp member
  omega

theorem no_completed_update (update : ContextualFrameUpdate.Update information) : update.remaining ≠ [] := by
  intro completed
  have completeTable := (ContextualPrincipalCountQueries.count_as_data_query_iff locals update completed
    rows before.present pattern 1).mp count_guard
  exact no_fixed_matching_table _ completeTable.2

theorem admitted : ContextualConditionalExecution.Admitted locals before rule picked outputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Empty, locals, model locals (literal 0), constant_model locals⟩, ?_⟩
  intro check member
  have same : check = .count pattern 1 := List.mem_singleton.mp member
  subst check
  exact count_guard

noncomputable def predicate (candidate : Candidate active) (_occurrence : Nat) (row : Row locals active [] ()) : Bool := by
  classical
  exact decide (Matches locals active candidate.assignment (instantiate candidate.assignment pattern) row)

noncomputable def table : SymbolicPredicateTable.Table (Row locals active [] ()) Nat :=
  SymbolicPredicateTable.snapshot predicate (fun candidate => ContextualResidual.Models candidate.assignment information)
    rows before.present

theorem table_read : AskData information (table.query predicate) (fun occurrence => (occurrence, rows occurrence)) before.present := by
  intro Future future candidate solved
  exact SymbolicPredicateTable.snapshot_admitted predicate
    (fun candidate => ContextualResidual.Models candidate.assignment information) rows before.present
    ⟨Future, future, candidate⟩ solved

theorem table_matching {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment active declaration) (solved : ContextualResidual.Models candidate information) :
    table.matching predicate ⟨V, declaration, candidate⟩ = region locals candidate rows before.present pattern := by
  rw [table, SymbolicPredicateTable.snapshot_matching predicate
    (fun candidate => ContextualResidual.Models candidate.assignment information) rows before.present
    ⟨V, declaration, candidate⟩ solved]
  ext occurrence
  simp only [mem_regionOf, mem_region, predicate, decide_eq_true_eq]

def changedRows (occurrence : Nat) : Row locals active [] () :=
  if occurrence = 0 then ofStored locals active (.shared (literal 1)) else rows occurrence

/-- Keeping the occurrence identities while changing a relevant row does
not validate the old table. -/
theorem changed_payload_is_refused :
    ¬ AskData information (table.query predicate) (fun occurrence => (occurrence, changedRows occurrence)) before.present := by
  classical
  intro observed
  have reconstructed := table.actual_region predicate ⟨Empty, locals, model locals (literal 0)⟩
    changedRows before.present (observed Empty locals (model locals (literal 0)) (constant_model locals))
  rw [table_matching locals _ (constant_model locals),
    region_at_literal locals (model locals (literal 0)) 0 (.inl rfl) rfl] at reconstructed
  have selected : (0 : Nat) ∈ regionOf (fun occurrence => (occurrence, changedRows occurrence)) before.present
      (fun value => predicate ⟨Empty, locals, model locals (literal 0)⟩ value.1 value.2) := by
    rw [reconstructed]
    exact Finset.mem_singleton_self _
  have matched := of_decide_eq_true (mem_regionOf.mp selected).2
  change Matches locals active (model locals (literal 0)) (literal 0)
    (ofStored locals active (.shared (literal 1))) at matched
  rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff] at matched
  have impossible : (0 : Nat) = 1 := Sum.inl.inj (Term.op.inj matched).1
  omega

def duplicateRows (occurrence : Nat) : Row locals active [] () :=
  if occurrence = 2 then ofStored locals active (.shared (literal 0)) else rows occurrence

/-- A second occurrence of the same value is a new match, even though
its payload duplicates the first. -/
theorem matching_duplicate_is_refused :
    ¬ AskData information (table.query predicate) (fun occurrence => (occurrence, duplicateRows occurrence))
      (insert 2 before.present) := by
  classical
  intro observed
  have reconstructed := table.actual_region predicate ⟨Empty, locals, model locals (literal 0)⟩
    duplicateRows (insert 2 before.present) (observed Empty locals (model locals (literal 0)) (constant_model locals))
  rw [table_matching locals _ (constant_model locals),
    region_at_literal locals (model locals (literal 0)) 0 (.inl rfl) rfl] at reconstructed
  have selected : (2 : Nat) ∈ regionOf (fun occurrence => (occurrence, duplicateRows occurrence)) (insert 2 before.present)
      (fun value => predicate ⟨Empty, locals, model locals (literal 0)⟩ value.1 value.2) := by
    apply mem_regionOf.mpr
    refine ⟨Finset.mem_insert_self _ _, ?_⟩
    apply decide_eq_true
    change Matches locals active (model locals (literal 0)) (literal 0)
      (ofStored locals active (.shared (literal 0)))
    rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
    rfl
  rw [reconstructed] at selected
  have impossible : (2 : Nat) = 0 := Finset.mem_singleton.mp selected
  omega

/-- Actual finite-budget execution retains the nonprincipal equation and
publishes the value. The table is validated at that same information cut. -/
theorem an_actual_firing_with_residual_count (fuel : Nat) :
    ∃ observed : WithQueries locals before,
      observed.firing.rule = rule ∧ observed.firing.selection = picked ∧ observed.firing.outputs = outputs ∧
        observed.firing.reusable = (fun _ => true) ∧ observed.firing.fuel = fuel ∧
        observed.firing.update.remaining ≠ [] ∧ observed.firing.target.present = {0, 1, 2} ∧
        observed.queries = [table.query predicate] := by
  obtain ⟨firing, sourceRule, selection, values, reusable, budget⟩ :=
    ContextualConditionalExecution.realize_at_fuel locals before rule picked outputs (fun _ => true) admitted fuel
  have queried : AskData
      (ContextualConditionalExecution.information locals functions ∅ firing.selection firing.rule before.rows problem)
      (table.query predicate) (nativeLabels locals before) before.present := by
    rw [sourceRule, selection]
    exact table_read
  let observed : WithQueries locals before :=
    ⟨firing, [table.query predicate], fun query member => (List.mem_singleton.mp member) ▸ queried⟩
  refine ⟨observed, sourceRule, selection, values, reusable, budget, ?_, ?_, rfl⟩
  · have equality : information = ContextualConditionalExecution.information locals functions ∅
        firing.selection firing.rule before.rows problem := by rw [sourceRule, selection]; rfl
    have residual (actual : ContextualResidual.Problem active) (same : actual = information)
        (update : ContextualFrameUpdate.Update actual) : update.remaining ≠ [] := by
      subst actual
      exact no_completed_update update
    exact residual _ equality.symm firing.update
  · rw [firing.physical_result, selection]
    decide +kernel

theorem the_actual_output_denotes_seven (firing : ContextualConditionalExecution.Firing locals before)
    (sourceRule : firing.rule = rule) (selection : firing.selection = picked)
    (values : firing.outputs = outputs) (reusable : firing.reusable = (fun _ => true))
    {V : Type} (declaration : V → MetaArity base) (candidate : Assignment firing.target.declarations declaration) :
    Matches (ContextualPublication.privateFamily locals firing.update.declaration) firing.target.declarations
      candidate (literal 7) (firing.target.rows 2) := by
  apply (firing.ordinary_matches_source 2 (by rw [selection]; exact List.mem_singleton_self _)
    (by rw [reusable]) declaration candidate (literal 7)).mpr
  refine ⟨ContextualGuardMatching.Extension.identity declaration, model declaration (literal 0), ?_, ?_⟩
  · rw [sourceRule, selection]
    exact constant_model declaration
  · rw [values]
    rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNonprincipalCountControls
