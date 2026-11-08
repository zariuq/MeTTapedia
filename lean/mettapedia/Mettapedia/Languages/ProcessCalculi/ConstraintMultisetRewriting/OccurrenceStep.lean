import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationStore
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits

/-!
# Occurrence steps with a shared equation store

A rule instance contributes equations between both sides of every selected
take and read, together with its explicit tells. The equations refine the
shared store, so bindings affect surviving frame occurrences as well as new
outputs. Occurrence labels remain immutable syntax; observing them means
interpreting them in a solution of the shared store.

This file defines the atomic operation on already freshened rule instances.
It does not implement rule-schema freshening, a higher-order solver, or a
native engine. Reads may share an occurrence; consumption may not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO

inductive Check (T : Type uT) where
  | equal (left right : T)
  | absent (pattern : T)
  | count (pattern : T) (number : Nat)

namespace Check

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def pattern : Check T → T
  | .equal left _ => left
  | .absent p | .count p _ => p

def map {U : Type*} (f : T → U) : Check T → Check U
  | .equal left right => .equal (f left) (f right)
  | .absent p => .absent (f p)
  | .count p n => .count (f p) n

noncomputable def «matches» (A : SubstitutionAction T S) (σ : S)
    (label : O → T) (store : Finset O) (pattern : T) : Finset O := by
  classical
  exact store.filter fun o => A.E (A.apply σ pattern) (A.apply σ (label o))

def Holds (A : SubstitutionAction T S) (σ : S) (label : O → T)
    (store : Finset O) : Check T → Prop
  | .equal left right => A.Solves σ (left, right)
  | .absent pattern => ∀ o ∈ store,
      ¬ A.E (A.apply σ pattern) (A.apply σ (label o))
  | .count pattern number => («matches» A σ label store pattern).card = number

end Check

/-- A rule instance whose schematic locals have already been made fresh.
Shared logic variables remain shared across the whole configuration. -/
structure RuleInstance (T : Type uT) where
  take : List T
  read : List T
  tell : EquationStore T
  checks : List (Check T)
  produce : List T

/-- Rename every term-bearing position together, including checks and tells. -/
def RuleInstance.map {T : Type uT} {U : Type*} (f : T → U) (rule : RuleInstance T) :
    RuleInstance U where
  take := rule.take.map f
  read := rule.read.map f
  tell := rule.tell.map fun pair => (f pair.1, f pair.2)
  checks := rule.checks.map (Check.map f)
  produce := rule.produce.map f

structure Configuration (T : Type uT) (O : Type uO) where
  equations : EquationStore T
  present : Finset O

/-- Inspectable choices of occurrences, in pattern order. -/
structure Selection (O : Type uO) where
  taken : List O
  read : List O
  made : List O

namespace Selection

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def commit (selection : Selection O) : Commit O T :=
  ⟨selection.taken.toFinset, selection.read.toFinset, selection.made.toFinset, []⟩

def equations (label : O → T) (patterns : List T) (selected : List O) : EquationStore T :=
  patterns.zipWith (fun pattern o => (pattern, label o)) selected

def problem (selection : Selection O) (label : O → T)
    (rule : RuleInstance T) (before : Configuration T O) : EquationStore T :=
  before.equations ++ equations label rule.take selection.taken ++
    equations label rule.read selection.read ++ rule.tell

def result (selection : Selection O) (label : O → T)
    (rule : RuleInstance T) (before : Configuration T O) : Configuration T O :=
  ⟨selection.problem label rule before, fire before.present (selection.commit (T := T))⟩

structure Valid (A : SubstitutionAction T S) (selection : Selection O)
    (label : O → T) (rule : RuleInstance T) (before : Configuration T O) : Prop where
  take_distinct : selection.taken.Nodup
  output_distinct : selection.made.Nodup
  take_length : rule.take.length = selection.taken.length
  read_length : rule.read.length = selection.read.length
  outputs : selection.made.map label = rule.produce
  occurrences : Enabled label before.present selection.commit
  consistent : A.Consistent (selection.problem label rule before)
  checks : ∀ check ∈ rule.checks,
    A.Entails (selection.problem label rule before)
      (fun σ => check.Holds A σ label before.present)

omit [DecidableEq O] in
theorem models_equations_iff (A : SubstitutionAction T S) (σ : S)
    (label : O → T) {patterns : List T} {selected : List O}
    (lengths : patterns.length = selected.length) :
    A.Models σ (equations label patterns selected) ↔
      List.Forall₂ (fun p o => A.E (A.apply σ p) (A.apply σ (label o))) patterns selected := by
  induction patterns generalizing selected with
  | nil =>
    have empty : selected = [] := List.length_eq_zero_iff.mp lengths.symm
    subst selected
    simp [equations]
  | cons pattern rest ih =>
    cases selected with
    | nil => simp at lengths
    | cons o others =>
      have lengths' : rest.length = others.length := Nat.succ.inj lengths
      simpa only [equations, List.zipWith_cons_cons,
        SubstitutionAction.models_cons, List.forall₂_cons, SubstitutionAction.Solves] using
        and_congr_right (fun _ => ih lengths')

theorem models_problem (A : SubstitutionAction T S) {σ : S}
    {selection : Selection O} {label : O → T} {rule : RuleInstance T}
    {before : Configuration T O} (valid : selection.Valid A label rule before)
    (solved : A.Models σ (selection.problem label rule before)) :
    A.Models σ before.equations ∧
      List.Forall₂ (fun p o => A.E (A.apply σ p) (A.apply σ (label o)))
        rule.take selection.taken ∧
      List.Forall₂ (fun p o => A.E (A.apply σ p) (A.apply σ (label o)))
        rule.read selection.read ∧ A.Models σ rule.tell := by
  have split := solved
  simp only [problem, SubstitutionAction.models_append] at split
  exact ⟨split.1.1.1,
    (models_equations_iff A σ label valid.take_length).mp split.1.1.2,
    (models_equations_iff A σ label valid.read_length).mp split.1.2, split.2⟩

theorem Valid.refines {A : SubstitutionAction T S} {selection : Selection O}
    {label : O → T} {rule : RuleInstance T} {before : Configuration T O}
    (valid : selection.Valid A label rule before) :
    A.Refines (selection.result label rule before).equations before.equations :=
  fun _ solved => (models_problem A valid solved).1

theorem Valid.kept_survive {A : SubstitutionAction T S} {selection : Selection O}
    {label : O → T} {rule : RuleInstance T} {before : Configuration T O}
    (valid : selection.Valid A label rule before) {o : O} (read : o ∈ selection.read) :
    o ∈ (selection.result label rule before).present :=
  kept_subset_fire valid.occurrences (by simpa [commit] using read)

theorem Valid.consumed_removed {A : SubstitutionAction T S} {selection : Selection O}
    {label : O → T} {rule : RuleInstance T} {before : Configuration T O}
    (valid : selection.Valid A label rule before) {o : O} (taken : o ∈ selection.taken) :
    o ∉ (selection.result label rule before).present := by
  have old : o ∈ before.present := valid.occurrences.taken_subset (by simpa [commit] using taken)
  have notMade : o ∉ selection.commit.made := fun made =>
    Finset.disjoint_left.mp valid.occurrences.fresh made old
  simp only [result, fire, Finset.mem_union, Finset.mem_sdiff, not_or]
  exact ⟨fun member => member.2 (by simpa [commit] using taken), notMade⟩

/-- The old one-sided equation is recovered when the selected value is fixed
by the solution. Groundness is a sufficient condition in applicable profiles. -/
theorem solves_iff_matching_of_fixed (A : SubstitutionAction T S) (σ : S)
    (pattern value : T) (fixed : A.apply σ value = value) :
    A.Solves σ (pattern, value) ↔ A.E (A.apply σ pattern) value := by
  simp only [SubstitutionAction.Solves, fixed]

end Selection

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- One atomic rule instance. It may refine shared logic variables through
the equation store; no separate proof evaluator is involved. -/
def Step (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (before after : Configuration T O) : Prop :=
  ∃ selection : Selection O, selection.Valid A label rule before ∧
    after = selection.result label rule before

theorem Step.refines {A : SubstitutionAction T S} {label : O → T}
    {rule : RuleInstance T} {before after : Configuration T O}
    (step : Step A label rule before after) : A.Refines after.equations before.equations := by
  obtain ⟨selection, valid, rfl⟩ := step
  exact valid.refines

theorem Step.consistent {A : SubstitutionAction T S} {label : O → T}
    {rule : RuleInstance T} {before after : Configuration T O}
    (step : Step A label rule before after) : A.Consistent after.equations := by
  obtain ⟨selection, valid, rfl⟩ := step
  exact valid.consistent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
