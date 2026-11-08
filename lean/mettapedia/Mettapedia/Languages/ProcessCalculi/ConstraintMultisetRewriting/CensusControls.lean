import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison

/-! # Complete batches, retained constraints and stale-census controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MetaMeTTaComparison (atomAction)

def one : Atom := .symbol "1"
def two : Atom := .symbol "2"
def x : Atom := .var "x"
def y : Atom := .var "y"
def p (value : Atom) : Atom := Insertion.wrap "p" value
def r (value : Atom) : Atom := Insertion.wrap "r" value
def f (value : Atom) : Atom := Insertion.wrap "f" value

def label : Nat → Atom
  | 0 | 1 => p one
  | 2 => p two
  | 3 | 4 => r one
  | 5 => r two
  | 6 | 7 => p (.symbol "3")
  | _ => .symbol "unrelated"

def isP : Atom → Bool
  | .expression [.symbol "p", _] => true
  | _ => false

def query : PredicateQuery Nat Atom := ⟨isP, {0, 1, 2}⟩
def before : Configuration Atom Nat := ⟨[(x, f y)], {0, 1, 2}⟩
def tells : EquationStore Atom := [(y, one)]
def batch : Commit Nat Atom := ⟨∅, {0, 1, 2}, {3, 4, 5}, [query]⟩

def solution : Subst := fun name =>
  if name = "x" then some (f one) else if name = "y" then some one else none

theorem constraints_consistent : atomAction.Consistent (before.equations ++ tells) := by
  refine ⟨solution, ?_⟩
  intro equation member
  change equation ∈ [(x, f y), (y, one)] at member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · obtain rfl := List.mem_singleton.mp member
    rfl

theorem batch_enabled : Enabled label before.present batch := by decide +kernel

/-- The complete batch retains a genuine two-way constraint, rather than
solving the census in an empty or ground-only equation store. -/
theorem complete_batch_is_admitted :
    PredicateQueryAdmission.Valid atomAction label (CensusSourceCompilation.rule label batch tells)
      (batch.queries.map PredicateQueryAdmission.Query.fixed) before (CensusSourceCompilation.selection batch) :=
  CensusSourceCompilation.realize_commit atomAction label batch tells before batch_enabled constraints_consistent

theorem duplicate_answers_are_retained : labels label batch.made = {r one, r one, r two} := by
  decide +kernel

theorem joint_equations_are_retained (candidate : Subst) :
    atomAction.Models candidate
      ((CensusSourceCompilation.selection batch).result label
        (CensusSourceCompilation.rule label batch tells) before).equations ↔
      atomAction.Models candidate [(x, f y), (y, one)] :=
  CensusSourceCompilation.models_problem_iff atomAction candidate label batch tells before

def withMissedRow : Configuration Atom Nat := ⟨before.equations, insert 7 before.present⟩
def withoutCensus : Commit Nat Atom := { batch with queries := [] }

/-- A missed row leaves the five-port update available, but invalidates its
claim that every answer was observed. -/
theorem missed_row_separates_admissions :
    (CensusSourceCompilation.selection batch).Valid atomAction label
        (CensusSourceCompilation.rule label batch tells) withMissedRow ∧
      ¬ PredicateQueryAdmission.Valid atomAction label (CensusSourceCompilation.rule label batch tells)
        (batch.queries.map PredicateQueryAdmission.Query.fixed) withMissedRow (CensusSourceCompilation.selection batch) := by
  constructor
  · exact (CensusSourceCompilation.realize_commit atomAction label withoutCensus tells withMissedRow
      (by decide +kernel) constraints_consistent).firing
  · intro valid
    have holds := ((PredicateQueryAdmission.valid_fixed_iff _ _ _ batch.queries _ _).mp valid).2 query
      (List.mem_singleton_self query)
    exact (by decide +kernel : ¬ query.Holds label withMissedRow.present) holds

def withUnrelatedRow : Configuration Atom Nat := ⟨before.equations, insert 8 before.present⟩

theorem unrelated_arrival_preserves_admission :
    PredicateQueryAdmission.Valid atomAction label (CensusSourceCompilation.rule label batch tells)
      (batch.queries.map PredicateQueryAdmission.Query.fixed) withUnrelatedRow (CensusSourceCompilation.selection batch) :=
  CensusSourceCompilation.realize_commit atomAction label batch tells withUnrelatedRow
    (by decide +kernel) constraints_consistent

def selfJoin : Commit Nat Atom := ⟨∅, {0, 1, 2}, {6}, [query]⟩

/-- A new matching row is produced at commit. It was not an input to the
same complete source observation; checking that observation on the result
would incorrectly reject this legitimate self-join update. -/
theorem self_join_observes_the_original_cut :
    PredicateQueryAdmission.Valid atomAction label (CensusSourceCompilation.rule label selfJoin tells)
        (selfJoin.queries.map PredicateQueryAdmission.Query.fixed) before (CensusSourceCompilation.selection selfJoin) ∧
      ¬ query.Holds label (fire before.present selfJoin) := by
  exact ⟨CensusSourceCompilation.realize_commit atomAction label selfJoin tells before
    (by decide +kernel) constraints_consistent, by decide +kernel⟩

def bindingQuery (seen : Finset Nat) : PredicateQueryAdmission.Query Atom Subst Nat :=
  ⟨fun candidate value => decide (subst candidate (p x) = value), seen⟩

theorem at_one : (bindingQuery {0, 1}).Ask atomAction [(x, one)] label before.present := by
  intro candidate solved
  have fixes := solved (x, one) (List.mem_singleton_self _)
  change subst candidate x = one at fixes
  change regionOf label before.present (fun value => decide (subst candidate (p x) = value)) = {0, 1}
  simp only [p, Insertion.subst_wrap, fixes]
  decide +kernel

theorem at_two : (bindingQuery {2}).Ask atomAction [(x, two)] label before.present := by
  intro candidate solved
  have fixes := solved (x, two) (List.mem_singleton_self _)
  change subst candidate x = two at fixes
  change regionOf label before.present (fun value => decide (subst candidate (p x) = value)) = {2}
  simp only [p, Insertion.subst_wrap, fixes]
  decide +kernel

/-- Physical identities alone do not fix a query whose caller parameter is
still live. This census cannot be promoted across the missing binding cut. -/
theorem the_binding_cut_cannot_be_dropped :
    ¬ (bindingQuery {0, 1}).Ask atomAction [] label before.present := by
  intro asked
  have holds := asked (Insertion.single "x" two) (atomAction.models_nil _)
  have selected : regionOf label before.present
      ((bindingQuery {0, 1}).region (Insertion.single "x" two)) = {2} := by
    decide +kernel
  change regionOf label before.present ((bindingQuery {0, 1}).region (Insertion.single "x" two)) = {0, 1} at holds
  rw [selected] at holds
  exact (by decide : ({2} : Finset Nat) ≠ {0, 1}) holds

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusControls
