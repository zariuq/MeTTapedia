import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CoreControls

/-! # Complete observations commute with genuine shared two-way constraints -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusComposition.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls (signature A)
open Core.Controls
open GuardFreeProcessOrders

def isPersistent : Term signature → Bool
  | .const name => name == 9
  | _ => false

def completeRead : PredicateQuery Nat (Term signature) := ⟨isPersistent, {4}⟩
def observations : List (PredicateQueryAdmission.Query (Term signature) (Subst signature) Nat) :=
  [PredicateQueryAdmission.Query.fixed completeRead]

theorem first_census_ready : PredicateQueryAdmission.Valid A rows firstRule observations initial firstSelection := by
  exact (PredicateQueryAdmission.valid_fixed_iff _ _ _ [completeRead] _ _).mpr
    ⟨first_ready, fun query member => (List.mem_singleton.mp member) ▸ (by decide +kernel)⟩

theorem second_census_ready : PredicateQueryAdmission.Valid A rows secondRule observations initial secondSelection := by
  exact (PredicateQueryAdmission.valid_fixed_iff _ _ _ [completeRead] _ _).mpr
    ⟨second_ready, fun query member => (List.mem_singleton.mp member) ▸ (by decide +kernel)⟩

theorem census_ignores_first : ∀ query ∈ observations,
    query.IgnoresWrites A jointProblem rows firstSelection := by
  intro query member candidate _ occurrence written
  obtain rfl := List.mem_singleton.mp member
  have options : occurrence = 0 ∨ occurrence = 2 := by simpa [firstSelection] using written
  rcases options with rfl | rfl <;> rfl

theorem census_ignores_second : ∀ query ∈ observations,
    query.IgnoresWrites A jointProblem rows secondSelection := by
  intro query member candidate _ occurrence written
  obtain rfl := List.mem_singleton.mp member
  have options : occurrence = 1 ∨ occurrence = 3 := by simpa [secondSelection] using written
  rcases options with rfl | rfl <;> rfl

/-- The two events impose X = f(Y) and Y = 1, share a persistent occurrence,
and retain their original equality, absence and complete-region checks. -/
theorem complete_observations_survive_both_orders :
    PredicateQueryAdmission.Valid A rows secondRule observations (firstSelection.result rows firstRule initial) secondSelection ∧
      PredicateQueryAdmission.Valid A rows firstRule observations (secondSelection.result rows secondRule initial) firstSelection ∧
      SameUpTo A (secondSelection.result rows secondRule (firstSelection.result rows firstRule initial))
        (firstSelection.result rows firstRule (secondSelection.result rows secondRule initial)) :=
  CensusComposition.independently_ready_commute A rows first second initial observations observations
    first_census_ready second_census_ready resources_independent joint_consistent
    first_guards_ignore_second_writes second_guards_ignore_first_writes census_ignores_second census_ignores_first

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusComposition.Controls
