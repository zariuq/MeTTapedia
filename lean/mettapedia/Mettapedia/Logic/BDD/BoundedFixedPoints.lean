import Mettapedia.Logic.BDD.FixedPointSolver
import Mettapedia.Algebra.Order.FiniteSetIteration

/-!
# Total finite symbolic fixed points with an explicit iteration budget

At most `card State` strict set changes are possible, followed by one
stability check. The existing symbolic page engine therefore supplies a
completed least/greatest result at this budget. Extracting the diagram below
cannot interpret an unfinished page as a negative answer.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.BoundedFixedPoints

open StatePredicates FixedPointSolver
open Mettapedia.Algebra.Order.FixedPointIteration
open Mettapedia.Algebra.Order.FiniteSetIteration

def budget (n : Nat) : Nat := 2 ^ n + 1

theorem budget_eq_card (n : Nat) : budget n = Fintype.card (State n) + 1 := by simp [budget, State]

theorem least_finished {n : Nat} (operator : Operator n) :
    (advance operator (budget n) ⟨falsity n, 0⟩).finished = true := by
  rw [budget_eq_card]
  apply finishes_at_stable_walk operator (Fintype.card (State n))
  apply (equivalent_denote _ _).mpr
  rw [operator.refines, walk_denote]
  have seed : denote (falsity n) = (⊥ : Set (State n)) := by ext state; simp [denote, falsity, BDD.satSet]
  rw [seed, bottom_at_card_is_lfp, operator.meaning.map_lfp]

theorem greatest_finished {n : Nat} (operator : Operator n) :
    (advance operator (budget n) ⟨truth n, 0⟩).finished = true := by
  rw [budget_eq_card]
  apply finishes_at_stable_walk operator (Fintype.card (State n))
  apply (equivalent_denote _ _).mpr
  rw [operator.refines, walk_denote]
  have seed : denote (truth n) = (⊤ : Set (State n)) := by ext state; simp [denote, truth, BDD.satSet]
  rw [seed, top_at_card_is_gfp, operator.meaning.map_gfp]

def least {n : Nat} (operator : Operator n) : Diagram n :=
  (advance operator (budget n) ⟨falsity n, 0⟩).frame.current

def greatest {n : Nat} (operator : Operator n) : Diagram n :=
  (advance operator (budget n) ⟨truth n, 0⟩).frame.current

theorem least_denote {n : Nat} (operator : Operator n) : denote (least operator) = operator.meaning.lfp := by
  have done := least_finished operator
  cases completed : advance operator (budget n) ⟨falsity n, 0⟩ with
  | paused frame => simp [completed, Result.finished] at done
  | done frame =>
      simpa [least, completed, Result.frame] using completed_least operator (budget n) frame completed

theorem greatest_denote {n : Nat} (operator : Operator n) : denote (greatest operator) = operator.meaning.gfp := by
  have done := greatest_finished operator
  cases completed : advance operator (budget n) ⟨truth n, 0⟩ with
  | paused frame => simp [completed, Result.finished] at done
  | done frame =>
      simpa [greatest, completed, Result.frame] using completed_greatest operator (budget n) frame completed

theorem passes_bounds {n : Nat} (operator : Operator n) (fuel : Nat) (initial : Frame n) :
    initial.passes ≤ (advance operator fuel initial).frame.passes ∧
      (advance operator fuel initial).frame.passes ≤ initial.passes + fuel := by
  induction fuel generalizing initial with
  | zero => simp [advance, Result.frame]
  | succ fuel ih =>
      rw [advance]
      split
      · simp [Result.frame]
      · have rest := ih ⟨operator.step initial.current, initial.passes + 1⟩
        dsimp only at rest
        omega

theorem least_passes_bounded {n : Nat} (operator : Operator n) :
    (advance operator (budget n) ⟨falsity n, 0⟩).frame.passes ≤ 2 ^ n + 1 := by
  simpa [budget] using (passes_bounds operator (budget n) ⟨falsity n, 0⟩).2

theorem greatest_passes_bounded {n : Nat} (operator : Operator n) :
    (advance operator (budget n) ⟨truth n, 0⟩).frame.passes ≤ 2 ^ n + 1 := by
  simpa [budget] using (passes_bounds operator (budget n) ⟨truth n, 0⟩).2

end Mettapedia.Logic.BDDCore.BoundedFixedPoints
