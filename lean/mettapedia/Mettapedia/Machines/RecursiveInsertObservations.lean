import Mettapedia.Machines.SemiNaiveInsertSaturation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max

/-!
# What recursive insertion permits an observer to forget

Each insertion attempt records whether it was fresh or already present.
Local branch emissions are lists; answers from different calls concatenate.
This gives an exact count law, not an identification of arbitrary evaluator
return conventions with insertion events. Silent duplicate branches make
the fresh emission count independent of scheduling. General duplicate-call
counts, answer order, provenance and effects are not covered by that quotient.

Controls separate equal final sets from equal counts, local duplicate guards
from negative premises, and finite syntax from a finite ground universe.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RecursiveInsert

open Mettapedia.Logic
open scoped BigOperators

variable {Fact Answer : Type} [DecidableEq Fact]

def freshMass (weight : Fact → Nat) (events : List (Event Fact)) : Nat :=
  (events.map (fun event => match event with | .fresh fact => weight fact | .present _ => 0)).sum

def presentMass (weight : Fact → Nat) (events : List (Event Fact)) : Nat :=
  (events.map (fun event => match event with | .fresh _ => 0 | .present fact => weight fact)).sum

def answers (fresh present : Fact → List Answer) (events : List (Event Fact)) : List Answer :=
  events.reverse.flatMap (fun event => match event with
    | .fresh fact => fresh fact
    | .present fact => present fact)

omit [DecidableEq Fact] in
@[simp] theorem presentMass_zero (events : List (Event Fact)) : presentMass (fun _ => 0) events = 0 := by
  induction events with
  | nil => rfl
  | cons event events ih => cases event <;> simpa [presentMass] using ih

omit [DecidableEq Fact] in
theorem answers_length (fresh present : Fact → List Answer) (events : List (Event Fact)) :
    (answers fresh present events).length = freshMass (fun fact => (fresh fact).length) events +
      presentMass (fun fact => (present fact).length) events := by
  induction events with
  | nil => simp [answers, freshMass, presentMass]
  | cons event events ih =>
      cases event <;>
        simp [answers, freshMass, presentMass, List.flatMap_append, List.length_append,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at * <;> omega

def FreshBalanced (weight : Fact → Nat) (state : State Fact) : Prop :=
  freshMass weight state.log = ∑ fact ∈ state.known, weight fact

theorem initial_balanced (rules : List (LP.PropRule Fact)) (seeds : List Fact) (weight : Fact → Nat) :
    FreshBalanced weight (initial rules seeds) := by simp [FreshBalanced, initial, freshMass]

theorem handle_balanced (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (task : Task Fact) (rest : List (Task Fact)) (known : Finset Fact) (log : List (Event Fact))
    (weight : Fact → Nat) (balanced : FreshBalanced weight ⟨known, task :: rest, log⟩) :
    FreshBalanced weight (handle rules policy task rest known log) := by
  change freshMass weight log = ∑ fact ∈ known, weight fact at balanced
  cases task with
  | insert fact =>
      by_cases held : fact ∈ known <;>
        simp [FreshBalanced, handle, held, freshMass, Finset.sum_insert, ← balanced]
  | check rule =>
      by_cases enabled : rule.premises ⊆ known <;>
        simpa [FreshBalanced, handle, enabled] using balanced

theorem run_balanced (rules : List (LP.PropRule Fact)) (policy : QueuePolicy Fact)
    (fuel : Nat) (start finish : State Fact) (weight : Fact → Nat)
    (balanced : FreshBalanced weight start) (result : run rules policy fuel start = .done finish) :
    FreshBalanced weight finish := by
  induction fuel generalizing start with
  | zero =>
      by_cases empty : start.pending = []
      · have eq : start = finish := by simpa [run, empty] using result
        simpa [← eq] using balanced
      · simp [run, empty] at result
  | succ fuel ih =>
      cases hp : start.pending with
      | nil =>
          have eq : start = finish := by simpa [run, hp] using result
          simpa [← eq] using balanced
      | cons task rest =>
          have eq : start = ⟨start.known, task :: rest, start.log⟩ := by cases start; simp_all
          exact ih _ (handle_balanced rules policy task rest _ _ weight (eq ▸ balanced))
            (by simpa [run, hp] using result)

/-- Fresh emissions are a set fold; present emissions retain attempt multiplicity. -/
theorem completed_answer_count [Fintype Fact] (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (policy : QueuePolicy Fact) (fuel : Nat) (finish : State Fact)
    (result : run rules policy fuel (initial rules seeds) = .done finish)
    (fresh present : Fact → List Answer) :
    (answers fresh present finish.log).length =
      (∑ fact ∈ reference rules seeds, (fresh fact).length) +
        presentMass (fun fact => (present fact).length) finish.log := by
  rw [answers_length]
  have balanced := run_balanced rules policy fuel _ finish (fun fact => (fresh fact).length)
    (initial_balanced rules seeds (fun fact => (fresh fact).length)) result
  change freshMass _ finish.log = _ at balanced
  rw [balanced, completed_eq_reference rules seeds policy fuel finish result]

/-- This is a count-only quotient. The ordered answer lists can still differ. -/
theorem silent_present_count [Fintype Fact] (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (policy : QueuePolicy Fact) (fuel : Nat) (finish : State Fact)
    (result : run rules policy fuel (initial rules seeds) = .done finish)
    (fresh : Fact → List Answer) :
    (answers fresh (fun _ => []) finish.log).length =
      ∑ fact ∈ reference rules seeds, (fresh fact).length := by
  rw [completed_answer_count rules seeds policy fuel finish result]
  simp

theorem silent_present_schedules_agree [Fintype Fact]
    (rules : List (LP.PropRule Fact)) (seeds : List Fact)
    (first second : QueuePolicy Fact) (m n : Nat) (left right : State Fact)
    (hl : run rules first m (initial rules seeds) = .done left)
    (hr : run rules second n (initial rules seeds) = .done right)
    (fresh : Fact → List Answer) :
    (answers fresh (fun _ => []) left.log).length = (answers fresh (fun _ => []) right.log).length := by
  rw [silent_present_count rules seeds first m left hl,
    silent_present_count rules seeds second n right hr]

namespace Controls

def bothPremises : List (LP.PropRule (Fin 3)) := [⟨{0, 1}, 2⟩]

def countAttempts : Result (Fin 3) → Option Nat
  | .done state => some state.log.length
  | .paused _ => none

/-- The same positive program has different duplicate-attempt counts under DFS and FIFO. -/
theorem dfs_three_attempts : countAttempts (run bothPremises depthFirst 30
    (initial bothPremises [0, 1])) = some 3 := by decide

theorem fifo_four_attempts : countAttempts (run bothPremises fifo 30
    (initial bothPremises [0, 1])) = some 4 := by decide

theorem both_saturate :
    run bothPremises depthFirst 6 (initial bothPremises [0, 1]) =
      .done ⟨{0, 1, 2}, [], [.fresh 2, .fresh 1, .fresh 0]⟩ ∧
    run bothPremises fifo 6 (initial bothPremises [0, 1]) =
      .done ⟨{0, 1, 2}, [], [.present 2, .fresh 2, .fresh 1, .fresh 0]⟩ := by
  constructor <;> (apply congrArg Result.done; apply State.ext <;> decide)

def cyclic : List (LP.PropRule (Fin 3)) := [⟨∅, 0⟩, ⟨{0}, 1⟩, ⟨{1}, 0⟩]

theorem empty_rule_and_cycle_complete :
    run cyclic depthFirst 6 (initial cyclic []) =
      .done ⟨{0, 1}, [], [.present 0, .fresh 1, .fresh 0]⟩ := by
  apply congrArg Result.done
  apply State.ext <;> decide

theorem duplicate_seeds_not_erased :
    run ([] : List (LP.PropRule (Fin 3))) depthFirst 5 (initial [] [0, 0]) =
      .done ⟨{0}, [], [.present 0, .fresh 0]⟩ := by decide

theorem duplicate_rules_not_erased :
    countAttempts (run [⟨{0}, 1⟩, ⟨{0}, 1⟩] depthFirst 30
      (initial ([] : List (LP.PropRule (Fin 3))) [0])) = some 3 := by decide

theorem cutoff_is_not_quiescence :
    run bothPremises depthFirst 0 (initial bothPremises [0, 1]) =
      .paused (initial bothPremises [0, 1]) := by decide

/-- This negative guard reads another fact, not the insertion's own key. -/
def negativeInsert (blocked fact : Fin 2) (known : Finset (Fin 2)) : Finset (Fin 2) :=
  if blocked ∈ known then known else insert fact known

theorem negative_premises_order_dependent :
    negativeInsert 0 1 (negativeInsert 1 0 ∅) = {0} ∧
    negativeInsert 1 0 (negativeInsert 0 1 ∅) = {1} := by decide

def removeThenAdd (known : Finset (Fin 2)) : Finset (Fin 2) := insert 1 (known.erase 0)

def copyIfPresent (known : Finset (Fin 2)) : Finset (Fin 2) :=
  if 0 ∈ known then insert 1 known else known

theorem removal_breaks_insert_only_observation :
    copyIfPresent ({0} : Finset (Fin 2)) = {0, 1} ∧
    copyIfPresent (({0} : Finset (Fin 2)).erase 0) = ∅ := by decide

theorem removal_and_propagation_do_not_commute :
    (copyIfPresent ({0} : Finset (Fin 2))).erase 0 = {1} ∧
    copyIfPresent (({0} : Finset (Fin 2)).erase 0) = ∅ := by decide

def chronology : Result (Fin 3) → Option (List (Event (Fin 3)))
  | .done state => some state.log.reverse
  | .paused _ => none

theorem silent_duplicates_do_not_preserve_order :
    chronology (run [⟨{0}, 2⟩] depthFirst 10 (initial [] [0, 1])) =
      some [.fresh 0, .fresh 2, .fresh 1] ∧
    chronology (run [⟨{0}, 2⟩] fifo 10 (initial [] [0, 1])) =
      some [.fresh 0, .fresh 1, .fresh 2] := by decide

/-- One finite rule schema over naturals can keep producing fresh facts. -/
def successorRound (known : Finset Nat) : Finset Nat := known ∪ known.image Nat.succ

theorem no_finite_successor_fixpoint (known : Finset Nat) (nonempty : known.Nonempty) :
    successorRound known ≠ known := by
  intro fixed
  let largest := known.max' nonempty
  have hm : largest ∈ known := Finset.max'_mem known nonempty
  have hs : largest + 1 ∈ successorRound known :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨largest, hm, rfl⟩)
  rw [fixed] at hs
  have bound := Finset.le_max' known (largest + 1) hs
  change largest + 1 ≤ largest at bound
  omega

end Controls

end Mettapedia.Machines.RecursiveInsert
