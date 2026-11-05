import Mettapedia.Machines.CTLUntilCandidateBag

/-! Ordered duplicate producers, preserved seed occurrences and quiet rounds. -/

set_option autoImplicit false

namespace Mettapedia.Machines.CTLUntilCandidateBag.Controls

def edges : List (Nat × Nat) := [(0, 1), (0, 1)]
def holds : List Nat := [0, 0]
def initial : State Nat := ⟨[1, 1], [1, 1]⟩

theorem eight_producers_one_new_vertex :
    candidates edges holds initial.delta = List.replicate 8 0 ∧
      (advance edges holds initial).delta = [0] ∧
      (advance edges holds initial).known = [1, 1, 0] := by decide +kernel

theorem old_presence_suppresses_every_producer :
    (advance edges holds ⟨[1, 1, 0], [1, 1]⟩).delta = [] := by decide +kernel

theorem producer_count_is_not_progress :
    (candidates edges holds initial.delta).length ≠ (advance edges holds initial).delta.length := by decide +kernel

theorem producer_order_controls_insertion_order :
    (advance [(0, 2), (1, 2)] [0, 1] (⟨[2], [2]⟩ : State Nat)).delta = [0, 1] ∧
      (advance [(1, 2), (0, 2)] [0, 1] (⟨[2], [2]⟩ : State Nat)).delta = [1, 0] := by decide +kernel

theorem two_round_run_keeps_seed_duplicates :
    (run edges holds 3 0 initial).map (fun result => (result.1.known, result.1.delta, result.2)) =
      some ([1, 1, 0], [], 2) := by decide +kernel

theorem empty_goal_has_a_quiet_round :
    (run edges holds 1 0 ⟨[], []⟩).map (fun result => (result.1.known, result.1.delta, result.2)) =
      some ([], [], 1) := by decide +kernel

theorem no_fuel_does_not_certify_completion : run edges holds 0 0 initial = none := rfl

theorem split_chunks_keep_first_occurrences_and_old_duplicates :
    fresh ([2, 1, 2] ++ [2, 3, 1, 4, 3]) ({1} : Finset Nat) = [2, 3, 4] ∧
      fresh [2, 3, 1, 4, 3] ([1, 1] ++ fresh [2, 1, 2] ({1} : Finset Nat)).toFinset = [3, 4] ∧
      [1, 1] ++ fresh ([2, 1, 2] ++ [2, 3, 1, 4, 3]) ({1} : Finset Nat) = [1, 1, 2, 3, 4] := by
  decide +kernel

theorem stale_known_suffix_republishes_an_old_prefix_candidate :
    fresh ([2, 2] ++ [2, 3]) ({1} : Finset Nat) ≠
      fresh [2, 2] ({1} : Finset Nat) ++ fresh [2, 3] ({1} : Finset Nat) := by
  decide +kernel

#print axioms known_union_fresh
#print axioms fresh_append
#print axioms fresh_append_known
#print axioms advance_support
#print axioms run_support
#print axioms finite_completion

end Mettapedia.Machines.CTLUntilCandidateBag.Controls
