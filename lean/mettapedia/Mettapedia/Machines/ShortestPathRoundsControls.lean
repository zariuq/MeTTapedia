import Mettapedia.Machines.ShortestPathRounds
import Mettapedia.Machines.WeightedPathTransport
import Mettapedia.Tools.KernelReflexivity

/-! Productive rounds, exact frontiers and order-sensitive counters. -/

set_option autoImplicit false

namespace Mettapedia.Machines.WeightedRelaxation.Rounds.Controls

def graph : List (Arc (Fin 4)) := [⟨0, 1, 2⟩, ⟨0, 2, 9⟩, ⟨1, 2, 3⟩, ⟨2, 3, 1⟩]
def reordered : List (Arc (Fin 4)) := [⟨0, 2, 9⟩, ⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨2, 3, 1⟩]

theorem finite_graph_over_unbounded_names_terminates (edges : List (Arc Nat)) (root : Nat) :
    ∃ fuel rounds, run edges fuel (initial root) [root] 0 = some (distance edges root, rounds) :=
  finite_shortest_paths edges root

theorem untouched_names_are_not_copied_into_the_rank : targets ([⟨0, 2^64 + 1, 3⟩] : List (Arc Nat)) = {2^64 + 1} := by
  decide +kernel

def observe (result : Option (Labels (Fin 4) × Nat)) : Option (List (WithTop Nat) × Nat) :=
  result.map (fun value => (List.ofFn value.1, value.2))

theorem first_frontier_retains_order : (pass graph (initial 0) [0]).2 = [1, 2] := by decide +kernel

theorem reordered_graph_changes_frontier_order : (pass reordered (initial 0) [0]).2 = [2, 1] := by decide +kernel

theorem ordered_rounds : observe (run graph 3 (initial 0) [0] 0) = some ([0, 2, 5, 6], 2) := by decide +kernel

theorem reordered_rounds : observe (run reordered 4 (initial 0) [0] 0) = some ([0, 2, 5, 6], 3) := by decide +kernel

theorem same_final_distances_do_not_fix_round_count :
    observe (run graph 3 (initial 0) [0] 0) ≠ observe (run reordered 4 (initial 0) [0] 0) := by
  rw [ordered_rounds, reordered_rounds]
  decide

theorem two_rounds_are_not_completion : run graph 2 (initial 0) [0] 0 = none := by kernel_reflexivity

theorem zero_allowance_is_not_empty_frontier : run graph 0 (initial 0) [0] 0 = none := rfl

theorem seed_frontier_is_required : ¬ Valid graph (0 : Fin 4) (initial 0) [] := by
  intro valid
  have omitted := valid.covered ⟨0, 1, 2⟩ (by decide) (by decide)
  exact List.not_mem_nil omitted

theorem dropped_frontier_fabricates_early_completion :
    observe (run graph 1 (initial 0) [] 0) = some ([0, ⊤, ⊤, ⊤], 0) := by decide +kernel

def improvements : List (Arc (Fin 4)) := [⟨0, 1, 9⟩, ⟨0, 1, 2⟩, ⟨0, 2, 4⟩]

theorem improvement_events_keep_occurrences : (scan improvements (initial 0) []).2 = [1, 1, 2] := by decide +kernel

theorem only_next_frontier_deduplicates : (pass improvements (initial 0) [0]).2 = [1, 2] := by decide +kernel

def zeroCycle : List (Arc (Fin 4)) := [⟨0, 1, 0⟩, ⟨1, 0, 0⟩]

theorem zero_weight_cycle_terminates : observe (run zeroCycle 2 (initial 0) [0] 0) = some ([0, 0, ⊤, ⊤], 1) := by decide +kernel

theorem every_graph_has_a_completed_distance_result (edges : List (Arc (Fin 4))) :
    ∃ fuel rounds, run edges fuel (initial 0) [0] 0 = some (distance edges 0, rounds) :=
  finite_shortest_paths edges 0

theorem graph_order_preserves_all_final_distances (root : Fin 4) : distance graph root = distance reordered root :=
  distance_perm (by decide +kernel) root

def single : List (Arc (Fin 4)) := [⟨0, 1, 2⟩]
def doubled : List (Arc (Fin 4)) := [⟨0, 1, 2⟩, ⟨0, 1, 2⟩]

theorem duplicates_preserve_current_distances (root : Fin 4) : distance single root = distance doubled root :=
  distance_support_congr (fun edge => by simp [single, doubled]) root

/-- This continuation deletes one edge occurrence, unlike a remove-all row
primitive. Current distance equality is not sufficient for that observer. -/
theorem one_occurrence_deletion_distinguishes_distances :
    (observe (run (single.erase ⟨0, 1, 2⟩) 1 (initial 0) [0] 0)).map Prod.fst ≠
      (observe (run (doubled.erase ⟨0, 1, 2⟩) 2 (initial 0) [0] 0)).map Prod.fst := by decide +kernel

end Mettapedia.Machines.WeightedRelaxation.Rounds.Controls
