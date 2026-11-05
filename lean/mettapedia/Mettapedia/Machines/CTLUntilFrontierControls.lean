import Mettapedia.Machines.CTLUntilFrontier

/-! EU support, quiet-round counting and the missing-frontier negative. -/

set_option autoImplicit false

namespace Mettapedia.Machines.CTLUntilFrontier.Controls

open Mettapedia.Logic
open RecursiveInsert

def edges : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 2)}
def holds : Finset (Fin 5) := {0, 1, 3}
def goal : Finset (Fin 5) := {2}
def expected : SemiNaive.State (Fin 5) := ⟨{0, 1, 2}, ∅⟩

theorem source_style_counter_includes_quiet_round :
    run edges holds 6 0 ⟨goal, goal⟩ = some (expected, 3) := by
  have first : advance edges holds ⟨goal, goal⟩ = ⟨{1, 2}, {1}⟩ := by
    apply SemiNaive.State.ext <;> decide +kernel
  have second : advance edges holds ⟨{1, 2}, {1}⟩ = ⟨{0, 1, 2}, {0}⟩ := by
    apply SemiNaive.State.ext <;> decide +kernel
  have last : advance edges holds ⟨{0, 1, 2}, {0}⟩ = expected := by
    apply SemiNaive.State.ext <;> decide +kernel
  simp only [run, first, second, last, expected, Finset.singleton_ne_empty, ↓reduceIte]

theorem final_support_has_path_meaning (state : Fin 5) :
    state ∈ expected.known ↔ CTLFixedPoints.Until (Relation edges) ↑holds ↑goal state :=
  run_until edges holds goal 6 expected 3 source_style_counter_includes_quiet_round state

theorem empty_seed_still_runs_a_quiet_round :
    run edges holds 1 0 ⟨∅, ∅⟩ = some (⟨∅, ∅⟩, 1) := by decide +kernel

theorem final_set_does_not_erase_counter :
    (some (expected, 3) : Option (SemiNaive.State (Fin 5) × Nat)) ≠ some (expected, 2) := by decide +kernel

theorem two_paths_make_one_fresh_state :
    progress ({(0, 1), (0, 2)} : Finset (Fin 3 × Fin 3)) {0} ⟨{1, 2}, {1, 2}⟩ = 1 := by decide +kernel

def missingFrontier : SemiNaive.State (Fin 5) := ⟨goal, ∅⟩

theorem empty_frontier_alone_is_not_completion :
    progress edges holds missingFrontier = 0 ∧ (1 : Fin 5) ∉ missingFrontier.known ∧
      CTLFixedPoints.Until (Relation edges) ↑holds ↑goal (1 : Fin 5) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact .advance (next := (2 : Fin 5)) (by decide)
    (by change ((1 : Fin 5), 2) ∈ edges; decide) (.reached (by decide))

theorem missing_frontier_breaks_the_required_invariant :
    ¬SemiNaive.Invariant (rules edges holds) missingFrontier := by
  intro valid
  have obligation := valid.old_complete (rule ((1 : Fin 5), 2)) (by decide +kernel) (by decide +kernel)
  rcases obligation with hot | known
  · simp [SemiNaive.hot, missingFrontier, rule] at hot
  · exact (by decide : (1 : Fin 5) ∉ goal) known

theorem changed_graph_changes_the_answer :
    run (insert ((3 : Fin 5), 2) edges) holds 6 0 ⟨goal, goal⟩ =
      some (⟨{0, 1, 2, 3}, ∅⟩, 3) ∧ (3 : Fin 5) ∉ expected.known := by
  have first : advance (insert ((3 : Fin 5), 2) edges) holds ⟨goal, goal⟩ = ⟨{1, 2, 3}, {1, 3}⟩ := by
    apply SemiNaive.State.ext <;> decide +kernel
  have second : advance (insert ((3 : Fin 5), 2) edges) holds ⟨{1, 2, 3}, {1, 3}⟩ = ⟨{0, 1, 2, 3}, {0}⟩ := by
    apply SemiNaive.State.ext <;> decide +kernel
  have last : advance (insert ((3 : Fin 5), 2) edges) holds ⟨{0, 1, 2, 3}, {0}⟩ = ⟨{0, 1, 2, 3}, ∅⟩ := by
    apply SemiNaive.State.ext <;> decide +kernel
  refine ⟨?_, by decide +kernel⟩
  simp only [run, first, second, last, Finset.insert_ne_empty, Finset.singleton_ne_empty, ↓reduceIte]

end Mettapedia.Machines.CTLUntilFrontier.Controls
