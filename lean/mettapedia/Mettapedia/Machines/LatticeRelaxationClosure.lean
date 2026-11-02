import Mettapedia.Machines.ShortestPathWorklist
import Mettapedia.GSLT.OpenEnded.ChaoticIteration

/-!
# Shortest-path improvement as the existing least-closure construction

Numerically smaller distances carry more information. Reversing their order
places edge relaxation in the existing complete-lattice chaotic-iteration
theory. Its least closure is proved equal to the independent path infimum,
using the completed worklist and the path-bound theorem, not by definition.

Fair schedules therefore agree on final distances. This does not equate their
productive-event traces, propagation counts, budgets or source round counters.
The executable finite worklist also handles an empty edge inventory, where
there is no infinite edge-valued schedule to instantiate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.WeightedRelaxation.Lattice

open Mettapedia.GSLT.OpenEnded

variable {Vertex : Type} [DecidableEq Vertex]

abbrev Knowledge (Vertex : Type) := OrderDual (Labels Vertex)

def contribution (edge : Arc Vertex) : Knowledge Vertex →o Knowledge Vertex where
  toFun labels vertex := if vertex = edge.target then proposal labels edge else ⊤
  monotone' := by
    intro first second ordered vertex
    by_cases atTarget : vertex = edge.target
    · simp only [if_pos atTarget]
      exact add_le_add (ordered edge.source) le_rfl
    · simp only [if_neg atTarget]
      exact le_rfl

theorem contribution_closed_iff (edge : Arc Vertex) (labels : Labels Vertex) :
    contribution edge (labels : Knowledge Vertex) ≤ (labels : Knowledge Vertex) ↔
      labels edge.target ≤ proposal labels edge := by
  change (∀ vertex, labels vertex ≤ if vertex = edge.target then proposal labels edge else ⊤) ↔ _
  constructor
  · intro closed
    simpa using closed edge.target
  · intro closed vertex
    by_cases atTarget : vertex = edge.target
    · subst vertex; simpa using closed
    · simp [atTarget]

theorem accumulate_eq_relax (edge : Arc Vertex) (labels : Labels Vertex) :
    ((labels : Knowledge Vertex) ⊔ contribution edge labels : Knowledge Vertex) = relax labels edge := by
  funext vertex
  change min (labels vertex) (if vertex = edge.target then proposal labels edge else ⊤) = relax labels edge vertex
  by_cases atTarget : vertex = edge.target
  · subst vertex; simp
  · simp [atTarget, relax_other labels edge vertex atTarget]

abbrev Edge (graph : List (Arc Vertex)) := {edge : Arc Vertex // edge ∈ graph}

noncomputable def target (graph : List (Arc Vertex)) (root : Vertex) : Labels Vertex :=
  ChaoticIteration.target (L := Knowledge Vertex) (fun edge : Edge graph => contribution edge.1) (initial root)

theorem distance_closed [Finite Vertex] (graph : List (Arc Vertex)) (root : Vertex) :
    Closed graph (distance graph root) := by
  obtain ⟨fuel, empty, exactLabels⟩ := Worklist.finite_shortest_paths graph root Worklist.fifo Worklist.fifo_keeps
  have valid := Worklist.slice_valid graph root Worklist.fifo Worklist.fifo_keeps fuel _ (Worklist.initial_valid graph root)
  have closed := Worklist.quiescent_closed graph root _ valid empty
  simpa only [exactLabels] using closed

theorem distance_below_initial [Finite Vertex] (graph : List (Arc Vertex)) (root : Vertex) :
    distance graph root ≤ initial root := by
  obtain ⟨fuel, _, exactLabels⟩ := Worklist.finite_shortest_paths graph root Worklist.fifo Worklist.fifo_keeps
  have valid := Worklist.slice_valid graph root Worklist.fifo Worklist.fifo_keeps fuel _ (Worklist.initial_valid graph root)
  simpa only [exactLabels] using valid.below

theorem distance_isGreatest [Finite Vertex] (graph : List (Arc Vertex)) (root : Vertex) :
    IsGreatest {labels : Labels Vertex | labels ≤ initial root ∧ Closed graph labels} (distance graph root) :=
  ⟨⟨distance_below_initial graph root, distance_closed graph root⟩,
    fun _ feasible => closed_le_distance graph root _ feasible.1 feasible.2⟩

/-- The order reversal is substantive: numerically this is the greatest
feasible potential, not a least numeric distance assignment satisfying inequalities. -/
theorem target_eq_distance [Finite Vertex] (graph : List (Arc Vertex)) (root : Vertex) :
    target graph root = distance graph root := by
  have least := ChaoticIteration.isLeast_target (L := Knowledge Vertex)
    (fun edge : Edge graph => contribution edge.1) (initial root)
  have below : target graph root ≤ initial root := least.1.1
  have closed : Closed graph (target graph root) := by
    intro edge member
    exact (contribution_closed_iff edge _).1 (least.1.2 ⟨edge, member⟩)
  apply le_antisymm (closed_le_distance graph root _ below closed)
  apply least.2
  constructor
  · exact distance_below_initial graph root
  · intro edge
    exact (contribution_closed_iff edge.1 _).2 (distance_closed graph root edge.1 edge.2)

def scheduled (graph : List (Arc Vertex)) (root : Vertex) (schedule : Nat → Edge graph) : Nat → Labels Vertex
  | 0 => initial root
  | n + 1 => relax (scheduled graph root schedule n) (schedule n).1

theorem scheduled_eq_chaotic (graph : List (Arc Vertex)) (root : Vertex) (schedule : Nat → Edge graph) (n : Nat) :
    scheduled graph root schedule n =
      ChaoticIteration.run (L := Knowledge Vertex) (fun edge : Edge graph => contribution edge.1) (initial root) schedule n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [scheduled, ChaoticIteration.run, ih]
      exact (accumulate_eq_relax (schedule n).1 _).symm

theorem fair_schedule_reaches_distance [Finite Vertex] (graph : List (Arc Vertex)) (root : Vertex)
    (schedule : Nat → Edge graph) (fair : ChaoticIteration.Fair schedule) :
    ∃ N, ∀ n, N ≤ n → scheduled graph root schedule n = distance graph root := by
  obtain ⟨N, reached⟩ := ChaoticIteration.run_eventually_eq_target (L := Knowledge Vertex)
    (fun edge : Edge graph => contribution edge.1) (initial root) fair
  refine ⟨N, fun n later => ?_⟩
  rw [scheduled_eq_chaotic, reached n later]
  exact target_eq_distance graph root

end Mettapedia.Machines.WeightedRelaxation.Lattice
