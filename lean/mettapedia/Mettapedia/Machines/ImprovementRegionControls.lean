import Mettapedia.Machines.LatticeRelaxationClosure
import Mettapedia.Machines.RelaxationAdjacency
import Mettapedia.Machines.KeyedImprovementTransactions

/-!
# Controls delimiting the keyed-improvement region

These controls compare actual worklist runs, including pending duties,
productive-event occurrences and unreachable vertices. Deliberately broken
enqueue and non-strict guards exhibit premature quiescence and endless churn.
Negative weights, finite infinity sentinels, stale reads and changed graphs
remain outside the proved static nonnegative region.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.WeightedRelaxation.Controls

open Worklist

def graph : List (Arc (Fin 3)) := [⟨0, 1, 1⟩, ⟨0, 2, 10⟩, ⟨1, 2, 1⟩]
def depthFirst := MachineCore.runSlice (core graph dfs) 10 (initialState graph 0)
def breadthFirst := MachineCore.runSlice (core graph fifo) 10 (initialState graph 0)

theorem actual_distances_agree :
    depthFirst.1.pending = [] ∧ breadthFirst.1.pending = [] ∧
    depthFirst.1.labels 0 = 0 ∧ depthFirst.1.labels 1 = 1 ∧ depthFirst.1.labels 2 = 2 ∧
    breadthFirst.1.labels 0 = 0 ∧ breadthFirst.1.labels 1 = 1 ∧ breadthFirst.1.labels 2 = 2 := by decide

/-- A vertex improved through a worse path can be emitted before the better
path arrives. Set-valued final distances do not determine that occurrence. -/
theorem propagation_traces_differ :
    depthFirst.1.improvements.reverse = [(1, 1), (2, 2)] ∧
    breadthFirst.1.improvements.reverse = [(1, 1), (2, 10), (2, 2)] ∧
    depthFirst.1.improvements.length = 2 ∧ breadthFirst.1.improvements.length = 3 := by decide

theorem partial_prefix_is_not_quiescence :
    (MachineCore.runSlice (core graph dfs) 1 (initialState graph 0)).1.pending ≠ [] ∧
      (MachineCore.runSlice (core graph dfs) 1 (initialState graph 0)).1.labels 2 = ⊤ := by decide

theorem exact_resumption (first later : Nat) :
    MachineCore.runSlice (core graph dfs) (first + later) (initialState graph 0) =
      let earlier := MachineCore.runSlice (core graph dfs) first (initialState graph 0)
      let suffix := MachineCore.runSlice (core graph dfs) later earlier.1
      (suffix.1, earlier.2 + suffix.2) := MachineCore.runSlice_add _ _ _ _

def cyclic : List (Arc (Fin 3)) := [⟨0, 0, 0⟩, ⟨0, 1, 2⟩, ⟨1, 0, 0⟩]

theorem zero_cycle_terminates_and_preserves_infinity :
    (MachineCore.runSlice (core cyclic dfs) 20 (initialState cyclic 0)).1.pending = [] ∧
    (MachineCore.runSlice (core cyclic dfs) 20 (initialState cyclic 0)).1.labels 1 = 2 ∧
    (MachineCore.runSlice (core cyclic dfs) 20 (initialState cyclic 0)).1.labels 2 = ⊤ := by decide

theorem empty_graph_complete_without_any_step :
    (MachineCore.runSlice (core ([] : List (Arc (Fin 2))) dfs) 0 (initialState [] 0)).1.pending = [] ∧
    (MachineCore.runSlice (core ([] : List (Arc (Fin 2))) dfs) 0 (initialState [] 0)).1.labels 1 = ⊤ := by decide

def repeated : List (Arc (Fin 2)) := [⟨0, 1, 4⟩, ⟨0, 1, 4⟩]

theorem duplicate_edges_keep_duties_not_duplicate_improvements :
    (MachineCore.runSlice (core repeated dfs) 10 (initialState repeated 0)).2 = 2 ∧
    (MachineCore.runSlice (core repeated dfs) 10 (initialState repeated 0)).1.improvements = [(1, 4)] := by decide

def forgetChildren : Enqueue (Fin 3) := fun _ rest => rest
def chain : List (Arc (Fin 3)) := [⟨0, 1, 1⟩, ⟨1, 2, 1⟩]

theorem dropped_duty_fakes_quiescence :
    (MachineCore.runSlice (core chain forgetChildren) 10 (initialState chain 0)).1.pending = [] ∧
    (MachineCore.runSlice (core chain forgetChildren) 10 (initialState chain 0)).1.labels 2 = ⊤ ∧
    (MachineCore.runSlice (core chain dfs) 10 (initialState chain 0)).1.labels 2 = 2 := by decide

theorem dropping_children_is_not_admitted : ¬ Keeps forgetChildren := by
  intro claimed
  have missing := (claimed [⟨0, 1, 1⟩] [] ⟨0, 1, 1⟩).2 (Or.inl (by simp))
  simp [forgetChildren] at missing

theorem duplicate_pending_duties_may_merge :
    dedupFifo ([⟨0, 1, 1⟩] : List (Arc (Fin 3))) [⟨0, 1, 1⟩] = [⟨0, 1, 1⟩] := by decide

theorem deduplicating_queue_has_same_distances :
    (MachineCore.runSlice (core graph dedupFifo) 10 (initialState graph 0)).1.pending = [] ∧
    (MachineCore.runSlice (core graph dedupFifo) 10 (initialState graph 0)).1.labels 2 = 2 := by decide

/-- The faulty variant schedules work even when the stored distance does not
strictly improve. Its zero-weight self-loop never consumes its last duty. -/
def nonStrictStep (graph : List (Arc (Fin 1))) (state : State (Fin 1)) : State (Fin 1) :=
  match state.pending with
  | [] => state
  | edge :: rest =>
      if proposal state.labels edge ≤ state.labels edge.target then
        ⟨relax state.labels edge, outgoing graph edge.target ++ rest, state.improvements⟩
      else ⟨state.labels, rest, state.improvements⟩

def selfEdge : Arc (Fin 1) := ⟨0, 0, 0⟩
def loopState : State (Fin 1) := ⟨fun _ => 0, [selfEdge], []⟩

theorem nonStrict_self_loop_repeats : nonStrictStep [selfEdge] loopState = loopState := by
  simp [nonStrictStep, loopState, selfEdge, proposal, relax, KeyedImprovement.lower, outgoing]

theorem nonStrict_never_drains (n : Nat) :
    ((nonStrictStep [selfEdge])^[n] loopState).pending = [selfEdge] := by
  have fixed : Function.IsFixedPt (nonStrictStep [selfEdge]) loopState := nonStrict_self_loop_repeats
  exact congrArg State.pending (fixed.iterate n)

theorem negative_cycle_has_no_fixed_finite_distance :
    ¬ ∃ distance : Int, min distance (distance - 1) = distance := by
  rintro ⟨distance, fixed⟩
  rw [min_eq_right (by omega)] at fixed
  omega

def longEdge : List (Arc (Fin 2)) := [⟨0, 1, 2000⟩]

theorem finite_sentinel_loses_a_real_path :
    (MachineCore.runSlice (core longEdge dfs) 5 (initialState longEdge 0)).1.labels 1 = 2000 ∧
      min (1000 : Nat) (0 + 2000) = 1000 := by decide

theorem graph_deletion_invalidates_provenance :
    ¬ PathSound ([] : List (Arc (Fin 3))) 0 depthFirst.1.labels := by
  intro sound
  have held : depthFirst.1.labels 1 = (1 : WithTop Nat) := by decide
  obtain ⟨path, _⟩ := sound 1 1 held
  have onlyRoot : ∀ {vertex : Fin 3}, Path [] (0 : Fin 3) vertex → vertex = 0 := by
    intro vertex path
    induction path with
    | nil => rfl
    | cons path edge _ => exact False.elim (by simpa using edge.2.1)
  have impossible := onlyRoot path
  norm_num at impossible

end Mettapedia.Machines.WeightedRelaxation.Controls
