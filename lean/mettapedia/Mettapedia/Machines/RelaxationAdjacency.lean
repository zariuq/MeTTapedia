import Mettapedia.Machines.WeightedPathRelaxation

/-!
# Capturing one source distance across an outgoing-edge loop

The source-shaped loop reads a vertex distance once and then processes its
captured outgoing-edge sequence. A live loop rereads the source label at each
edge. Nonnegative costs make the source coordinate stable under these own
updates, including self-loops, so both loops preserve the exact ordered
improvement emissions and final labels. This permits read/write pattern
overlap when the actual value is unchanged.

No external update is hidden inside the loop. Interference on the source
coordinate, changed graph rows or a different snapshot policy requires a
separate boundary argument.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.WeightedRelaxation.Adjacency

variable {Vertex : Type} [DecidableEq Vertex]

theorem relax_keeps_source (labels : Labels Vertex) (edge : Arc Vertex) :
    relax labels edge edge.source = labels edge.source := by
  by_cases self : edge.source = edge.target
  · have dominated : labels edge.source ≤ proposal labels edge := by
      calc
        labels edge.source = labels edge.source + 0 := (add_zero _).symm
        _ ≤ labels edge.source + (edge.weight : WithTop Nat) := add_le_add le_rfl zero_le
    rw [self, relax_target]
    rw [self] at dominated
    exact min_eq_left dominated
  · exact relax_other labels edge edge.source self

structure State (Vertex : Type) where
  labels : Labels Vertex
  emitted : List Vertex

def capturedStep (sourceDistance : WithTop Nat) (edge : Arc Vertex) (state : State Vertex) : State Vertex :=
  let candidate := sourceDistance + (edge.weight : WithTop Nat)
  if candidate < state.labels edge.target then
    ⟨KeyedImprovement.lower state.labels edge.target candidate, state.emitted ++ [edge.target]⟩
  else state

def liveStep (edge : Arc Vertex) (state : State Vertex) : State Vertex :=
  if proposal state.labels edge < state.labels edge.target then
    ⟨relax state.labels edge, state.emitted ++ [edge.target]⟩
  else state

theorem step_agrees (state : State Vertex) (edge : Arc Vertex) :
    capturedStep (state.labels edge.source) edge state = liveStep edge state := rfl

theorem liveStep_keeps_source (state : State Vertex) (edge : Arc Vertex) :
    (liveStep edge state).labels edge.source = state.labels edge.source := by
  by_cases better : proposal state.labels edge < state.labels edge.target
  · simpa [liveStep, better] using relax_keeps_source state.labels edge
  · simp [liveStep, better]

def capturedLoop (sourceDistance : WithTop Nat) (edges : List (Arc Vertex)) (state : State Vertex) : State Vertex :=
  edges.foldl (fun current edge => capturedStep sourceDistance edge current) state

def liveLoop (edges : List (Arc Vertex)) (state : State Vertex) : State Vertex :=
  edges.foldl (fun current edge => liveStep edge current) state

/-- Agreement includes each source-shaped successful-improvement return,
not merely the final minimum at each key. -/
theorem captured_loop_exact (source : Vertex) (edges : List (Arc Vertex)) (state : State Vertex)
    (outgoing : ∀ edge ∈ edges, edge.source = source) :
    capturedLoop (state.labels source) edges state = liveLoop edges state := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih =>
      have here := outgoing edge (List.mem_cons_self ..)
      have later : ∀ next ∈ rest, next.source = source :=
        fun next member => outgoing next (List.mem_cons_of_mem _ member)
      change capturedLoop (state.labels source) rest (capturedStep (state.labels source) edge state) =
        liveLoop rest (liveStep edge state)
      have first : capturedStep (state.labels source) edge state = liveStep edge state := by
        rw [← here]
        exact step_agrees state edge
      rw [first]
      have stable : (liveStep edge state).labels source = state.labels source := by
        simpa only [here] using liveStep_keeps_source state edge
      simpa only [stable] using ih (liveStep edge state) later

theorem liveLoop_append (first later : List (Arc Vertex)) (state : State Vertex) :
    liveLoop (first ++ later) state = liveLoop later (liveLoop first state) := by
  simp [liveLoop, List.foldl_append]

namespace Controls

def edge : Arc (Fin 2) := ⟨0, 1, 1⟩
def before : Labels (Fin 2) := fun key => if key = 0 then 10 else ⊤
def after : State (Fin 2) := ⟨Function.update before 0 0, []⟩

theorem external_source_improvement_breaks_capture :
    (capturedStep 10 edge after).labels 1 = 11 ∧
      (liveStep edge after).labels 1 = 1 := by decide

theorem nonnegative_self_loop_emits_nothing :
    (liveStep (⟨0, 0, 0⟩ : Arc (Fin 2)) ⟨before, []⟩).emitted = [] := by decide

end Controls

end Mettapedia.Machines.WeightedRelaxation.Adjacency
