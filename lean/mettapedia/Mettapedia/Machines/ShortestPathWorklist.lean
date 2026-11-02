import Mettapedia.Machines.WeightedPathRelaxation
import Mettapedia.Machines.ResumableRegion

/-!
# A terminating improvement-driven shortest-path worklist

Only a strict distance improvement schedules outgoing edges again. The
coverage invariant says every currently violated edge inequality has a
pending duty. This establishes quiescence as closure, not mere queue emptiness
after dropped work. Nonnegative costs and a finite vertex universe make
strict label descent well-founded; finite pending work handles silent steps.

The existing MachineCore slice runner retains the full queue and event log.
DFS, FIFO and any duty-support-preserving enqueue discipline have the same final
path distances. Event traces, counts and source round counters are not thereby
identified. This is not a C scheduler, physical cost or atomicity theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.WeightedRelaxation.Worklist

variable {Vertex : Type} [DecidableEq Vertex]

structure State (Vertex : Type) where
  labels : Labels Vertex
  pending : List (Arc Vertex)
  improvements : List (Vertex × WithTop Nat)

abbrev Enqueue (Vertex : Type) := List (Arc Vertex) → List (Arc Vertex) → List (Arc Vertex)

/-- Pending duties retain their exact support. Duplicate duties may be
merged under the final-distance observer; source answer occurrences are a
different observation and are not deduplicated by this condition. -/
def Keeps (enqueue : Enqueue Vertex) : Prop :=
  ∀ children rest edge, edge ∈ enqueue children rest ↔ edge ∈ children ∨ edge ∈ rest

def outgoing (graph : List (Arc Vertex)) (vertex : Vertex) : List (Arc Vertex) :=
  graph.filter (fun edge => edge.source = vertex)

def initialState (graph : List (Arc Vertex)) (root : Vertex) : State Vertex :=
  ⟨initial root, outgoing graph root, []⟩

def handle (graph : List (Arc Vertex)) (enqueue : Enqueue Vertex)
    (labels : Labels Vertex) (edge : Arc Vertex) (rest : List (Arc Vertex))
    (events : List (Vertex × WithTop Nat)) : State Vertex :=
  if proposal labels edge < labels edge.target then
    ⟨relax labels edge, enqueue (outgoing graph edge.target) rest,
      (edge.target, proposal labels edge) :: events⟩
  else ⟨labels, rest, events⟩

def step (graph : List (Arc Vertex)) (enqueue : Enqueue Vertex) (state : State Vertex) : Option (State Vertex) :=
  match state.pending with
  | [] => none
  | edge :: rest => some (handle graph enqueue state.labels edge rest state.improvements)

abbrev core (graph : List (Arc Vertex)) (enqueue : Enqueue Vertex) : MachineCore Vertex where
  State := State Vertex
  load := initialState graph
  step := step graph enqueue

def Ranked (next before : State Vertex) : Prop :=
  Prod.Lex (fun a b : Labels Vertex => a < b) (fun a b : Nat => a < b)
    (next.labels, next.pending.length) (before.labels, before.pending.length)

omit [DecidableEq Vertex] in
theorem ranked_wellFounded [Finite Vertex] : WellFounded (Ranked (Vertex := Vertex)) := by
  let labelsWF : WellFoundedRelation (Labels Vertex) := ⟨(· < ·), wellFounded_lt⟩
  exact InvImage.wf (fun state : State Vertex => (state.labels, state.pending.length))
    (Prod.lex labelsWF Nat.lt_wfRel).wf

theorem handle_decreases (graph : List (Arc Vertex)) (enqueue : Enqueue Vertex)
    (labels : Labels Vertex) (edge : Arc Vertex) (rest : List (Arc Vertex))
    (events : List (Vertex × WithTop Nat)) :
    Ranked (handle graph enqueue labels edge rest events) ⟨labels, edge :: rest, events⟩ := by
  by_cases better : proposal labels edge < labels edge.target
  · simp only [Ranked, handle, if_pos better]
    exact Prod.Lex.left _ _ (relax_lt_of_better labels edge better)
  · simp only [Ranked, handle, if_neg better, List.length_cons]
    exact Prod.Lex.right _ (Nat.lt_succ_self _)

/-- Every finite worklist finishes; no fairness assumption is needed beyond
processing the head and finite enqueue results at each actual step. -/
theorem eventually_quiescent [Finite Vertex] (graph : List (Arc Vertex)) (enqueue : Enqueue Vertex)
    (state : State Vertex) : ∃ fuel, (MachineCore.runSlice (core graph enqueue) fuel state).1.pending = [] := by
  refine (ranked_wellFounded (Vertex := Vertex)).induction
    (C := fun current : State Vertex =>
      ∃ fuel, (MachineCore.runSlice (core graph enqueue) fuel current).1.pending = []) state ?_
  intro state ih
  cases pending : state.pending with
  | nil => exact ⟨0, pending⟩
  | cons edge rest =>
      have shape : state = ⟨state.labels, edge :: rest, state.improvements⟩ := by cases state; simp_all
      have decreases := handle_decreases graph enqueue state.labels edge rest state.improvements
      rw [← shape] at decreases
      obtain ⟨fuel, done⟩ := ih (handle graph enqueue state.labels edge rest state.improvements) decreases
      exact ⟨fuel + 1, by simpa [MachineCore.runSlice, core, step, pending] using done⟩

structure Valid (graph : List (Arc Vertex)) (root : Vertex) (state : State Vertex) : Prop where
  below : state.labels ≤ initial root
  sound : PathSound graph root state.labels
  authorized : ∀ edge ∈ state.pending, edge ∈ graph
  covered : ∀ edge ∈ graph, proposal state.labels edge < state.labels edge.target → edge ∈ state.pending

theorem initial_valid (graph : List (Arc Vertex)) (root : Vertex) : Valid graph root (initialState graph root) := by
  constructor
  · exact le_rfl
  · exact initial_sound graph root
  · intro edge member
    exact (List.mem_filter.mp member).1
  · intro edge member violated
    by_cases source : edge.source = root
    · simp [initialState, outgoing, member, source]
    · simp [initialState, proposal, initial, source] at violated

theorem handle_valid (graph : List (Arc Vertex)) (root : Vertex) (enqueue : Enqueue Vertex)
    (keeps : Keeps enqueue) (labels : Labels Vertex) (edge : Arc Vertex) (rest : List (Arc Vertex))
    (events : List (Vertex × WithTop Nat)) (valid : Valid graph root ⟨labels, edge :: rest, events⟩) :
    Valid graph root (handle graph enqueue labels edge rest events) := by
  have member : edge ∈ graph := valid.authorized edge (List.mem_cons_self ..)
  by_cases better : proposal labels edge < labels edge.target
  · simp only [handle, if_pos better]
    constructor
    · exact (relax_le labels edge).trans valid.below
    · exact relax_sound graph root labels edge member valid.sound
    · intro later held
      rcases (keeps _ _ later).1 held with child | remaining
      · exact (List.mem_filter.mp child).1
      · exact valid.authorized later (List.mem_cons_of_mem _ remaining)
    · intro later authorized violated
      apply (keeps _ _ later).2
      by_cases readsChanged : later.source = edge.target
      · left
        simp [outgoing, authorized, readsChanged]
      · right
        have sourceKept : proposal (relax labels edge) later = proposal labels later := by
          simp [proposal, relax_other labels edge later.source readsChanged]
        have oldViolation : proposal labels later < labels later.target := by
          rw [sourceKept] at violated
          exact violated.trans_le (relax_le labels edge later.target)
        rcases List.mem_cons.mp (valid.covered later authorized oldViolation) with same | pending
        · subst later
          have satisfied : relax labels edge edge.target ≤ proposal (relax labels edge) edge := by
            rw [sourceKept, relax_target]
            exact min_le_right _ _
          exact False.elim (not_lt_of_ge satisfied violated)
        · exact pending
  · simp only [handle, if_neg better]
    constructor
    · exact valid.below
    · exact valid.sound
    · intro later held
      exact valid.authorized later (List.mem_cons_of_mem _ held)
    · intro later authorized violated
      rcases List.mem_cons.mp (valid.covered later authorized violated) with same | pending
      · subst later
        exact False.elim (better violated)
      · exact pending

theorem slice_valid (graph : List (Arc Vertex)) (root : Vertex) (enqueue : Enqueue Vertex)
    (keeps : Keeps enqueue) (fuel : Nat) (state : State Vertex) (valid : Valid graph root state) :
    Valid graph root (MachineCore.runSlice (core graph enqueue) fuel state).1 := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      cases pending : state.pending with
      | nil => simpa [MachineCore.runSlice, core, step, pending] using valid
      | cons edge rest =>
          have shape : state = ⟨state.labels, edge :: rest, state.improvements⟩ := by cases state; simp_all
          simpa [MachineCore.runSlice, core, step, pending] using
            ih (handle graph enqueue state.labels edge rest state.improvements)
              (handle_valid graph root enqueue keeps _ _ _ _ (shape ▸ valid))

theorem quiescent_closed (graph : List (Arc Vertex)) (root : Vertex) (state : State Vertex)
    (valid : Valid graph root state) (empty : state.pending = []) : Closed graph state.labels := by
  intro edge member
  by_contra violated
  have pending := valid.covered edge member (lt_of_not_ge violated)
  simp [empty] at pending

theorem quiescent_eq_distance (graph : List (Arc Vertex)) (root : Vertex) (state : State Vertex)
    (valid : Valid graph root state) (empty : state.pending = []) : state.labels = distance graph root :=
  closed_sound_eq_distance graph root state.labels valid.below (quiescent_closed graph root state valid empty) valid.sound

/-- Finite termination and path-semantic correctness are both established. -/
theorem finite_shortest_paths [Finite Vertex] (graph : List (Arc Vertex)) (root : Vertex)
    (enqueue : Enqueue Vertex) (keeps : Keeps enqueue) :
    ∃ fuel, let result := (MachineCore.runSlice (core graph enqueue) fuel (initialState graph root)).1
      result.pending = [] ∧ result.labels = distance graph root := by
  obtain ⟨fuel, empty⟩ := eventually_quiescent graph enqueue (initialState graph root)
  exact ⟨fuel, empty, quiescent_eq_distance graph root _
    (slice_valid graph root enqueue keeps fuel _ (initial_valid graph root)) empty⟩

theorem completed_queues_agree (graph : List (Arc Vertex)) (root : Vertex)
    (first second : Enqueue Vertex) (firstKeeps : Keeps first) (secondKeeps : Keeps second)
    (m n : Nat)
    (firstDone : (MachineCore.runSlice (core graph first) m (initialState graph root)).1.pending = [])
    (secondDone : (MachineCore.runSlice (core graph second) n (initialState graph root)).1.pending = []) :
    (MachineCore.runSlice (core graph first) m (initialState graph root)).1.labels =
      (MachineCore.runSlice (core graph second) n (initialState graph root)).1.labels := by
  rw [quiescent_eq_distance graph root _ (slice_valid graph root first firstKeeps m _ (initial_valid graph root)) firstDone,
    quiescent_eq_distance graph root _ (slice_valid graph root second secondKeeps n _ (initial_valid graph root)) secondDone]

def dfs : Enqueue Vertex := fun children rest => children ++ rest
def fifo : Enqueue Vertex := fun children rest => rest ++ children
def dedupFifo : Enqueue Vertex := fun children rest => (rest ++ children).eraseDups

omit [DecidableEq Vertex] in
theorem dfs_keeps : Keeps (dfs (Vertex := Vertex)) := by
  intro children rest edge
  exact List.mem_append

omit [DecidableEq Vertex] in
theorem fifo_keeps : Keeps (fifo (Vertex := Vertex)) := by
  intro children rest edge
  simp [fifo, or_comm]

theorem dedupFifo_keeps : Keeps (dedupFifo (Vertex := Vertex)) := by
  intro children rest edge
  simp [dedupFifo, or_comm]

end Mettapedia.Machines.WeightedRelaxation.Worklist
