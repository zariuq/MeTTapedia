import Mettapedia.Machines.ShortestPathWorklist

/-!
# Improvement-driven vertex-frontier rounds

Each round visits the outgoing edges of the ordered frontier, accumulating
strict-improvement events. Only the next frontier is deduplicated. A productive
round increments the counter; the final empty round does not. Coverage, path
soundness and finite strict label descent establish termination and shortest
paths. This source-shaped scheduler is not an adequacy theorem for PeTTa's
`unique` frontend or a correspondence for native work and allocation costs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.WeightedRelaxation.Rounds

variable {Vertex : Type} [DecidableEq Vertex]

def scan : List (Arc Vertex) → Labels Vertex → List Vertex → Labels Vertex × List Vertex
  | [], labels, changed => (labels, changed)
  | edge :: rest, labels, changed =>
      if proposal labels edge < labels edge.target then
        scan rest (relax labels edge) (changed ++ [edge.target])
      else scan rest labels changed

def duties (graph : List (Arc Vertex)) (frontier : List Vertex) : List (Arc Vertex) :=
  frontier.flatMap (Worklist.outgoing graph)

theorem scan_append (first later : List (Arc Vertex)) (labels : Labels Vertex) (changed : List Vertex) :
    scan (first ++ later) labels changed =
      scan later (scan first labels changed).1 (scan first labels changed).2 := by
  induction first generalizing labels changed with
  | nil => rfl
  | cons edge rest ih =>
      by_cases better : proposal labels edge < labels edge.target
      · simpa only [List.cons_append, scan, if_pos better] using ih (relax labels edge) (changed ++ [edge.target])
      · simpa only [List.cons_append, scan, if_neg better] using ih labels changed

theorem scan_prefix (edges : List (Arc Vertex)) (labels : Labels Vertex) (earlier changed : List Vertex) :
    scan edges labels (earlier ++ changed) =
      ((scan edges labels changed).1, earlier ++ (scan edges labels changed).2) := by
  induction edges generalizing labels changed with
  | nil => rfl
  | cons edge rest ih =>
      by_cases better : proposal labels edge < labels edge.target
      · simpa only [scan, if_pos better, List.append_assoc] using ih (relax labels edge) (changed ++ [edge.target])
      · simpa only [scan, if_neg better] using ih labels changed

theorem mem_duties (graph : List (Arc Vertex)) (frontier : List Vertex) (edge : Arc Vertex) :
    edge ∈ duties graph frontier ↔ edge ∈ graph ∧ edge.source ∈ frontier := by
  simp only [duties, List.mem_flatMap, Worklist.outgoing, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨vertex, member, authorized, equal⟩
    exact ⟨authorized, equal ▸ member⟩
  · rintro ⟨authorized, member⟩
    exact ⟨edge.source, member, authorized, rfl⟩

def pass (graph : List (Arc Vertex)) (labels : Labels Vertex) (frontier : List Vertex) : Labels Vertex × List Vertex :=
  let result := scan (duties graph frontier) labels []
  (result.1, result.2.eraseDups)

structure Valid (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex) (frontier : List Vertex) : Prop where
  below : labels ≤ initial root
  sound : PathSound graph root labels
  covered : ∀ edge ∈ graph, proposal labels edge < labels edge.target → edge.source ∈ frontier

structure Pending (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex)
    (pending : List (Arc Vertex)) (changed : List Vertex) : Prop where
  below : labels ≤ initial root
  sound : PathSound graph root labels
  authorized : ∀ edge ∈ pending, edge ∈ graph
  covered : ∀ edge ∈ graph, proposal labels edge < labels edge.target → edge ∈ pending ∨ edge.source ∈ changed

theorem initial_valid (graph : List (Arc Vertex)) (root : Vertex) : Valid graph root (initial root) [root] := by
  refine ⟨le_rfl, initial_sound graph root, ?_⟩
  intro edge _ better
  by_cases source : edge.source = root
  · simp [source]
  · simp [proposal, initial, source] at better

theorem begin_pass {graph : List (Arc Vertex)} {root : Vertex} {labels : Labels Vertex} {frontier : List Vertex}
    (valid : Valid graph root labels frontier) : Pending graph root labels (duties graph frontier) [] := by
  refine ⟨valid.below, valid.sound, ?_, ?_⟩
  · intro edge member
    exact ((mem_duties graph frontier edge).mp member).1
  · intro edge member better
    exact Or.inl ((mem_duties graph frontier edge).mpr ⟨member, valid.covered edge member better⟩)

theorem improved_pending {graph : List (Arc Vertex)} {root : Vertex} {labels : Labels Vertex}
    {edge : Arc Vertex} {rest : List (Arc Vertex)} {changed : List Vertex}
    (valid : Pending graph root labels (edge :: rest) changed) :
    Pending graph root (relax labels edge) rest (changed ++ [edge.target]) := by
  have member := valid.authorized edge List.mem_cons_self
  refine ⟨(relax_le labels edge).trans valid.below, relax_sound graph root labels edge member valid.sound, ?_, ?_⟩
  · intro later held
    exact valid.authorized later (List.mem_cons_of_mem _ held)
  · intro later authorized violated
    by_cases readsChanged : later.source = edge.target
    · exact Or.inr (by simp [readsChanged])
    · have sourceKept : proposal (relax labels edge) later = proposal labels later := by
        simp [proposal, relax_other labels edge later.source readsChanged]
      have oldViolation : proposal labels later < labels later.target := by
        rw [sourceKept] at violated
        exact violated.trans_le (relax_le labels edge later.target)
      rcases valid.covered later authorized oldViolation with pending | deferred
      · rcases List.mem_cons.mp pending with same | held
        · subst later
          have satisfied : relax labels edge edge.target ≤ proposal (relax labels edge) edge := by
            rw [sourceKept, relax_target]
            exact min_le_right _ _
          exact False.elim (not_lt_of_ge satisfied violated)
        · exact Or.inl held
      · exact Or.inr (List.mem_append_left _ deferred)

theorem silent_pending {graph : List (Arc Vertex)} {root : Vertex} {labels : Labels Vertex}
    {edge : Arc Vertex} {rest : List (Arc Vertex)} {changed : List Vertex}
    (valid : Pending graph root labels (edge :: rest) changed)
    (quiet : ¬ proposal labels edge < labels edge.target) : Pending graph root labels rest changed := by
  refine ⟨valid.below, valid.sound, ?_, ?_⟩
  · intro later held
    exact valid.authorized later (List.mem_cons_of_mem _ held)
  · intro later authorized violated
    rcases valid.covered later authorized violated with pending | deferred
    · rcases List.mem_cons.mp pending with same | held
      · subst later; exact False.elim (quiet violated)
      · exact Or.inl held
    · exact Or.inr deferred

theorem scan_valid (graph : List (Arc Vertex)) (root : Vertex) (pending : List (Arc Vertex))
    (labels : Labels Vertex) (changed : List Vertex) (valid : Pending graph root labels pending changed) :
    Pending graph root (scan pending labels changed).1 [] (scan pending labels changed).2 := by
  induction pending generalizing labels changed with
  | nil => exact valid
  | cons edge rest ih =>
      by_cases better : proposal labels edge < labels edge.target
      · simpa only [scan, if_pos better] using ih (relax labels edge) (changed ++ [edge.target]) (improved_pending valid)
      · simpa only [scan, if_neg better] using ih labels changed (silent_pending valid better)

theorem pass_valid (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex) (frontier : List Vertex)
    (valid : Valid graph root labels frontier) : Valid graph root (pass graph labels frontier).1 (pass graph labels frontier).2 := by
  have completed := scan_valid graph root (duties graph frontier) labels [] (begin_pass valid)
  refine ⟨completed.below, completed.sound, ?_⟩
  intro edge member violated
  have held := completed.covered edge member violated
  simpa [pass] using held

theorem scan_progress (pending : List (Arc Vertex)) (labels : Labels Vertex) (changed : List Vertex) :
    (scan pending labels changed).1 ≤ labels ∧
      ((scan pending labels changed).2 ≠ changed → (scan pending labels changed).1 < labels) := by
  induction pending generalizing labels changed with
  | nil => exact ⟨le_rfl, fun impossible => (impossible rfl).elim⟩
  | cons edge rest ih =>
      by_cases better : proposal labels edge < labels edge.target
      · simp only [scan, if_pos better]
        have tail := ih (relax labels edge) (changed ++ [edge.target])
        exact ⟨tail.1.trans (relax_le labels edge), fun _ => lt_of_le_of_lt tail.1 (relax_lt_of_better labels edge better)⟩
      · simpa only [scan, if_neg better] using ih labels changed

theorem scan_changed_finite (pending : List (Arc Vertex)) (labels : Labels Vertex) (changed : List Vertex)
    (reached : ∀ vertex ∈ changed, labels vertex ≠ ⊤) :
    ∀ vertex ∈ (scan pending labels changed).2, (scan pending labels changed).1 vertex ≠ ⊤ := by
  induction pending generalizing labels changed with
  | nil => exact reached
  | cons edge rest ih =>
      by_cases better : proposal labels edge < labels edge.target
      · have nextReached : ∀ vertex ∈ changed ++ [edge.target], relax labels edge vertex ≠ ⊤ := by
          intro vertex member
          rcases List.mem_append.mp member with old | new
          · exact ne_of_lt ((relax_le labels edge vertex).trans_lt (lt_top_iff_ne_top.mpr (reached vertex old)))
          · have same := List.mem_singleton.mp new
            subst vertex
            rw [relax_target]
            exact ne_of_lt ((min_le_right _ _).trans_lt (better.trans_le le_top))
        simpa only [scan, if_pos better] using ih (relax labels edge) (changed ++ [edge.target]) nextReached
      · simpa only [scan, if_neg better] using ih labels changed reached

theorem pass_frontier_finite (graph : List (Arc Vertex)) (labels : Labels Vertex) (frontier : List Vertex) :
    ∀ vertex ∈ (pass graph labels frontier).2, (pass graph labels frontier).1 vertex ≠ ⊤ := by
  intro vertex member
  exact scan_changed_finite (duties graph frontier) labels [] (by simp) vertex (List.mem_eraseDups.mp member)

theorem productive_decreases (graph : List (Arc Vertex)) (labels : Labels Vertex) (frontier : List Vertex)
    (productive : (pass graph labels frontier).2 ≠ []) : (pass graph labels frontier).1 < labels := by
  apply (scan_progress (duties graph frontier) labels []).2
  intro quiet
  simp [pass, quiet] at productive

def targets (graph : List (Arc Vertex)) : Finset Vertex := (graph.map Arc.target).toFinset

theorem scan_outside (pending : List (Arc Vertex)) (labels : Labels Vertex) (changed : List Vertex) (vertex : Vertex)
    (outside : ∀ edge ∈ pending, vertex ≠ edge.target) : (scan pending labels changed).1 vertex = labels vertex := by
  induction pending generalizing labels changed with
  | nil => rfl
  | cons edge rest ih =>
      have later : ∀ item ∈ rest, vertex ≠ item.target := fun item member => outside item (List.mem_cons_of_mem _ member)
      by_cases better : proposal labels edge < labels edge.target
      · simp only [scan, if_pos better]
        exact (ih (relax labels edge) (changed ++ [edge.target]) later).trans
          (relax_other labels edge vertex (outside edge List.mem_cons_self))
      · simpa only [scan, if_neg better] using ih labels changed later

theorem pass_outside_targets (graph : List (Arc Vertex)) (labels : Labels Vertex) (frontier : List Vertex)
    (vertex : Vertex) (outside : vertex ∉ targets graph) : (pass graph labels frontier).1 vertex = labels vertex := by
  apply scan_outside
  intro edge member same
  apply outside
  simp only [targets, List.mem_toFinset, List.mem_map]
  exact ⟨edge, ((mem_duties graph frontier edge).mp member).1, same.symm⟩

def restricted (graph : List (Arc Vertex)) (labels : Labels Vertex) : Labels (targets graph) :=
  fun vertex => labels vertex.1

theorem productive_restricted_decreases (graph : List (Arc Vertex)) (labels : Labels Vertex) (frontier : List Vertex)
    (productive : (pass graph labels frontier).2 ≠ []) :
    restricted graph (pass graph labels frontier).1 < restricted graph labels := by
  have smaller := productive_decreases graph labels frontier productive
  apply lt_iff_le_and_ne.mpr
  refine ⟨fun vertex => le_of_lt smaller vertex.1, ?_⟩
  intro same
  apply (ne_of_lt smaller)
  funext vertex
  by_cases member : vertex ∈ targets graph
  · exact congrFun same ⟨vertex, member⟩
  · exact pass_outside_targets graph labels frontier vertex member

theorem quiet_closed (graph : List (Arc Vertex)) (root : Vertex) (labels : Labels Vertex) (frontier : List Vertex)
    (valid : Valid graph root labels frontier) (quiet : frontier = []) : Closed graph labels := by
  intro edge member
  by_contra violated
  have held := valid.covered edge member (lt_of_not_ge violated)
  simp [quiet] at held

/-- Allowance counts complete rounds, not edge firings or source evaluator
instructions. `none` means unfinished, never an empty distance map. -/
def run (graph : List (Arc Vertex)) : Nat → Labels Vertex → List Vertex → Nat → Option (Labels Vertex × Nat)
  | 0, _, _, _ => none
  | fuel + 1, labels, frontier, count =>
      let result := pass graph labels frontier
      if result.2 = [] then some (result.1, count)
      else run graph fuel result.1 result.2 (count + 1)

theorem terminates (graph : List (Arc Vertex)) (labels : Labels Vertex) (frontier : List Vertex) (count : Nat) :
    ∃ fuel result, run graph fuel labels frontier count = some result := by
  have descent : WellFounded (fun next current : Labels Vertex => restricted graph next < restricted graph current) :=
    InvImage.wf (restricted graph) (wellFounded_lt (α := Labels (targets graph)))
  induction labels using descent.induction generalizing frontier count with
  | h labels ih =>
      by_cases quiet : (pass graph labels frontier).2 = []
      · exact ⟨1, ((pass graph labels frontier).1, count), by simp [run, quiet]⟩
      · obtain ⟨fuel, result, done⟩ := ih (pass graph labels frontier).1 (productive_restricted_decreases graph labels frontier quiet)
          (pass graph labels frontier).2 (count + 1)
        exact ⟨fuel + 1, result, by simp [run, quiet, done]⟩

theorem completed_distances (graph : List (Arc Vertex)) (root : Vertex) (fuel : Nat)
    (labels : Labels Vertex) (frontier : List Vertex) (count : Nat) (result : Labels Vertex) (rounds : Nat)
    (valid : Valid graph root labels frontier) (completed : run graph fuel labels frontier count = some (result, rounds)) :
    result = distance graph root := by
  induction fuel generalizing labels frontier count with
  | zero => cases completed
  | succ fuel ih =>
      have nextValid := pass_valid graph root labels frontier valid
      simp only [run] at completed
      split at completed
      next quiet =>
        obtain ⟨same, _⟩ := Prod.mk.inj (Option.some.inj completed)
        rw [← same]
        exact closed_sound_eq_distance graph root _ nextValid.below
          (quiet_closed graph root _ _ nextValid quiet) nextValid.sound
      next => exact ih _ _ _ nextValid completed

theorem finite_shortest_paths (graph : List (Arc Vertex)) (root : Vertex) :
    ∃ fuel rounds, run graph fuel (initial root) [root] 0 = some (distance graph root, rounds) := by
  obtain ⟨fuel, ⟨labels, rounds⟩, completed⟩ := terminates graph (initial root) [root] 0
  have exact := completed_distances graph root fuel (initial root) [root] 0 labels rounds (initial_valid graph root) completed
  exact ⟨fuel, rounds, by simpa [exact] using completed⟩

end Mettapedia.Machines.WeightedRelaxation.Rounds
