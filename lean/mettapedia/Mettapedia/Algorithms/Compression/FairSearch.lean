import Mettapedia.Algorithms.Compression.Search

/-!
# Coverage of the cost-and-age search

The queue's ticket deadline services an actual occurrence. Finite successor
paths therefore reach the service trace even in the presence of infinitely
many cheaper alternatives. Empty residual work certifies coverage of that
reachable region; a finite budget alone does not.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.FairQueue

universe u
variable {Node : Type u}

theorem ticket_unique {entries : List (Entry Node)}
    (ordered : entries.Pairwise (fun left right => left.ticket < right.ticket))
    {first second : Entry Node} (one : first ∈ entries) (two : second ∈ entries)
    (same : first.ticket = second.ticket) : first = second := by
  induction entries generalizing first second with
  | nil => simp at one
  | cons head rest ih =>
      obtain ⟨before, later⟩ := List.pairwise_cons.mp ordered
      rcases List.mem_cons.mp one with rfl | oneTail
      · rcases List.mem_cons.mp two with rfl | twoTail
        · rfl
        · have less := before second twoTail
          omega
      · rcases List.mem_cons.mp two with rfl | twoTail
        · have less := before first oneTail
          omega
        · exact ih later oneTail twoTail same

theorem numbered_values (start : Nat) (nodes : List Node) :
    (numbered start nodes).map Entry.value = nodes := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node rest ih => simp [numbered, ih]

/-- Every serviced and still-pending occurrence retains a successor-closed
invariant. This applies to arbitrary finite prefixes, not just complete runs. -/
theorem run_preserves_invariant (cost : Node → Nat) (successors : Node → List Node)
    (invariant : Node → Prop)
    (closed : ∀ node, invariant node → ∀ child ∈ successors node, invariant child)
    (fuel : Nat) (queue : Queue Node)
    (initial : ∀ node ∈ queue.pending.map Entry.value, invariant node) :
    (∀ node ∈ (run cost successors fuel queue).1.map Entry.value, invariant node) ∧
      (∀ node ∈ (run cost successors fuel queue).2.pending.map Entry.value, invariant node) := by
  induction fuel generalizing queue with
  | zero => exact ⟨by simp [run], initial⟩
  | succ fuel ih =>
      cases popped : pop cost queue with
      | none =>
          constructor
          · simp [run, tick, popped]
          · simpa [run, tick, popped] using initial
      | some choice =>
          obtain ⟨selected, remaining⟩ := choice
          have chosen : invariant selected.value := initial _
            (List.mem_map.mpr ⟨selected,
              (pop_perm cost queue popped).mem_iff.mp (List.mem_cons_self ..), rfl⟩)
          have rest : ∀ node ∈ (after successors queue selected remaining).pending.map Entry.value,
              invariant node := by
            intro node member
            simp only [after, List.map_append, numbered_values, List.mem_append] at member
            rcases member with old | generated
            · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp old
              exact initial _ (List.mem_map.mpr ⟨entry,
                (pop_perm cost queue popped).mem_iff.mp (List.mem_cons_of_mem _ present), rfl⟩)
            · exact closed _ chosen _ generated
          obtain ⟨serviced, pending⟩ := ih _ rest
          constructor
          · intro node member
            simp only [run, tick, popped, Option.map_some, List.map_cons, List.mem_cons] at member
            rcases member with rfl | later
            · exact chosen
            · exact serviced _ later
          · simpa [run, tick, popped] using pending

/-- Equal payloads do not merge tickets: the selected occurrence is the one
that was already waiting, regardless of newly generated equal values. -/
theorem entry_serviced_within (cost : Node → Nat) (successors : Node → List Node)
    (queue : Queue Node) (entry : Entry Node) (valid : Valid queue)
    (present : entry ∈ queue.pending) :
    ∃ fuel ≤ waitBound entry.ticket queue, entry ∈ (run cost successors fuel queue).1 := by
  have bounded : ∀ bound, ∀ q : Queue Node, waitBound entry.ticket q = bound →
      Valid q → entry ∈ q.pending → ∃ fuel ≤ bound, entry ∈ (run cost successors fuel q).1 := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
        intro q equal valid present
        obtain ⟨selected, remaining, popped⟩ :
            ∃ selected remaining, pop cost q = some (selected, remaining) := by
          cases pending : q.pending with
          | nil => simp [pending] at present
          | cons head rest =>
              by_cases age : q.phase.val = 7
              · exact ⟨head, rest, by simp [pop, pending, age]⟩
              · cases choice : minimum cost head rest with
                | mk selected remaining =>
                    exact ⟨selected, remaining, by simp [pop, pending, age, choice]⟩
        have advanced : tick cost successors q =
            some (selected, after successors q selected remaining) := by simp [tick, popped]
        by_cases same : selected.ticket = entry.ticket
        · have member : selected ∈ q.pending :=
            (pop_perm cost q popped).mem_iff.mp (List.mem_cons_self ..)
          have identical := ticket_unique valid.1 member present same
          refine ⟨1, ?_, ?_⟩
          · have positive := waitBound_positive entry.ticket q
            omega
          · simp [run, advanced, identical]
        · have live : HasTicket entry.ticket q := ⟨entry, present, rfl⟩
          have smaller := deadline_decreases cost successors q entry.ticket valid live popped same
          have moved := (pop_perm cost q popped).mem_iff.mpr present
          have retained : entry ∈ remaining := by
            rcases List.mem_cons.mp moved with identical | retained
            · exact False.elim (same (congrArg Entry.ticket identical.symm))
            · exact retained
          have validNext := after_valid cost successors q valid popped
          obtain ⟨fuel, allowance, served⟩ := ih _ (by omega) _ rfl validNext
            (List.mem_append_left _ retained)
          exact ⟨fuel + 1, by omega, by simp [run, advanced, served]⟩
  exact bounded _ queue rfl valid present

theorem run_valid (cost : Node → Nat) (successors : Node → List Node)
    (fuel : Nat) (queue : Queue Node) (valid : Valid queue) :
    Valid (run cost successors fuel queue).2 := by
  induction fuel generalizing queue with
  | zero => exact valid
  | succ fuel ih =>
      cases popped : pop cost queue with
      | none => simpa [run, tick, popped] using valid
      | some choice =>
          rcases choice with ⟨selected, remaining⟩
          simpa [run, tick, popped] using
            ih (after successors queue selected remaining) (after_valid cost successors queue valid popped)

theorem service_member (cost : Node → Nat) (successors : Node → List Node)
    (queue : Queue Node) (valid : Valid queue) (node : Node)
    (present : node ∈ queue.pending.map Entry.value) :
    ∃ fuel, node ∈ ((run cost successors fuel queue).1.map Entry.value) := by
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨fuel, _, served⟩ := entry_serviced_within cost successors queue entry valid member
  exact ⟨fuel, List.mem_map.mpr ⟨entry, served, rfl⟩⟩

/-- A finite prefix either services each old pending value or retains it. -/
theorem pending_account (cost : Node → Nat) (successors : Node → List Node)
    (fuel : Nat) (queue : Queue Node) (node : Node)
    (present : node ∈ queue.pending.map Entry.value) :
    node ∈ ((run cost successors fuel queue).1.map Entry.value) ∨
      node ∈ ((run cost successors fuel queue).2.pending.map Entry.value) := by
  induction fuel generalizing queue with
  | zero => exact .inr present
  | succ fuel ih =>
      cases popped : pop cost queue with
      | none => exact .inr (by simpa [run, tick, popped] using present)
      | some choice =>
          rcases choice with ⟨selected, remaining⟩
          obtain ⟨entry, member, rfl⟩ := List.mem_map.mp present
          have moved := (pop_perm cost queue popped).mem_iff.mpr member
          rcases List.mem_cons.mp moved with identical | retained
          · subst entry
            exact .inl (by simp [run, tick, popped])
          · have live : entry.value ∈ (after successors queue selected remaining).pending.map Entry.value :=
              List.mem_map.mpr ⟨entry, List.mem_append_left _ retained, rfl⟩
            rcases ih _ live with served | pending
            · exact .inl (by simp [run, tick, popped, served])
            · exact .inr (by simpa [run, tick, popped] using pending)

/-- Every successor of a serviced node remains accounted for in the trace or
residual queue, including when other occurrences have equal values. -/
theorem successor_account (cost : Node → Nat) (successors : Node → List Node)
    (fuel : Nat) (queue : Queue Node) (parent child : Node)
    (serviced : parent ∈ ((run cost successors fuel queue).1.map Entry.value))
    (generated : child ∈ successors parent) :
    child ∈ ((run cost successors fuel queue).1.map Entry.value) ∨
      child ∈ ((run cost successors fuel queue).2.pending.map Entry.value) := by
  induction fuel generalizing queue with
  | zero => simp [run] at serviced
  | succ fuel ih =>
      cases popped : pop cost queue with
      | none => simp [run, tick, popped] at serviced
      | some choice =>
          rcases choice with ⟨selected, remaining⟩
          have advanced : tick cost successors queue =
              some (selected, after successors queue selected remaining) := by simp [tick, popped]
          simp only [run, advanced, List.map_cons, List.mem_cons] at serviced
          rcases serviced with identical | later
          · have live : child ∈ (after successors queue selected remaining).pending.map Entry.value := by
              simp only [after, List.map_append, List.mem_append, numbered_values]
              exact .inr (identical ▸ generated)
            rcases pending_account cost successors fuel _ child live with served | pending
            · exact .inl (by simp [run, advanced, served])
            · exact .inr (by simpa [run, advanced] using pending)
          · rcases ih _ later with served | pending
            · exact .inl (by simp [run, advanced, served])
            · exact .inr (by simpa [run, advanced] using pending)

/-- The proved deadline, rather than an assumed fairness condition, covers
every finite successor path from each root occurrence. -/
theorem services_reachable (cost : Node → Nat) (successors : Node → List Node)
    (queue : Queue Node) (valid : Valid queue) {root target : Node}
    (rootMember : root ∈ queue.pending.map Entry.value)
    (reachable : Relation.ReflTransGen (fun parent child => child ∈ successors parent) root target) :
    ∃ fuel, target ∈ ((run cost successors fuel queue).1.map Entry.value) := by
  induction reachable with
  | refl => exact service_member cost successors queue valid root rootMember
  | tail reachable generated ih =>
      obtain ⟨fuel, serviced⟩ := ih
      rcases successor_account cost successors fuel queue _ _ serviced generated with done | live
      · exact ⟨fuel, done⟩
      · obtain ⟨extra, done⟩ := service_member cost successors _
          (run_valid cost successors fuel queue valid) _ live
        refine ⟨fuel + extra, ?_⟩
        rw [run_add]
        simp only [List.map_append, List.mem_append]
        exact .inr done

/-- Empty residual work proves outgoing coverage of the region rooted in the
initial queue. This statement does not follow from a budget stop. -/
theorem complete_covers_reachable (cost : Node → Nat) (successors : Node → List Node)
    (fuel : Nat) (queue : Queue Node) {root target : Node}
    (rootMember : root ∈ queue.pending.map Entry.value)
    (reachable : Relation.ReflTransGen (fun parent child => child ∈ successors parent) root target)
    (complete : (run cost successors fuel queue).2.pending = []) :
    target ∈ ((run cost successors fuel queue).1.map Entry.value) := by
  induction reachable with
  | refl =>
      rcases pending_account cost successors fuel queue root rootMember with served | live
      · exact served
      · simp [complete] at live
  | tail reachable generated ih =>
      rcases successor_account cost successors fuel queue _ _ ih generated with served | live
      · exact served
      · simp [complete] at live

namespace CoverageControls

/-- Seven cost turns may legitimately miss a waiting answer. -/
theorem finite_budget_can_miss_live_root :
    1 ∈ ((initial [0, 1] : Queue Nat).pending.map Entry.value) ∧
      1 ∉ ((run id Controls.zeroCostLoop 7 (initial [0, 1])).1.map Entry.value) ∧
      (run id Controls.zeroCostLoop 7 (initial [0, 1])).2.pending ≠ [] := by decide

/-- The next age turn services it while the cheap branch remains productive. -/
theorem age_services_root_behind_loop :
    ((run id Controls.zeroCostLoop 8 (initial [0, 1])).1.map Entry.value) =
      [0, 0, 0, 0, 0, 0, 0, 1] := by decide

theorem equal_values_keep_distinct_occurrences :
    ((run (fun _ : Nat => 0) (fun _ => []) 2 (initial [3, 3])).1.map Entry.ticket) =
      [0, 1] := by decide

end CoverageControls

#print axioms run_preserves_invariant

end Mettapedia.Algorithms.Compression.FairQueue

namespace Mettapedia.Algorithms.Compression.Search

open FramedTree Mettapedia.GSLT.Core.BranchingTemporal

variable {Node Observation : Type} [DecidableEq Observation]

theorem best_eventually_le_reachable (read : Tree → Option Observation) (original current : Tree)
    (system : BranchingSystem Node Tree) (cost : Node → Nat) (queue : FairQueue.Queue Node)
    (validQueue : FairQueue.Valid queue) {root node : Node} (rootMember : root ∈ queue.pending.map FairQueue.Entry.value)
    (reachable : Relation.ReflTransGen (fun parent child => child ∈ system.successors parent) root node)
    (artifact : Tree) (emits : system.emit node = some artifact) (observation : Observation)
    (source : read original = some observation) (currentValid : read current = some observation)
    (artifactValid : read artifact = some observation) :
    ∃ fuel, byteLength (best read original current system cost fuel queue) ≤ byteLength artifact := by
  obtain ⟨fuel, serviced⟩ := FairQueue.services_reachable cost system.successors queue validQueue rootMember reachable
  obtain ⟨entry, present, same⟩ := List.mem_map.mp serviced
  refine ⟨fuel, best_le_every_emitted read original current system cost fuel queue observation source currentValid artifact ?_ artifactValid⟩
  exact (proposal_origin system cost fuel queue artifact).mpr ⟨entry, present, same ▸ emits⟩

theorem best_le_reachable_of_complete (read : Tree → Option Observation) (original current : Tree)
    (system : BranchingSystem Node Tree) (cost : Node → Nat) (queue : FairQueue.Queue Node)
    (fuel : Nat) (complete : (FairQueue.run cost system.successors fuel queue).2.pending = [])
    {root node : Node} (rootMember : root ∈ queue.pending.map FairQueue.Entry.value)
    (reachable : Relation.ReflTransGen (fun parent child => child ∈ system.successors parent) root node)
    (artifact : Tree) (emits : system.emit node = some artifact) (observation : Observation)
    (source : read original = some observation) (currentValid : read current = some observation)
    (artifactValid : read artifact = some observation) :
    byteLength (best read original current system cost fuel queue) ≤ byteLength artifact := by
  have serviced := FairQueue.complete_covers_reachable cost system.successors fuel queue rootMember reachable complete
  obtain ⟨entry, present, same⟩ := List.mem_map.mp serviced
  exact best_le_every_emitted read original current system cost fuel queue observation source currentValid artifact
    ((proposal_origin system cost fuel queue artifact).mpr ⟨entry, present, same ▸ emits⟩) artifactValid

end Mettapedia.Algorithms.Compression.Search
