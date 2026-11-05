import Mettapedia.Machines.CTLUntilCandidateBag

/-!
# EU frontier termination from finite input support

The existing occurrence-preserving worker can add only vertices from its
finite holds list. Every productive round removes at least one vertex from
the not-yet-known part of that support. No finite ambient vertex type is
needed, and the final quiet round remains part of the returned counter.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CTLUntilFiniteSupport

open CTLUntilCandidateBag

variable {Vertex : Type} [DecidableEq Vertex]

def remaining (holds : List Vertex) (state : State Vertex) : Finset Vertex :=
  holds.toFinset \ state.known.toFinset

theorem remaining_advance_subset (edges : List (Vertex × Vertex)) (holds : List Vertex)
    (state : State Vertex) :
    remaining holds (advance edges holds state) ⊆ remaining holds state := by
  intro vertex member
  simp only [remaining, Finset.mem_sdiff, List.mem_toFinset, advance,
    List.mem_append, not_or] at member ⊢
  exact ⟨member.1, member.2.1⟩

theorem advance_decreases (edges : List (Vertex × Vertex)) (holds : List Vertex)
    (state : State Vertex) (productive : (advance edges holds state).delta ≠ []) :
    (remaining holds (advance edges holds state)).card < (remaining holds state).card := by
  obtain ⟨vertex, member⟩ := List.exists_mem_of_ne_nil _ productive
  have fresh : vertex ∈ CTLUntilCandidateBag.fresh (candidates edges holds state.delta) state.known.toFinset := member
  obtain ⟨candidate, absent⟩ := (mem_fresh _ _ _).mp fresh
  have holding := ((mem_candidates edges holds state.delta vertex).mp candidate).1
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (remaining_advance_subset edges holds state)).mpr
  refine ⟨vertex, ?_, ?_⟩
  · simpa only [remaining, Finset.mem_sdiff, List.mem_toFinset] using And.intro holding absent
  · simp only [remaining, Finset.mem_sdiff, List.mem_toFinset, advance, List.mem_append]
    exact fun missing => missing.2 (Or.inr fresh)

theorem fresh_subset_remaining (edges : List (Vertex × Vertex)) (holds : List Vertex)
    (state : State Vertex) :
    (advance edges holds state).delta.toFinset ⊆ remaining holds state := by
  intro vertex member
  have present : vertex ∈ fresh (candidates edges holds state.delta) state.known.toFinset :=
    List.mem_toFinset.mp member
  obtain ⟨candidate, absent⟩ := (mem_fresh _ _ _).mp present
  exact Finset.mem_sdiff.mpr
    ⟨List.mem_toFinset.mpr ((mem_candidates edges holds state.delta vertex).mp candidate).1, absent⟩

theorem remaining_advance (edges : List (Vertex × Vertex)) (holds : List Vertex)
    (state : State Vertex) :
    remaining holds (advance edges holds state) =
      remaining holds state \ (advance edges holds state).delta.toFinset := by
  ext vertex
  simp only [remaining, Finset.mem_sdiff, List.mem_toFinset, advance, List.mem_append, not_or]
  tauto

/-- New frontiers have distinct entries even when their candidate word has
duplicate producers. Every newly known vertex spends exactly one rank unit. -/
theorem remaining_balance (edges : List (Vertex × Vertex)) (holds : List Vertex)
    (state : State Vertex) :
    (remaining holds (advance edges holds state)).card + (advance edges holds state).delta.length =
      (remaining holds state).card := by
  have balance := Finset.card_sdiff_add_card_eq_card (fresh_subset_remaining edges holds state)
  rw [← remaining_advance, List.toFinset_card_of_nodup (advance_new_occurrences_distinct edges holds state)] at balance
  exact balance

private theorem flatMap_length_le {Item Value : Type} (items : List Item) (f : Item → List Value)
    (bound : Nat) (bounded : ∀ item ∈ items, (f item).length ≤ bound) :
    (items.flatMap f).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
      have head := bounded item List.mem_cons_self
      have tail := ih (fun value member => bounded value (List.mem_cons_of_mem _ member))
      simpa only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul, Nat.add_comm] using
        Nat.add_le_add head tail

/-- The bound counts all three authored occurrence loops; it does not replace
the edge, predicate or current-frontier bags by their supports. -/
theorem candidates_length_le (edges : List (Vertex × Vertex)) (holds delta : List Vertex) :
    (candidates edges holds delta).length ≤ delta.length * edges.length * holds.length := by
  have bounded : (candidates edges holds delta).length ≤ delta.length * (edges.length * holds.length) := by
    apply flatMap_length_le delta _ (edges.length * holds.length)
    intro next _
    apply flatMap_length_le edges _ holds.length
    intro edge _
    by_cases same : edge.2 = next
    · simpa only [if_pos same] using List.length_filter_le (fun prior => prior == edge.1) holds
    · simp only [if_neg same, List.length_nil, Nat.zero_le]
  simpa only [Nat.mul_assoc] using bounded

/-- Initial identities sufficient for candidate processing, current-frontier
cleanup and all later phases. This is not a machine-step or wall-time bound. -/
def allowance (edges : List (Vertex × Vertex)) (holds : List Vertex) (state : State Vertex) : Nat :=
  (state.delta.length + (remaining holds state).card) * (edges.length * holds.length + 1)

theorem allowance_advance (edges : List (Vertex × Vertex)) (holds : List Vertex) (state : State Vertex) :
    allowance edges holds (advance edges holds state) +
      (candidates edges holds state.delta).length + state.delta.length ≤ allowance edges holds state := by
  have cost : (candidates edges holds state.delta).length + state.delta.length ≤
      state.delta.length * (edges.length * holds.length + 1) := by
    simpa only [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] using
      Nat.add_le_add_right (candidates_length_le edges holds state.delta) state.delta.length
  have retained : allowance edges holds (advance edges holds state) =
      (remaining holds state).card * (edges.length * holds.length + 1) := by
    unfold allowance
    rw [Nat.add_comm (advance edges holds state).delta.length, remaining_balance]
  rw [retained, Nat.add_assoc]
  calc
    (remaining holds state).card * (edges.length * holds.length + 1) +
        ((candidates edges holds state.delta).length + state.delta.length) ≤
      (remaining holds state).card * (edges.length * holds.length + 1) +
        state.delta.length * (edges.length * holds.length + 1) := Nat.add_le_add_left cost _
    _ = allowance edges holds state := by simp only [allowance, Nat.add_mul, Nat.add_comm]

/-- A sufficient phase allowance constructs a completed run of the existing
worker. Neither successful execution nor a future quiet-state certificate is
an input. The counter still includes the final quiet phase. -/
theorem run_complete_of_rank_lt (edges : List (Vertex × Vertex)) (holds : List Vertex)
    (fuel counter : Nat) (state : State Vertex)
    (enough : (remaining holds state).card < fuel) :
    ∃ after answer,
      run edges holds fuel counter state = some (after, answer) ∧
      counter < answer ∧ answer ≤ counter + fuel ∧ after.delta = [] := by
  induction fuel generalizing counter state with
  | zero => omega
  | succ fuel ih =>
      by_cases quiet : (advance edges holds state).delta = []
      · refine ⟨advance edges holds state, counter + 1, ?_, by omega, by omega, quiet⟩
        simp only [run, if_pos quiet]
      · have decrease := advance_decreases edges holds state quiet
        obtain ⟨after, answer, completed, lower, upper, finalQuiet⟩ :=
          ih (counter + 1) (advance edges holds state) (by omega)
        refine ⟨after, answer, ?_, by omega, by omega, finalQuiet⟩
        simpa only [run, if_neg quiet] using completed

/-- Arbitrary vertex namespaces, including natural source identifiers, need
only finite edge/operand/goal lists. Goal duplicates remain stored occurrences;
the independent EU meaning observes their support. -/
theorem finite_completion (edges : List (Vertex × Vertex)) (holds goal : List Vertex) :
    ∃ after counter,
      run edges holds ((holds.toFinset \ goal.toFinset).card + 1) 0
        ⟨goal, goal⟩ = some (after, counter) ∧
      0 < counter ∧ counter ≤ (holds.toFinset \ goal.toFinset).card + 1 ∧ after.delta = [] ∧
      ∀ vertex, vertex ∈ after.known ↔ Mettapedia.Logic.CTLFixedPoints.Until
        (CTLUntilFrontier.Relation edges.toFinset) ↑holds.toFinset ↑goal.toFinset vertex := by
  obtain ⟨after, counter, completed, positive, upper, quiet⟩ :=
    run_complete_of_rank_lt edges holds ((holds.toFinset \ goal.toFinset).card + 1) 0
      ⟨goal, goal⟩ (by simp [remaining])
  exact ⟨after, counter, completed, positive, by simpa using upper, quiet,
    fun vertex => completed_until edges holds goal _ after counter completed vertex⟩

namespace Controls

theorem empty_goal_has_one_quiet_round :
    run ([] : List (Nat × Nat)) [] 1 0 ⟨[], []⟩ = some (⟨[], []⟩, 1) := rfl

theorem duplicate_seed_occurrences_survive :
    run ([] : List (Nat × Nat)) [] 1 0 ⟨[7, 7], [7, 7]⟩ = some (⟨[7, 7], []⟩, 1) := rfl

theorem productive_then_quiet_counts_both :
    run [(0, 1)] [0] 2 0 ⟨[1], [1]⟩ = some (⟨[1, 0], []⟩, 2) := rfl

theorem productive_round_alone_does_not_complete :
    run [(0, 1)] [0] 1 0 ⟨[1], [1]⟩ = none := by decide

theorem duplicate_occurrences_are_charged :
    allowance [(0, 1)] [0, 0] ⟨[1], [1, 1]⟩ = 9 ∧
      (candidates [(0, 1)] [0, 0] [1, 1]).length = 4 := by decide

theorem support_only_frontier_budget_is_insufficient :
    allowance [(0, 1)] [0, 0] (advance [(0, 1)] [0, 0] ⟨[1], [1, 1]⟩) +
        (candidates [(0, 1)] [0, 0] [1, 1]).length + 2 >
      (([1, 1] : List Nat).toFinset.card + (remaining [0, 0] ⟨[1], [1, 1]⟩).card) * (1 * 2 + 1) := by decide

end Controls

#print axioms advance_decreases
#print axioms run_complete_of_rank_lt
#print axioms finite_completion
#print axioms remaining_balance
#print axioms allowance_advance

end Mettapedia.Machines.CTLUntilFiniteSupport
