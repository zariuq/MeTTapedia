import Mettapedia.Machines.SemiNaiveInsertSaturation
import Mettapedia.Logic.CTLFixedPoints

/-!
# Finite predecessor frontiers for existential until

The edge-driven implementation is independent of the Horn round worker.
Unary positive rules provide a proved bridge to that worker and to the
independent finite-path meaning of EU. This is an instance for positive
until, not a reduction of EG, effects or arbitrary revision to Horn closure.

The state records Boolean support and fresh-state counts. Stored occurrence
bags, producer counts and a PeTTa driver's operational correspondence are
separate observations and are not erased by these theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CTLUntilFrontier

open Mettapedia.Logic
open RecursiveInsert

variable {Vertex : Type} [DecidableEq Vertex]

def rule (edge : Vertex × Vertex) : LP.PropRule Vertex := ⟨{edge.2}, edge.1⟩

def rules (edges : Finset (Vertex × Vertex)) (holds : Finset Vertex) : LP.PropProgram Vertex :=
  (edges.filter fun edge => edge.1 ∈ holds).image rule

def Relation (edges : Finset (Vertex × Vertex)) (before after : Vertex) : Prop := (before, after) ∈ edges

theorem derivable_iff_until (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) (state : Vertex) :
    LP.Derivable (rules edges holds) goal state ↔ CTLFixedPoints.Until (Relation edges) ↑holds ↑goal state := by
  constructor
  · intro derived
    induction derived with
    | fact member => exact .reached member
    | @rule chosen member premises ih =>
        obtain ⟨edge, enabled, rfl⟩ := Finset.mem_image.mp member
        obtain ⟨edgePresent, holding⟩ := Finset.mem_filter.mp enabled
        exact .advance holding edgePresent (ih edge.2 (by simp [rule]))
  · intro path
    induction path with
    | reached member => exact .fact member
    | @advance state next holding edge later ih =>
        apply LP.Derivable.rule (r := rule (state, next))
        · exact Finset.mem_image.mpr ⟨(state, next), Finset.mem_filter.mpr ⟨edge, holding⟩, rfl⟩
        · intro vertex member
          have same : vertex = next := by simpa [rule] using member
          simpa [same] using ih

def heads (edges : Finset (Vertex × Vertex)) (holds delta : Finset Vertex) : Finset Vertex :=
  (edges.filter fun edge => edge.1 ∈ holds ∧ edge.2 ∈ delta).image Prod.fst

theorem mem_heads (edges : Finset (Vertex × Vertex)) (holds delta : Finset Vertex) (state : Vertex) :
    state ∈ heads edges holds delta ↔ state ∈ holds ∧ ∃ next ∈ delta, (state, next) ∈ edges := by
  simp only [heads, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨prior, next⟩, ⟨edge, holding, active⟩, same⟩
    change prior = state at same
    subst prior
    exact ⟨holding, next, active, edge⟩
  · rintro ⟨holding, next, active, edge⟩
    exact ⟨(state, next), ⟨edge, holding, active⟩, rfl⟩

theorem heads_eq_seminaive (edges : Finset (Vertex × Vertex)) (holds : Finset Vertex)
    (state : SemiNaive.State Vertex) (included : state.delta ⊆ state.known) :
    heads edges holds state.delta = SemiNaive.heads (rules edges holds) state := by
  ext vertex
  rw [mem_heads, SemiNaive.mem_heads]
  constructor
  · rintro ⟨holding, next, active, edge⟩
    refine ⟨rule (vertex, next), Finset.mem_image.mpr ⟨(vertex, next),
      Finset.mem_filter.mpr ⟨edge, holding⟩, rfl⟩, ?_, ?_, rfl⟩
    · simpa [rule] using included active
    · exact Or.inr ⟨next, by simp [rule], active⟩
  · rintro ⟨chosen, member, _enabled, hot, same⟩
    obtain ⟨edge, allowed, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨edgePresent, holding⟩ := Finset.mem_filter.mp allowed
    have active : edge.2 ∈ state.delta := by simpa [SemiNaive.hot, rule] using hot
    change edge.1 = vertex at same
    subst vertex
    exact ⟨holding, edge.2, active, edgePresent⟩

def advance (edges : Finset (Vertex × Vertex)) (holds : Finset Vertex)
    (state : SemiNaive.State Vertex) : SemiNaive.State Vertex :=
  let fresh := heads edges holds state.delta \ state.known
  ⟨state.known ∪ fresh, fresh⟩

theorem advance_eq_seminaive (edges : Finset (Vertex × Vertex)) (holds : Finset Vertex)
    (state : SemiNaive.State Vertex) (included : state.delta ⊆ state.known) :
    advance edges holds state = SemiNaive.round (rules edges holds) state := by
  simp only [advance, SemiNaive.round, heads_eq_seminaive edges holds state included]

def rounds (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) : Nat → SemiNaive.State Vertex
  | 0 => ⟨goal, goal⟩
  | n + 1 => advance edges holds (rounds edges holds goal n)

theorem rounds_eq_seminaive (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) (n : Nat) :
    rounds edges holds goal n = SemiNaive.rounds (rules edges holds) goal n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change advance edges holds (rounds edges holds goal n) = SemiNaive.round _ _
      rw [ih, advance_eq_seminaive _ _ _ (SemiNaive.rounds_invariant _ _ n).delta_known]

theorem rounds_invariant (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) (n : Nat) :
    SemiNaive.Invariant (rules edges holds) (rounds edges holds goal n) := by
  rw [rounds_eq_seminaive]
  exact SemiNaive.rounds_invariant _ _ _

def progress (edges : Finset (Vertex × Vertex)) (holds : Finset Vertex) (state : SemiNaive.State Vertex) : Nat :=
  (advance edges holds state).delta.card

theorem growth (edges : Finset (Vertex × Vertex)) (holds : Finset Vertex) (state : SemiNaive.State Vertex) :
    (advance edges holds state).known.card = state.known.card + progress edges holds state := by
  exact Finset.card_union_of_disjoint Finset.sdiff_disjoint.symm

theorem no_repeated_delta (edges : Finset (Vertex × Vertex)) (holds : Finset Vertex) (state : SemiNaive.State Vertex) :
    Disjoint (advance edges holds state).delta state.known := Finset.sdiff_disjoint

theorem rounds_sound (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) (n : Nat) (state : Vertex)
    (present : state ∈ (rounds edges holds goal n).known) :
    CTLFixedPoints.Until (Relation edges) ↑holds ↑goal state := by
  rw [rounds_eq_seminaive, SemiNaive.rounds_eq_iterate] at present
  exact (derivable_iff_until edges holds goal state).mp (LP.iterate_sound _ _ n state present)

theorem quiet_support (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) (n : Nat)
    (quiet : (rounds edges holds goal n).delta = ∅) (state : Vertex) :
    state ∈ (rounds edges holds goal n).known ↔ CTLFixedPoints.Until (Relation edges) ↑holds ↑goal state := by
  constructor
  · exact rounds_sound edges holds goal n state
  · intro path
    have derived := (derivable_iff_until edges holds goal state).mpr path
    apply LP.derivable_subset_of_closed (rules edges holds) goal (rounds edges holds goal n).known _ _ state derived
    · rw [rounds_eq_seminaive, SemiNaive.rounds_eq_iterate]
      exact LP.iterate_mono _ _ (Nat.zero_le n)
    · intro chosen member enabled
      rcases (rounds_invariant edges holds goal n).old_complete chosen member enabled with hot | held
      · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp member
        simp [SemiNaive.hot, rule, quiet] at hot
      · exact held

def run (edges : Finset (Vertex × Vertex)) (holds : Finset Vertex) :
    Nat → Nat → SemiNaive.State Vertex → Option (SemiNaive.State Vertex × Nat)
  | 0, _, _ => none
  | fuel + 1, counter, state =>
      let next := advance edges holds state
      if next.delta = ∅ then some (next, counter + 1)
      else run edges holds fuel (counter + 1) next

/-- The returned counter includes the quiet round. Every state is an actual
frontier iterate, not a final set reconstructed independently of the run. -/
theorem run_receipt (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex)
    (fuel counter : Nat) (after : SemiNaive.State Vertex) (result : Nat)
    (completed : run edges holds fuel counter (rounds edges holds goal counter) = some (after, result)) :
    counter < result ∧ result ≤ counter + fuel ∧ after = rounds edges holds goal result ∧ after.delta = ∅ := by
  induction fuel generalizing counter after result with
  | zero => cases completed
  | succ fuel ih =>
      simp only [run] at completed
      split at completed
      next quiet =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
        exact ⟨by omega, by omega, rfl, quiet⟩
      next productive =>
        obtain ⟨lower, upper, reached, quiet⟩ := ih (counter + 1) after result completed
        exact ⟨by omega, by omega, reached, quiet⟩

theorem run_until (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex)
    (fuel : Nat) (after : SemiNaive.State Vertex) (result : Nat)
    (completed : run edges holds fuel 0 ⟨goal, goal⟩ = some (after, result)) (state : Vertex) :
    state ∈ after.known ↔ CTLFixedPoints.Until (Relation edges) ↑holds ↑goal state := by
  obtain ⟨_, _, reached, quiet⟩ := run_receipt edges holds goal fuel 0 after result completed
  subst after
  exact quiet_support edges holds goal result quiet state

theorem stop_by_quiet (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex)
    (remaining counter : Nat)
    (quiet : progress edges holds (rounds edges holds goal (counter + remaining)) = 0) :
    ∃ after result, run edges holds (remaining + 1) counter (rounds edges holds goal counter) = some (after, result) := by
  induction remaining generalizing counter with
  | zero =>
      have empty : (advance edges holds (rounds edges holds goal counter)).delta = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [progress] using quiet
      exact ⟨advance edges holds (rounds edges holds goal counter), counter + 1, by rw [run, if_pos empty]⟩
  | succ remaining ih =>
      by_cases empty : (advance edges holds (rounds edges holds goal counter)).delta = ∅
      · exact ⟨advance edges holds (rounds edges holds goal counter), counter + 1, by rw [run, if_pos empty]⟩
      · have laterQuiet : progress edges holds (rounds edges holds goal (counter + 1 + remaining)) = 0 := by
          simpa only [Nat.add_assoc, Nat.add_comm 1 remaining] using quiet
        obtain ⟨after, result, completed⟩ := ih (counter + 1) laterQuiet
        refine ⟨after, result, ?_⟩
        rw [run, if_neg empty]
        exact completed

section Finite

variable [Fintype Vertex]

theorem final_support (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) (state : Vertex) :
    state ∈ (rounds edges holds goal (LP.maxSteps (α := Vertex))).known ↔
      CTLFixedPoints.Until (Relation edges) ↑holds ↑goal state := by
  rw [rounds_eq_seminaive, SemiNaive.rounds_eq_iterate]
  exact (LP.saturate_iff_derivable _ _ state).trans (derivable_iff_until edges holds goal state)

theorem bounded_quiet_round (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) :
    progress edges holds (rounds edges holds goal (LP.maxSteps (α := Vertex))) = 0 := by
  have emptyDelta := SemiNaive.bounded_delta_empty (rules edges holds) goal
  have next : advance edges holds (rounds edges holds goal (LP.maxSteps (α := Vertex))) =
      SemiNaive.rounds (rules edges holds) goal (LP.maxSteps (α := Vertex) + 1) :=
    rounds_eq_seminaive edges holds goal (LP.maxSteps (α := Vertex) + 1)
  simp only [progress, next, emptyDelta, Finset.card_empty]

theorem finite_completion (edges : Finset (Vertex × Vertex)) (holds goal : Finset Vertex) :
    ∃ after counter,
      run edges holds (LP.maxSteps (α := Vertex) + 1) 0 ⟨goal, goal⟩ = some (after, counter) ∧
      0 < counter ∧ counter ≤ LP.maxSteps (α := Vertex) + 1 ∧ after.delta = ∅ ∧
      ∀ state, state ∈ after.known ↔ CTLFixedPoints.Until (Relation edges) ↑holds ↑goal state := by
  obtain ⟨after, counter, completed⟩ := stop_by_quiet edges holds goal (LP.maxSteps (α := Vertex)) 0
    (by simpa using bounded_quiet_round edges holds goal)
  obtain ⟨positive, bound, _, quiet⟩ := run_receipt edges holds goal _ 0 after counter completed
  exact ⟨after, counter, completed, positive, by simpa using bound, quiet,
    fun state => run_until edges holds goal _ after counter completed state⟩

end Finite

end Mettapedia.Machines.CTLUntilFrontier
