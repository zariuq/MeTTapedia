import Mettapedia.Machines.CTLUntilFrontier
import Mettapedia.Machines.OrderedInsertGuardBatch

/-!
# Ordered EU candidate bags and fresh frontiers

The nested scan preserves frontier, edge and predicate occurrences. The
existing ordered guard planner identifies the first still-absent candidate;
only then may Boolean support forget repeated producers. Existing known
rows may contain duplicates and remain unchanged. This is the bag-to-frontier
square, not a source-evaluator adequacy or physical cost theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CTLUntilCandidateBag

open Mettapedia.Logic
open OrderedInsertGuardBatch (Token plan)

variable {Vertex : Type} [DecidableEq Vertex]

def fresh (candidates : List Vertex) (known : Finset Vertex) : List Vertex :=
  (plan candidates known).filterMap fun token => match token with
    | .fresh vertex => some vertex
    | .present _ => none

@[simp] theorem fresh_nil (known : Finset Vertex) : fresh [] known = [] := rfl

theorem fresh_cons (vertex : Vertex) (rest : List Vertex) (known : Finset Vertex) :
    fresh (vertex :: rest) known =
      if vertex ∈ known then fresh rest known else vertex :: fresh rest (insert vertex known) := by
  by_cases held : vertex ∈ known <;> simp [fresh, plan, held]

theorem mem_fresh (vertex : Vertex) (candidates : List Vertex) (known : Finset Vertex) :
    vertex ∈ fresh candidates known ↔ vertex ∈ candidates ∧ vertex ∉ known := by
  induction candidates generalizing known with
  | nil => simp
  | cons first rest ih =>
      rw [fresh_cons]
      by_cases held : first ∈ known
      · simp only [if_pos held, ih, List.mem_cons]
        aesop
      · simp only [if_neg held, List.mem_cons, ih, Finset.mem_insert]
        by_cases same : vertex = first <;> aesop

theorem fresh_nodup (candidates : List Vertex) (known : Finset Vertex) :
    (fresh candidates known).Nodup := by
  induction candidates generalizing known with
  | nil => simp
  | cons first rest ih =>
      rw [fresh_cons]
      split
      · exact ih known
      · apply List.nodup_cons.mpr
        exact ⟨by simp [mem_fresh], ih (insert first known)⟩

theorem fresh_support (candidates : List Vertex) (known : Finset Vertex) :
    (fresh candidates known).toFinset = candidates.toFinset \ known := by
  ext vertex
  simp [mem_fresh]

/-- Publishing the fresh occurrences reaches the same support as retaining
all candidate occurrences, without reintroducing already known rows. -/
theorem known_union_fresh (candidates : List Vertex) (known : Finset Vertex) :
    known ∪ (fresh candidates known).toFinset = known ∪ candidates.toFinset := by
  rw [fresh_support]
  exact Finset.union_sdiff_self_eq_union

/-- The suffix tests membership after the prefix's publications. Authored
order survives splitting, including candidates repeated across the boundary. -/
theorem fresh_append (first later : List Vertex) (known : Finset Vertex) :
    fresh (first ++ later) known =
      fresh first known ++ fresh later (known ∪ first.toFinset) := by
  induction first generalizing known with
  | nil => simp
  | cons vertex rest ih =>
    rw [List.cons_append, fresh_cons, fresh_cons]
    by_cases held : vertex ∈ known
    · have same : known ∪ (vertex :: rest).toFinset = known ∪ rest.toFinset := by
        ext value
        simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
        aesop
      rw [if_pos held, if_pos held, same, ih]
    · have same : insert vertex known ∪ rest.toFinset = known ∪ (vertex :: rest).toFinset := by
        ext value
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
        aesop
      rw [if_neg held, if_neg held, ih, same, List.cons_append]

/-- Stored known rows keep their original multiplicity. Only their support
is used when the next authored chunk decides which occurrences are fresh. -/
theorem fresh_append_known (initialKnown first later : List Vertex) :
    fresh (first ++ later) initialKnown.toFinset =
      fresh first initialKnown.toFinset ++
        fresh later (initialKnown ++ fresh first initialKnown.toFinset).toFinset := by
  rw [fresh_append, List.toFinset_append, known_union_fresh]

theorem fresh_count (candidates : List Vertex) (known : Finset Vertex) :
    (fresh candidates known).length = (candidates.toFinset \ known).card := by
  rw [← fresh_support, List.toFinset_card_of_nodup (fresh_nodup candidates known)]

/-- Authored order: current frontier, reverse-edge matches, predicate matches.
The edge carrier is `(prior, next)`, even though the source reverse-edge row
stores the two fields in the opposite order. -/
def candidates (edges : List (Vertex × Vertex)) (holds delta : List Vertex) : List Vertex :=
  delta.flatMap fun next => edges.flatMap fun edge =>
    if edge.2 = next then holds.filter (fun prior => prior == edge.1) else []

theorem mem_candidates (edges : List (Vertex × Vertex)) (holds delta : List Vertex) (vertex : Vertex) :
    vertex ∈ candidates edges holds delta ↔
      vertex ∈ holds ∧ ∃ next ∈ delta, (vertex, next) ∈ edges := by
  simp only [candidates, List.mem_flatMap]
  constructor
  · rintro ⟨next, active, edge, stored, selected⟩
    split at selected
    next follows =>
      obtain ⟨holding, same⟩ : vertex ∈ holds ∧ vertex = edge.1 := by simpa using selected
      have sameEdge : edge = (vertex, next) := Prod.ext same.symm follows
      exact ⟨holding, next, active, sameEdge ▸ stored⟩
    next => simp at selected
  · rintro ⟨holding, next, active, edge⟩
    exact ⟨next, active, (vertex, next), edge, by simp [holding]⟩

theorem candidate_support (edges : List (Vertex × Vertex)) (holds delta : List Vertex) :
    (candidates edges holds delta).toFinset =
      CTLUntilFrontier.heads edges.toFinset holds.toFinset delta.toFinset := by
  ext vertex
  simp only [List.mem_toFinset, mem_candidates, CTLUntilFrontier.mem_heads]

structure State (Vertex : Type) where
  known : List Vertex
  delta : List Vertex

def State.support (state : State Vertex) : RecursiveInsert.SemiNaive.State Vertex :=
  ⟨state.known.toFinset, state.delta.toFinset⟩

def advance (edges : List (Vertex × Vertex)) (holds : List Vertex) (state : State Vertex) : State Vertex :=
  let added := fresh (candidates edges holds state.delta) state.known.toFinset
  ⟨state.known ++ added, added⟩

theorem advance_support (edges : List (Vertex × Vertex)) (holds : List Vertex) (state : State Vertex) :
    (advance edges holds state).support =
      CTLUntilFrontier.advance edges.toFinset holds.toFinset state.support := by
  apply RecursiveInsert.SemiNaive.State.ext <;>
    simp [advance, State.support, CTLUntilFrontier.advance, fresh_support, candidate_support]

theorem advance_fresh_count (edges : List (Vertex × Vertex)) (holds : List Vertex) (state : State Vertex) :
    (advance edges holds state).delta.length =
      CTLUntilFrontier.progress edges.toFinset holds.toFinset state.support := by
  simp [advance, fresh_count, candidate_support, CTLUntilFrontier.progress,
    CTLUntilFrontier.advance, State.support]

theorem advance_keeps_old_occurrences (edges : List (Vertex × Vertex)) (holds : List Vertex) (state : State Vertex) :
    (advance edges holds state).known = state.known ++ (advance edges holds state).delta := rfl

theorem advance_new_occurrences_distinct (edges : List (Vertex × Vertex)) (holds : List Vertex) (state : State Vertex) :
    (advance edges holds state).delta.Nodup := fresh_nodup _ _

theorem quiet_iff_complete_candidates (edges : List (Vertex × Vertex)) (holds : List Vertex) (state : State Vertex) :
    (advance edges holds state).delta = [] ↔
      CTLUntilFrontier.heads edges.toFinset holds.toFinset state.delta.toFinset ⊆ state.known.toFinset := by
  rw [← List.toFinset_eq_empty_iff]
  change (fresh (candidates edges holds state.delta) state.known.toFinset).toFinset = ∅ ↔ _
  rw [fresh_support, candidate_support, Finset.sdiff_eq_empty_iff_subset]

def run (edges : List (Vertex × Vertex)) (holds : List Vertex) :
    Nat → Nat → State Vertex → Option (State Vertex × Nat)
  | 0, _, _ => none
  | fuel + 1, counter, state =>
      let next := advance edges holds state
      if next.delta = [] then some (next, counter + 1)
      else run edges holds fuel (counter + 1) next

/-- The ordered worker retains its bag and the quiet-round counter. Mapping
the result to support, rather than replacing its stored rows, gives the finite
frontier execution exactly. -/
theorem run_support (edges : List (Vertex × Vertex)) (holds : List Vertex)
    (fuel counter : Nat) (state : State Vertex) :
    (run edges holds fuel counter state).map (fun result => (result.1.support, result.2)) =
      CTLUntilFrontier.run edges.toFinset holds.toFinset fuel counter state.support := by
  induction fuel generalizing counter state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run, CTLUntilFrontier.run, ← advance_support]
      change (if (advance edges holds state).delta = [] then
        some (advance edges holds state, counter + 1) else
        run edges holds fuel (counter + 1) (advance edges holds state)).map _ =
        if (advance edges holds state).delta.toFinset = ∅ then
          some ((advance edges holds state).support, counter + 1) else _
      simp only [List.toFinset_eq_empty_iff]
      split
      · rfl
      · exact ih (counter + 1) (advance edges holds state)

theorem completed_until (edges : List (Vertex × Vertex)) (holds goal : List Vertex)
    (fuel : Nat) (after : State Vertex) (counter : Nat)
    (completed : run edges holds fuel 0 ⟨goal, goal⟩ = some (after, counter)) (vertex : Vertex) :
    vertex ∈ after.known ↔ CTLFixedPoints.Until
      (CTLUntilFrontier.Relation edges.toFinset) ↑holds.toFinset ↑goal.toFinset vertex := by
  have abstractRun := run_support edges holds fuel 0 ⟨goal, goal⟩
  rw [completed] at abstractRun
  simpa only [State.support, List.mem_toFinset] using
    CTLUntilFrontier.run_until edges.toFinset holds.toFinset goal.toFinset fuel after.support counter
      abstractRun.symm vertex

theorem finite_completion [Fintype Vertex] (edges : List (Vertex × Vertex)) (holds goal : List Vertex) :
    ∃ after counter,
      run edges holds (LP.maxSteps (α := Vertex) + 1) 0 ⟨goal, goal⟩ = some (after, counter) ∧
      0 < counter ∧ counter ≤ LP.maxSteps (α := Vertex) + 1 ∧ after.delta = [] ∧
      ∀ vertex, vertex ∈ after.known ↔ CTLFixedPoints.Until
        (CTLUntilFrontier.Relation edges.toFinset) ↑holds.toFinset ↑goal.toFinset vertex := by
  obtain ⟨abstractAfter, counter, completed, positive, bound, quiet, _meaning⟩ :=
    CTLUntilFrontier.finite_completion edges.toFinset holds.toFinset goal.toFinset
  have mapped := run_support edges holds (LP.maxSteps (α := Vertex) + 1) 0 ⟨goal, goal⟩
  change CTLUntilFrontier.run edges.toFinset holds.toFinset (LP.maxSteps (α := Vertex) + 1) 0
    (⟨goal, goal⟩ : State Vertex).support = some (abstractAfter, counter) at completed
  rw [completed] at mapped
  obtain ⟨⟨after, answer⟩, actual, same⟩ := Option.map_eq_some_iff.mp mapped
  obtain ⟨support, rfl⟩ := Prod.mk.inj same
  refine ⟨after, answer, actual, positive, bound, ?_, ?_⟩
  · have empty : after.delta.toFinset = ∅ := (congrArg (·.delta) support).trans quiet
    exact (List.toFinset_eq_empty_iff _).mp empty
  · intro vertex
    exact completed_until edges holds goal _ after answer actual vertex

end Mettapedia.Machines.CTLUntilCandidateBag
