import Mettapedia.Machines.Cursor.SemanticTermView

/-!
# Partial semantic observations as a complete retrieval filter

An observation cache records facts about logical views, not physical tags.
`none` means not inspected or not loaded. `some unknown` records an open
variable/tail. `some absent` is a proved structural absence. Only the last
case may refute a required path; lack of metadata cannot do that.

The executable filter, incremental fill, eviction and row replacement are
implemented below. The exact original resolver's answers and multiplicities
survive filtering. Dynamic representation changes may retain observations
when their meanings agree. A changed logical row invalidates its own entries.

This instantiates retrieval for the finite free-constructor view profile.
It does not run or erase arbitrary effectful code while indexing, prove a
native dictionary implementation, or identify observation caches with row
ownership. Source iteration is preserved by this filter; an answer-order
promise is not thereby imposed on a dialect whose answers are bags.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.PartialViewIndex

open SemanticTermView

abbrev Store := Nat → Focus
abbrev Cache := Nat → Path → Option Observation

def empty : Cache := fun _ _ => none

def Valid (store : Store) (cache : Cache) : Prop :=
  ∀ occurrence path fact, cache occurrence path = some fact →
    fact = observe (store occurrence) path

def permits (query : Observation) : Option Observation → Bool
  | none => true
  | some fact => compatible query fact

def candidate (query : Focus) (paths : List Path) (cache : Cache) (occurrence : Nat) : Bool :=
  paths.all fun path => permits (observe query path) (cache occurrence path)

def candidates (query : Focus) (paths : List Path) (cache : Cache)
    (occurrences : List Nat) : List Nat := occurrences.filter (candidate query paths cache)

theorem empty_valid (store : Store) : Valid store empty := by
  intro occurrence path fact found
  cases found

/-- Fill computes a genuine logical observation at one requested coordinate.
It does not mark every other coordinate as absent or complete. -/
def fill (store : Store) (cache : Cache) (occurrence : Nat) (path : Path) : Cache :=
  let fact := observe (store occurrence) path
  fun row probe => if row = occurrence ∧ probe = path then some fact
    else cache row probe

theorem fill_valid (store : Store) (cache : Cache) (valid : Valid store cache)
    (occurrence : Nat) (path : Path) : Valid store (fill store cache occurrence path) := by
  intro row probe fact found
  by_cases same : row = occurrence ∧ probe = path
  · rcases same with ⟨rfl, rfl⟩
    simpa [fill] using found.symm
  · simp only [fill, if_neg same] at found
    exact valid row probe fact found

def evict (cache : Cache) (occurrence : Nat) (path : Path) : Cache :=
  fun row probe => if row = occurrence ∧ probe = path then none else cache row probe

theorem evict_valid (store : Store) (cache : Cache) (valid : Valid store cache)
    (occurrence : Nat) (path : Path) : Valid store (evict cache occurrence path) := by
  intro row probe fact found
  by_cases same : row = occurrence ∧ probe = path
  · simp [evict, same] at found
  · exact valid row probe fact (by simpa [evict, same] using found)

def invalidate (cache : Cache) (occurrence : Nat) : Cache :=
  fun row probe => if row = occurrence then none else cache row probe

theorem replace_valid (store : Store) (cache : Cache) (valid : Valid store cache)
    (occurrence : Nat) (value : Focus) :
    Valid (Function.update store occurrence value) (invalidate cache occurrence) := by
  intro row probe fact found
  by_cases same : row = occurrence
  · simp [invalidate, same] at found
  · simp only [invalidate, if_neg same] at found
    simpa [Function.update_of_ne same] using valid row probe fact found

/-- Physical replacement is free to retain semantic metadata when its
logical values agree. No global store revision equality is required. -/
theorem transport_valid (before after : Store) (cache : Cache) (valid : Valid before cache)
    (same : ∀ occurrence, (before occurrence).denote = (after occurrence).denote) :
    Valid after cache := by
  intro occurrence path fact found
  exact (valid occurrence path fact found).trans
    (representation_invariant _ _ (same occurrence) path)

theorem candidate_of_unifier (store : Store) (cache : Cache) (valid : Valid store cache)
    (query : Focus) (paths : List Path) (occurrence : Nat)
    (matched : Unifies query.denote (store occurrence).denote) :
    candidate query paths cache occurrence = true := by
  apply List.all_eq_true.mpr
  intro path _
  cases fact : cache occurrence path with
  | none => rfl
  | some value =>
      change compatible (observe query path) value = true
      rw [valid occurrence path value fact]
      exact stored_unifier_not_refuted query (store occurrence) path matched

/-- A resolver can return bindings, values or other pure answer records.
All of its actual answers survive, including duplicate occurrences. -/
theorem resolver_answers_preserved {Answer : Type} (store : Store) (cache : Cache)
    (valid : Valid store cache) (query : Focus) (paths : List Path)
    (resolve : Nat → List Answer)
    (sound : ∀ occurrence answer, answer ∈ resolve occurrence →
      Unifies query.denote (store occurrence).denote)
    (occurrences : List Nat) :
    (candidates query paths cache occurrences).flatMap resolve = occurrences.flatMap resolve := by
  induction occurrences with
  | nil => rfl
  | cons occurrence later ih =>
      by_cases accepted : candidate query paths cache occurrence = true
      · simpa [candidates, List.filter_cons, accepted] using congrArg (resolve occurrence ++ ·) ih
      · have noAnswers : resolve occurrence = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro answer member
          exact accepted (candidate_of_unifier store cache valid query paths occurrence
            (sound occurrence answer member))
        simpa [candidates, List.filter_cons, accepted, noAnswers] using ih

theorem empty_keeps_every_occurrence (query : Focus) (paths : List Path) (occurrences : List Nat) :
    candidates query paths empty occurrences = occurrences := by
  simp [candidates, candidate, empty, permits]

/-- Information grows from uninspected to an observation. Once established,
a fact remains the same in this refinement relation. Logical edits instead
use invalidation or an appropriate new source identity. -/
def Refines (before after : Cache) : Prop :=
  ∀ occurrence path, before occurrence path = none ∨ after occurrence path = before occurrence path

theorem fill_refines (store : Store) (cache : Cache) (valid : Valid store cache)
    (occurrence : Nat) (path : Path) : Refines cache (fill store cache occurrence path) := by
  intro row probe
  by_cases same : row = occurrence ∧ probe = path
  · rcases same with ⟨rfl, rfl⟩
    cases found : cache row probe with
    | none => exact Or.inl rfl
    | some fact =>
        exact Or.inr (by simp [fill, valid row probe fact found])
  · exact Or.inr (by simp [fill, same])

theorem refined_candidate_was_candidate (before after : Cache) (refined : Refines before after)
    (query : Focus) (paths : List Path) (occurrence : Nat)
    (accepted : candidate query paths after occurrence = true) :
    candidate query paths before occurrence = true := by
  apply List.all_eq_true.mpr
  intro path member
  rcases refined occurrence path with unknown | same
  · simp [unknown, permits]
  · simpa [same] using List.all_eq_true.mp accepted path member

theorem refinement_keeps_only_candidates (before after : Cache) (refined : Refines before after)
    (query : Focus) (paths : List Path) (occurrences : List Nat) :
    candidates query paths after occurrences =
      (candidates query paths before occurrences).filter (candidate query paths after) := by
  simp only [candidates, List.filter_filter]
  apply List.filter_congr
  intro occurrence _
  by_cases accepted : candidate query paths after occurrence = true
  · simp [accepted, refined_candidate_was_candidate before after refined query paths occurrence accepted]
  · simp [accepted]

theorem refinement_candidate_count (before after : Cache) (refined : Refines before after)
    (query : Focus) (paths : List Path) (occurrences : List Nat) :
    (candidates query paths after occurrences).length ≤
      (candidates query paths before occurrences).length := by
  rw [refinement_keeps_only_candidates before after refined]
  exact List.length_filter_le _ _

namespace Controls

def seven : Focus := .value (.rigid (.symbol 7))
def eight : Focus := .value (.rigid (.symbol 8))
def openValue : Focus := .value (.var 0)

@[simp] theorem observe_seven : observe seven [] = .rigid (.symbol 7) := by
  rw [observe_correct]
  simp [seven, Focus.denote, Stored.denote, project]

@[simp] theorem observe_eight : observe eight [] = .rigid (.symbol 8) := by
  rw [observe_correct]
  simp [eight, Focus.denote, Stored.denote, project]

@[simp] theorem observe_open : observe openValue [] = .unknown := by
  rw [observe_correct]
  simp [openValue, Focus.denote, Stored.denote, project]

def store : Store
  | 0 => seven
  | 1 => eight
  | _ => openValue

def twoKnown : Cache := fill store (fill store empty 0 []) 1 []
def allKnown : Cache := fill store twoKnown 2 []

theorem observations_are_earned : Valid store allKnown :=
  fill_valid _ _ (fill_valid _ _ (fill_valid _ _ (empty_valid _) _ _) _ _) _ _

theorem one_unknown_row_does_not_disable_the_index :
    candidates seven [[]] twoKnown [0, 1, 2] = [0, 2] := by
  simp [candidates, candidate, twoKnown, fill, empty, store, permits, compatible]

theorem learning_an_open_tail_is_not_a_refutation :
    candidates seven [[]] allKnown [0, 1, 2] = [0, 2] := by
  simp [candidates, candidate, allKnown, twoKnown, fill, empty, store, permits, compatible]

theorem pending_is_not_absence :
    permits (.rigid (.symbol 7)) none = true ∧
      permits (.rigid (.symbol 7)) (some .absent) = false := by decide

theorem stale_cache_can_hide_a_valid_replacement :
    candidate seven [[]] twoKnown 1 = false ∧
      candidate seven [[]] (invalidate twoKnown 1) 1 = true ∧
      Unifies seven.denote (Function.update store 1 seven 1).denote := by
  refine ⟨?_, ?_, ⟨Term.var, Term.var, rfl⟩⟩
  · simp [candidate, twoKnown, fill, empty, store, permits, compatible]
  · simp [candidate, invalidate, permits]

theorem duplicate_occurrences_remain :
    candidates seven [[]] allKnown [0, 2, 0, 1] = [0, 2, 0] := by
  simp [candidates, candidate, allKnown, twoKnown, fill, empty, store, permits, compatible]

end Controls

end Mettapedia.Machines.Cursor.PartialViewIndex
