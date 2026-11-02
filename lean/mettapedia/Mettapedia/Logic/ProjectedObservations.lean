import Mathlib.Data.Set.Image
import Mettapedia.Logic.ConstructiveObservationReversals

/-! Set-valued specialization of the constructive observation laws.
Possibility and universal queries characterize the projected solution set;
private helpers may change its internal carrier, but not its observations. -/

set_option autoImplicit false

namespace Mettapedia.Logic.ProjectedObservations

variable {A B O : Type*}

def Possible (models : Set A) (observe : A → O) (query : O → Prop) : Prop :=
  ∃ model ∈ models, query (observe model)

def Necessary (models : Set A) (observe : A → O) (query : O → Prop) : Prop :=
  ∀ model ∈ models, query (observe model)

theorem image_eq_iff_possible (left : Set A) (right : Set B) (observeLeft : A → O) (observeRight : B → O) :
    observeLeft '' left = observeRight '' right ↔
      ∀ query, Possible left observeLeft query ↔ Possible right observeRight query := by
  rw [Set.ext_iff]
  exact ConstructiveObservationReversals.view_iff_all_possible left right observeLeft observeRight

theorem image_eq_iff_necessary (left : Set A) (right : Set B) (observeLeft : A → O) (observeRight : B → O) :
    observeLeft '' left = observeRight '' right ↔
      ∀ query, Necessary left observeLeft query ↔ Necessary right observeRight query := by
  rw [Set.ext_iff]
  exact ConstructiveObservationReversals.view_iff_all_necessary left right observeLeft observeRight

/-- Matching observations in both directions suffices even when private
helper assignments have entirely different representations. -/
theorem image_eq_of_matching (left : Set A) (right : Set B) (observeLeft : A → O) (observeRight : B → O)
    (forward : ∀ model ∈ left, ∃ other ∈ right, observeLeft model = observeRight other)
    (backward : ∀ model ∈ right, ∃ other ∈ left, observeRight model = observeLeft other) :
    observeLeft '' left = observeRight '' right := by
  apply Set.Subset.antisymm
  · exact Set.image_subset_iff.mpr (fun model member =>
      let ⟨other, present, same⟩ := forward model member
      ⟨other, present, same.symm⟩)
  · exact Set.image_subset_iff.mpr (fun model member =>
      let ⟨other, present, same⟩ := backward model member
      ⟨other, present, same.symm⟩)

def diagonal : Set (Bool × Bool) := {pair | pair.1 = pair.2}

theorem individual_marginals_do_not_determine_joint_view :
    Prod.fst '' diagonal = Prod.fst '' (Set.univ : Set (Bool × Bool)) ∧
    Prod.snd '' diagonal = Prod.snd '' (Set.univ : Set (Bool × Bool)) ∧
    diagonal ≠ Set.univ := by
  have diagonalPair (bit : Bool) : (bit, bit) ∈ diagonal := rfl
  refine ⟨?_, ?_, ?_⟩
  · exact image_eq_of_matching diagonal Set.univ Prod.fst Prod.fst
      (fun pair _ => ⟨pair, trivial, rfl⟩) (fun pair _ => ⟨(pair.1, pair.1), diagonalPair _, rfl⟩)
  · exact image_eq_of_matching diagonal Set.univ Prod.snd Prod.snd
      (fun pair _ => ⟨pair, trivial, rfl⟩) (fun pair _ => ⟨(pair.2, pair.2), diagonalPair _, rfl⟩)
  · intro same
    have impossible : (false, true) ∈ diagonal := same.symm ▸ Set.mem_univ _
    cases impossible

theorem unchanged_joint_view_preserves_all_queries (before after : Set A) (protectedView : A → O) :
    protectedView '' before = protectedView '' after ↔
      (∀ query, Possible before protectedView query ↔ Possible after protectedView query) ∧
      (∀ query, Necessary before protectedView query ↔ Necessary after protectedView query) := by
  rw [← image_eq_iff_possible, ← image_eq_iff_necessary, and_self]

/-- A private helper may be constrained without granting any write to the
observed caller. Projection preservation alone is not a one-way matcher. -/
theorem protected_view_does_not_forbid_internal_solving :
    let before : Set (Bool × Bool) := Set.univ
    let after : Set (Bool × Bool) := {state | state.2 = false}
    after ⊆ before ∧ after ≠ before ∧ Prod.fst '' before = Prod.fst '' after := by
  dsimp only
  refine ⟨Set.subset_univ _, ?_, ?_⟩
  · intro same
    have impossible : (false, true) ∈ ({state : Bool × Bool | state.2 = false} : Set (Bool × Bool)) :=
      same.symm ▸ Set.mem_univ _
    cases impossible
  · exact image_eq_of_matching _ _ Prod.fst Prod.fst
      (fun pair _ => ⟨(pair.1, false), rfl, rfl⟩) (fun pair _ => ⟨pair, trivial, rfl⟩)

end Mettapedia.Logic.ProjectedObservations
