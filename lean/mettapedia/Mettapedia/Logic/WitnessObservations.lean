import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter

/-! Exact information requirements for observing finite witness collections.
Emptiness, cardinality and witness identity have different converses. A
witness can be an occurrence tuple for a conjunctive query; its identity is
retained even when several tuples have the same projected answer. -/

set_option autoImplicit false

namespace Mettapedia.Logic.WitnessObservations

variable {W : Type*}

/-- The semantic candidates that actually satisfy a query in one model. -/
def matchingWitnesses (candidate : Finset W) (predicate : W → Prop) [DecidablePred predicate] : Finset W :=
  candidate.filter predicate

/-- Every global witness is visible. This does not assert uniqueness. -/
def Covers (visible world : Finset W) (predicate : W → Prop) : Prop :=
  ∀ witness ∈ world, predicate witness → witness ∈ visible

theorem matchingWitnesses_subset (visible world : Finset W) (predicate : W → Prop) [DecidablePred predicate]
    (included : visible ⊆ world) : matchingWitnesses visible predicate ⊆ matchingWitnesses world predicate :=
  Finset.filter_subset_filter _ included

theorem covers_iff_matchingWitnesses_eq (visible world : Finset W) (predicate : W → Prop) [DecidablePred predicate]
    (included : visible ⊆ world) : Covers visible world predicate ↔ matchingWitnesses visible predicate = matchingWitnesses world predicate := by
  rw [Finset.Subset.antisymm_iff]
  simp only [matchingWitnesses_subset visible world predicate included, true_and]
  simp only [Finset.subset_iff, matchingWitnesses, Finset.mem_filter, Covers]
  exact ⟨fun covered witness found => ⟨covered witness found.1 found.2, found.2⟩,
    fun retained witness present accepted => (retained ⟨present, accepted⟩).1⟩

theorem covers_iff_count_eq (visible world : Finset W) (predicate : W → Prop) [DecidablePred predicate]
    (included : visible ⊆ world) :
    Covers visible world predicate ↔ (matchingWitnesses visible predicate).card = (matchingWitnesses world predicate).card := by
  rw [covers_iff_matchingWitnesses_eq visible world predicate included]
  exact ⟨congrArg Finset.card,
    fun same => Finset.eq_of_subset_of_card_le (matchingWitnesses_subset visible world predicate included) (by omega)⟩

theorem absence_iff_witness_retention (visible world : Finset W) (predicate : W → Prop) [DecidablePred predicate]
    (included : visible ⊆ world) :
    (matchingWitnesses visible predicate = ∅ ↔ matchingWitnesses world predicate = ∅) ↔
      ((matchingWitnesses world predicate).Nonempty → (matchingWitnesses visible predicate).Nonempty) := by
  have forward := fun found => Finset.Nonempty.mono
    (matchingWitnesses_subset visible world predicate included) found
  simp only [← Finset.not_nonempty_iff_eq_empty, not_iff_not]
  exact ⟨Iff.mpr, fun backward => ⟨forward, backward⟩⟩

/-- All witness-selective absence observations recover exact coverage. -/
theorem covers_iff_all_filtered_absence (visible world : Finset W) (predicate : W → Prop)
    (included : visible ⊆ world) :
    Covers visible world predicate ↔ ∀ test : W → Prop,
      (¬ ∃ witness ∈ visible, predicate witness ∧ test witness) ↔
      (¬ ∃ witness ∈ world, predicate witness ∧ test witness) := by
  classical
  constructor
  · intro covered test
    constructor
    · intro absent ⟨witness, member, accepted, observed⟩
      exact absent ⟨witness, covered witness member accepted, accepted, observed⟩
    · intro absent ⟨witness, member, accepted, observed⟩
      exact absent ⟨witness, included member, accepted, observed⟩
  · intro observations witness member accepted
    by_contra omitted
    have noneVisible : ¬ ∃ value ∈ visible, predicate value ∧ value = witness := by
      rintro ⟨value, present, _, rfl⟩
      exact omitted present
    exact (observations (· = witness)).mp noneVisible ⟨witness, member, accepted, rfl⟩

theorem absence_does_not_force_coverage :
    let visible : Finset Bool := {false}
    let world : Finset Bool := {false, true}
    visible ⊆ world ∧
      (matchingWitnesses visible (fun _ => True) = ∅ ↔ matchingWitnesses world (fun _ => True) = ∅) ∧
      ¬ Covers visible world (fun _ => True) ∧
      (matchingWitnesses visible (fun _ => True)).card = 1 ∧ (matchingWitnesses world (fun _ => True)).card = 2 := by
  simp only [Covers]
  decide +kernel

theorem missing_only_witness_changes_absence :
    matchingWitnesses (∅ : Finset Bool) (· = true) = ∅ ∧ matchingWitnesses {true} (· = true) ≠ ∅ := by
  decide +kernel

end Mettapedia.Logic.WitnessObservations
