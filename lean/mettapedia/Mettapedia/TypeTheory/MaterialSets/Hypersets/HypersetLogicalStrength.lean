import Mettapedia.TypeTheory.MaterialSets.Hypersets.Operations

/-!
# Logical strength of equality and truth readouts

Separation of the singleton of the empty set represents every proposition by
an actual material subset. Its inhabitedness is that proposition, whereas
inequality with the empty set is only its double negation. Thus converting
absence of an empty-set equality into a membership witness is a logical
commitment, not an administrative readout operation.

An equality decision procedure on the entire hyperset carrier entails
excluded middle. So does the assertion that every material subset of a
singleton is either empty or the whole singleton. These are consequences of
the stated capabilities, not principles adopted by this development.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HypersetLogicalStrength

universe u

/-- The complete singleton subset selected by a proposition. -/
def truthSet (proposition : Prop) : HSet.{u} :=
  HSet.sep (fun _ => proposition) {∅}

theorem member_truthSet (proposition : Prop) (value : HSet.{u}) :
    value ∈ truthSet proposition ↔ value = ∅ ∧ proposition :=
  HSet.mem_sep.trans (and_congr HSet.mem_singleton Iff.rfl)

theorem empty_member_truthSet (proposition : Prop) :
    (∅ : HSet.{u}) ∈ truthSet proposition ↔ proposition :=
  (member_truthSet proposition ∅).trans (and_iff_right rfl)

theorem truthSet_inhabited (proposition : Prop) :
    (∃ value : HSet.{u}, value ∈ truthSet proposition) ↔ proposition := by
  constructor
  · rintro ⟨value, belongs⟩
    exact ((member_truthSet proposition value).mp belongs).2
  · intro holds
    exact ⟨∅, (empty_member_truthSet proposition).mpr holds⟩

theorem truthSet_eq_singleton (proposition : Prop) :
    truthSet proposition = ({∅} : HSet.{u}) ↔ proposition := by
  constructor
  · intro same
    apply (empty_member_truthSet proposition).mp
    exact same ▸ HSet.mem_singleton_self ∅
  · intro holds
    apply HSet.ext
    intro value
    exact (member_truthSet proposition value).trans
      ((and_iff_left holds).trans HSet.mem_singleton.symm)

theorem truthSet_eq_empty (proposition : Prop) :
    truthSet proposition = (∅ : HSet.{u}) ↔ ¬ proposition := by
  constructor
  · intro same holds
    exact HSet.notMem_empty ∅ (same ▸ (empty_member_truthSet proposition).mpr holds)
  · intro absent
    apply HSet.eq_empty_iff.mpr
    intro value belongs
    exact absent (((member_truthSet proposition value).mp belongs).2)

/-- Mere inequality with the empty value does not supply a member. -/
theorem truthSet_ne_empty (proposition : Prop) :
    truthSet proposition ≠ (∅ : HSet.{u}) ↔ ¬ ¬ proposition :=
  not_congr (truthSet_eq_empty proposition)

theorem truthSet_eq_iff (first second : Prop) :
    truthSet first = (truthSet second : HSet.{u}) ↔ (first ↔ second) := by
  constructor
  · intro same
    have observations : (∅ : HSet.{u}) ∈ truthSet first ↔ (∅ : HSet.{u}) ∈ truthSet second := by
      rw [same]
    exact (empty_member_truthSet first).symm.trans
      (observations.trans (empty_member_truthSet second))
  · intro agreement
    apply HSet.ext
    intro value
    exact (member_truthSet first value).trans
      ((and_congr Iff.rfl agreement).trans (member_truthSet second value).symm)

/-- This is an actual proposition decision computed from the supplied
material equality decision, rather than a choice of a propositional witness. -/
def propositionDecision (equality : DecidableEq HSet.{u}) (proposition : Prop) :
    Decidable proposition :=
  match equality (truthSet proposition) {∅} with
  | .isTrue same => .isTrue ((truthSet_eq_singleton proposition).mp same)
  | .isFalse different => .isFalse (fun holds =>
      different ((truthSet_eq_singleton proposition).mpr holds))

theorem excludedMiddle_of_decidableEquality (equality : DecidableEq HSet.{u}) :
    ∀ proposition : Prop, proposition ∨ ¬ proposition := by
  intro proposition
  cases propositionDecision equality proposition with
  | isTrue holds => exact Or.inl holds
  | isFalse absent => exact Or.inr absent

/-- Separating predicates need not make a singleton's power set consist of
just two material values in a constructive profile. -/
theorem truthSet_mem_powerset (proposition : Prop) :
    truthSet proposition ∈ HSet.powerset ({∅} : HSet.{u}) :=
  HSet.mem_powerset.mpr fun _ belongs => (HSet.mem_sep.mp belongs).1

theorem singleton_subsets_binary_iff_excludedMiddle :
    (∀ subset : HSet.{u}, subset ∈ HSet.powerset {∅} →
      subset = ∅ ∨ subset = {∅}) ↔
    (∀ proposition : Prop, proposition ∨ ¬ proposition) := by
  constructor
  · intro binary proposition
    rcases binary (truthSet proposition) (truthSet_mem_powerset proposition) with empty | whole
    · exact Or.inr ((truthSet_eq_empty proposition).mp empty)
    · exact Or.inl ((truthSet_eq_singleton proposition).mp whole)
  · intro excludedMiddle subset contained
    rcases excludedMiddle ((∅ : HSet.{u}) ∈ subset) with inhabited | absent
    · right
      apply HSet.ext
      intro value
      constructor
      · intro belongs
        exact (HSet.mem_powerset.mp contained) belongs
      · intro belongs
        exact (HSet.mem_singleton.mp belongs).symm ▸ inhabited
    · left
      apply HSet.eq_empty_iff.mpr
      intro value belongs
      have emptyValue := HSet.mem_singleton.mp ((HSet.mem_powerset.mp contained) belongs)
      exact absent (emptyValue ▸ belongs)

/-- Turning nonemptiness into positive membership for every truth set is
exactly double-negation elimination. -/
theorem nonempty_readout_reflection_iff_doubleNegationElimination :
    (∀ proposition : Prop, truthSet proposition ≠ (∅ : HSet.{u}) →
      (∅ : HSet.{u}) ∈ truthSet proposition) ↔
    (∀ proposition : Prop, (¬ ¬ proposition) → proposition) := by
  constructor
  · intro reflect proposition stable
    exact (empty_member_truthSet proposition).mp
      (reflect proposition ((truthSet_ne_empty proposition).mpr stable))
  · intro eliminate proposition nonempty
    exact (empty_member_truthSet proposition).mpr
      (eliminate proposition ((truthSet_ne_empty proposition).mp nonempty))

namespace Controls

theorem true_whole : truthSet True = ({∅} : HSet.{u}) :=
  (truthSet_eq_singleton True).mpr True.intro

theorem false_empty : truthSet False = (∅ : HSet.{u}) :=
  (truthSet_eq_empty False).mpr False.elim

theorem true_false_distinguished : truthSet True ≠ (truthSet False : HSet.{u}) := by
  rw [true_whole, false_empty]
  exact HSet.empty_ne_singleton_empty.symm

/-- A separated false reading has no positive member evidence. -/
theorem false_has_no_member : ¬ ∃ value : HSet.{u}, value ∈ truthSet False :=
  fun witness => (truthSet_inhabited False).mp witness

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HypersetLogicalStrength
