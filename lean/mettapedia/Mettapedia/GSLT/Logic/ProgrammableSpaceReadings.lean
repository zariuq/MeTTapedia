import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings

/-!
# Current support and occurrence-sensitive material readings

The unordered support graph retains exactly membership among the declared
atom values. Its occurrence index is an actual list position. A separate
ordered graph retains the entire source list, including repeated values.
Neither reading assigns independent probabilistic evidence to its members.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceReadings

open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u
variable {Atom : Type u} (coding : ArgumentCoding Atom)

def supportGraph (atoms : List Atom) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup fun position : ULift.{u} (Fin atoms.length) =>
    coding.graph atoms[position.down]

def support (atoms : List Atom) : HSet.{u} := HSet.mk (supportGraph coding atoms)

theorem member_support_iff (atoms : List Atom) (value : HSet.{u}) :
    value ∈ support coding atoms ↔ ∃ atom ∈ atoms, coding.reading atom = value := by
  change value ∈ HSet.range (fun position : ULift.{u} (Fin atoms.length) =>
    coding.graph atoms[position.down]) ↔ _
  rw [HSet.mem_range]
  constructor
  · rintro ⟨position, same⟩
    exact ⟨atoms[position.down], List.getElem_mem position.down.isLt, same⟩
  · rintro ⟨atom, member, same⟩
    obtain ⟨position, atPosition⟩ := List.mem_iff_get.mp member
    exact ⟨⟨position⟩, (congrArg coding.reading atPosition).trans same⟩

theorem fact_member_iff (atoms : List Atom) (atom : Atom) :
    coding.reading atom ∈ support coding atoms ↔ atom ∈ atoms := by
  rw [member_support_iff]
  constructor
  · rintro ⟨other, member, same⟩
    exact coding.injective same ▸ member
  · intro member
    exact ⟨atom, member, rfl⟩

/-- This is an exact kernel theorem, not just forward preservation. -/
theorem support_eq_iff (first second : List Atom) :
    support coding first = support coding second ↔
      ∀ atom, atom ∈ first ↔ atom ∈ second := by
  constructor
  · intro same atom
    rw [← fact_member_iff coding first atom, ← fact_member_iff coding second atom, same]
  · intro same
    apply HSet.ext
    intro value
    rw [member_support_iff, member_support_iff]
    constructor
    · rintro ⟨atom, member, reads⟩
      exact ⟨atom, (same atom).mp member, reads⟩
    · rintro ⟨atom, member, reads⟩
      exact ⟨atom, (same atom).mpr member, reads⟩

def occurrences (atoms : List Atom) : HSet.{u} := coding.lists.reading atoms

theorem occurrences_eq_iff (first second : List Atom) :
    occurrences coding first = occurrences coding second ↔ first = second :=
  ⟨fun same => coding.lists.injective same, fun same => congrArg _ same⟩

theorem occurrences_determine_support (first second : List Atom)
    (same : occurrences coding first = occurrences coding second) :
    support coding first = support coding second :=
  congrArg (support coding) ((occurrences_eq_iff coding first second).mp same)

theorem duplicate_support (atom : Atom) :
    support coding [atom, atom] = support coding [atom] := by
  apply (support_eq_iff coding _ _).mpr
  intro other
  simp

theorem duplicate_occurrences (atom : Atom) :
    occurrences coding [atom, atom] ≠ occurrences coding [atom] := by
  intro same
  have lists := (occurrences_eq_iff coding _ _).mp same
  have sizes := congrArg List.length lists
  exact (by decide : ¬ (2 : Nat) = 1) sizes

theorem support_does_not_supply_occurrences (atom : Atom) :
    ¬ ∃ recover : HSet.{u} → HSet.{u},
      ∀ atoms : List Atom, recover (support coding atoms) = occurrences coding atoms := by
  rintro ⟨recover, correct⟩
  exact duplicate_occurrences coding atom
    ((correct [atom, atom]).symm.trans
      ((congrArg recover (duplicate_support coding atom)).trans (correct [atom])))

theorem permutation_support {first second : List Atom} (same : first.Perm second) :
    support coding first = support coding second :=
  (support_eq_iff coding first second).mpr (fun _ => same.mem_iff)

end Mettapedia.GSLT.ProgrammableSpaceReadings
