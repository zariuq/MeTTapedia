import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLift
import Mathlib.Logic.Small.Basic

/-!
# Membership recovery and set operations across universe lifting

The inverse on the members of a fixed lifted set is constructed by separation
from the original bound and union. It uses neither a graph selector nor
selection from an existential member. Every subset of a lifted set similarly
descends by separation from its original bound. This proves that lifting
preserves power sets and union, as well as the pairs proved in `UniverseLift`.

These are bounded recovery laws. They do not give a global inverse on the
larger carrier, whose proper extension was proved in `UniverseLift`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet

universe u

/-- Decode a member below a known original bound by its separated row. -/
def lowerMemberValue (X : HSet.{u}) (y : HSet.{u + 1}) : HSet.{u} :=
  sUnion (HSet.sep (fun x => lift x = y) X)

theorem lowerMemberValue_lift {X x : HSet.{u}} (member : x ∈ X) :
    lowerMemberValue X (lift x) = x := by
  have separated : HSet.sep (fun z => lift z = lift x) X = {x} := by
    ext z
    rw [mem_sep, mem_singleton]
    exact ⟨fun row => lift_injective row.2, fun same => ⟨same ▸ member, congrArg lift same⟩⟩
  rw [lowerMemberValue, separated, sUnion_singleton]

theorem lowerMemberValue_mem {X : HSet.{u}} {y : HSet.{u + 1}} (member : y ∈ lift X) :
    lowerMemberValue X y ∈ X := by
  obtain ⟨x, original, same⟩ := mem_lift_iff.mp member
  rw [← same, lowerMemberValue_lift original]
  exact original

theorem lift_lowerMemberValue {X : HSet.{u}} {y : HSet.{u + 1}} (member : y ∈ lift X) :
    lift (lowerMemberValue X y) = y := by
  obtain ⟨x, original, same⟩ := mem_lift_iff.mp member
  rw [← same, lowerMemberValue_lift original]

/-- An actual inverse on material members, constructed from the original
bound rather than supplied as occurrence-recovery data. -/
def liftedMembersEquiv (X : HSet.{u}) :
    {x : HSet.{u} // x ∈ X} ≃ {y : HSet.{u + 1} // y ∈ lift X} where
  toFun x := ⟨lift x.val, lift_mem_lift_iff.mpr x.property⟩
  invFun y := ⟨lowerMemberValue X y.val, lowerMemberValue_mem y.property⟩
  left_inv x := Subtype.ext (lowerMemberValue_lift x.property)
  right_inv y := Subtype.ext (lift_lowerMemberValue y.property)

@[simp] theorem liftedMembersEquiv_val (X : HSet.{u}) (x : {x : HSet.{u} // x ∈ X}) :
    (liftedMembersEquiv X x).val = lift x.val := rfl

theorem liftedMembersEquiv_small (X : HSet.{u}) :
    Small.{u + 1} {y : HSet.{u + 1} // y ∈ lift X} :=
  Small.mk' (liftedMembersEquiv X).symm

/-- Separation of the original bound recovers any subset at the larger
level, irrespective of the presentation size of that subset. -/
def lowerSubset (X : HSet.{u}) (Y : HSet.{u + 1}) : HSet.{u} :=
  HSet.sep (fun x => lift x ∈ Y) X

theorem lowerSubset_subset (X : HSet.{u}) (Y : HSet.{u + 1}) : lowerSubset X Y ⊆ X :=
  fun _ member => (mem_sep.mp member).1

theorem lift_lowerSubset {X : HSet.{u}} {Y : HSet.{u + 1}} (bounded : Y ⊆ lift X) :
    lift (lowerSubset X Y) = Y := by
  ext y
  rw [mem_lift_iff]
  constructor
  · rintro ⟨x, member, same⟩
    exact same ▸ (mem_sep.mp member).2
  · intro member
    obtain ⟨x, original, same⟩ := mem_lift_iff.mp (bounded member)
    exact ⟨x, mem_sep.mpr ⟨original, same.symm ▸ member⟩, same⟩

theorem lift_subset_iff {X Y : HSet.{u}} : lift X ⊆ lift Y ↔ X ⊆ Y := by
  constructor
  · intro bounded x member
    exact lift_mem_lift_iff.mp (bounded (lift_mem_lift_iff.mpr member))
  · intro bounded y member
    obtain ⟨x, original, same⟩ := mem_lift_iff.mp member
    exact mem_lift_iff.mpr ⟨x, bounded original, same⟩

/-- The larger power set adds no new subsets of a lifted bound: every one
is recovered by the proved bounded separation construction. -/
theorem lift_powerset (X : HSet.{u}) : lift (powerset X) = powerset (lift X) := by
  ext Y
  rw [mem_lift_iff, mem_powerset]
  constructor
  · rintro ⟨Z, member, same⟩
    exact same ▸ lift_subset_iff.mpr (mem_powerset.mp member)
  · intro bounded
    exact ⟨lowerSubset X Y, mem_powerset.mpr (lowerSubset_subset X Y),
      lift_lowerSubset bounded⟩

theorem lift_sUnion (X : HSet.{u}) : lift (sUnion X) = sUnion (lift X) := by
  ext y
  rw [mem_lift_iff, mem_sUnion]
  constructor
  · rintro ⟨x, member, same⟩
    obtain ⟨Z, original, contained⟩ := mem_sUnion.mp member
    exact ⟨lift Z, lift_mem_lift_iff.mpr original,
      mem_lift_iff.mpr ⟨x, contained, same⟩⟩
  · rintro ⟨Z, original, contained⟩
    obtain ⟨W, oldMember, same⟩ := mem_lift_iff.mp original
    obtain ⟨x, oldContained, pictured⟩ := mem_lift_iff.mp (same.symm ▸ contained)
    exact ⟨x, mem_sUnion.mpr ⟨W, oldMember, oldContained⟩, pictured⟩

/-- The original bound and value are preserved by bounded subset descent. -/
theorem lowerSubset_lift (X Y : HSet.{u}) : lowerSubset X (lift Y) = HSet.sep (· ∈ Y) X := by
  ext x
  rw [lowerSubset, mem_sep, mem_sep, lift_mem_lift_iff]

/-! ## A proper enclosure of the complete smaller carrier -/

/-- The larger level contains every smaller material value as a member. -/
def smallerCarrier : HSet.{u + 1} := imageUp (id : HSet.{u} → HSet.{u})

theorem mem_smallerCarrier_iff {y : HSet.{u + 1}} :
    y ∈ smallerCarrier.{u} ↔ ∃ x : HSet.{u}, lift x = y := mem_imageUp_iff

theorem lift_mem_smallerCarrier (x : HSet.{u}) : lift x ∈ smallerCarrier.{u} :=
  lift_mem_imageUp id x

theorem smallerCarrier_transitive {X y : HSet.{u + 1}}
    (outer : X ∈ smallerCarrier.{u}) (inner : y ∈ X) : y ∈ smallerCarrier.{u} := by
  obtain ⟨Z, same⟩ := mem_smallerCarrier_iff.mp outer
  obtain ⟨x, _, pictured⟩ := mem_lift_iff.mp (same.symm ▸ inner)
  exact mem_smallerCarrier_iff.mpr ⟨x, pictured⟩

theorem smallerCarrier_powerset {X : HSet.{u + 1}} (member : X ∈ smallerCarrier.{u}) :
    powerset X ∈ smallerCarrier.{u} := by
  obtain ⟨Y, same⟩ := mem_smallerCarrier_iff.mp member
  exact mem_smallerCarrier_iff.mpr ⟨powerset Y, (lift_powerset Y).trans (congrArg powerset same)⟩

theorem smallerCarrier_sUnion {X : HSet.{u + 1}} (member : X ∈ smallerCarrier.{u}) :
    sUnion X ∈ smallerCarrier.{u} := by
  obtain ⟨Y, same⟩ := mem_smallerCarrier_iff.mp member
  exact mem_smallerCarrier_iff.mpr ⟨sUnion Y, (lift_sUnion Y).trans (congrArg sUnion same)⟩

/-- The enclosure contains a non-well-founded value. It is therefore
different from a Grothendieck universe restricted to well-founded sets. -/
theorem quineAtom_mem_smallerCarrier : quineAtom.{u + 1} ∈ smallerCarrier.{u} := by
  rw [← lift_quineAtom]
  exact lift_mem_smallerCarrier quineAtom

theorem smallerCarrier_not_lifted : ¬ ∃ X : HSet.{u}, lift X = smallerCarrier.{u} := by
  rintro ⟨X, same⟩
  apply not_exists_universal
  refine ⟨X, fun x => ?_⟩
  apply lift_mem_lift_iff.mp
  rw [same]
  exact lift_mem_smallerCarrier x

#print axioms liftedMembersEquiv
#print axioms liftedMembersEquiv_small
#print axioms lift_powerset
#print axioms smallerCarrier_not_lifted

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet
