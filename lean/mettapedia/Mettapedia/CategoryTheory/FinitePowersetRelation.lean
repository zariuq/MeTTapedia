import Mettapedia.CategoryTheory.FinitePowerset

/-!
# Complete finite relation spans

Two-sided coverage constructs the entire finite relation between the
supplied finite sets. Its projections are exactly those sets. The
construction retains every matching pair instead of selecting one witness
for each input, and its relation condition need not be an equality kernel.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FinitePowersetRelation

open FinitePowerset

universe u v

variable {X : Type u} {Y : Type v} (relation : X → Y → Prop)

abbrev Pair := {coordinates : X × Y // relation coordinates.1 coordinates.2}

def first : Pair relation → X := fun pair => pair.val.1
def second : Pair relation → Y := fun pair => pair.val.2

def matching (left : Finset X) (right : Finset Y) : Finset (Pair relation) := by
  classical
  exact (left.product right).subtype (fun coordinates => relation coordinates.1 coordinates.2)

@[simp] theorem mem_matching (left : Finset X) (right : Finset Y)
    (pair : Pair relation) :
    pair ∈ matching relation left right ↔ pair.val.1 ∈ left ∧ pair.val.2 ∈ right := by
  classical
  simp only [matching, Finset.mem_subtype]
  exact Finset.mem_product

theorem matching_first (left : Finset X) (right : Finset Y)
    (covers : Related relation left right) :
    map (first relation) (matching relation left right) = left := by
  apply Finset.ext
  intro value
  rw [mem_map]
  constructor
  · rintro ⟨pair, member, rfl⟩
    exact ((mem_matching relation left right pair).mp member).1
  · intro member
    obtain ⟨other, otherMember, related⟩ := covers.1 value member
    refine ⟨⟨(value, other), related⟩, ?_, rfl⟩
    exact (mem_matching relation left right _).mpr ⟨member, otherMember⟩

theorem matching_second (left : Finset X) (right : Finset Y)
    (covers : Related relation left right) :
    map (second relation) (matching relation left right) = right := by
  apply Finset.ext
  intro other
  rw [mem_map]
  constructor
  · rintro ⟨pair, member, rfl⟩
    exact ((mem_matching relation left right pair).mp member).2
  · intro member
    obtain ⟨value, valueMember, related⟩ := covers.2 other member
    refine ⟨⟨(value, other), related⟩, ?_, rfl⟩
    exact (mem_matching relation left right _).mpr ⟨valueMember, member⟩

/-- Any finite span gives complete coverage of both of its images. -/
theorem span_related (pairs : Finset (Pair relation)) :
    Related relation (map (first relation) pairs) (map (second relation) pairs) := by
  constructor
  · intro value member
    obtain ⟨pair, pairMember, rfl⟩ := (mem_map _ _ _).mp member
    exact ⟨pair.val.2, (mem_map _ _ _).mpr ⟨pair, pairMember, rfl⟩, pair.property⟩
  · intro other member
    obtain ⟨pair, pairMember, rfl⟩ := (mem_map _ _ _).mp member
    exact ⟨pair.val.1, (mem_map _ _ _).mpr ⟨pair, pairMember, rfl⟩, pair.property⟩

theorem related_iff_span (left : Finset X) (right : Finset Y) :
    Related relation left right ↔
      ∃ pairs : Finset (Pair relation),
        map (first relation) pairs = left ∧ map (second relation) pairs = right := by
  constructor
  · intro covers
    exact ⟨matching relation left right, matching_first relation left right covers,
      matching_second relation left right covers⟩
  · rintro ⟨pairs, rfl, rfl⟩
    exact span_related relation pairs

end Mettapedia.CategoryTheory.FinitePowersetRelation
