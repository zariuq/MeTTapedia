import Mettapedia.CategoryTheory.FinitePowerset

/-!
# Complete finite matching relations for weak pullbacks

Equal finite direct images construct the entire finite relation of matching
pairs. Both projected images are the supplied successor sets. Thus the
canonical comparison onto the pullback of finite direct images is surjective.
Different relations can have the same projections; no inverse is inferred.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FinitePowersetWeakPullback

open FinitePowerset

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

abbrev Pair (first : X → Z) (second : Y → Z) :=
  {coordinates : X × Y // first coordinates.1 = second coordinates.2}

def first (left : X → Z) (right : Y → Z) : Pair left right → X :=
  fun pair => pair.val.1

def second (left : X → Z) (right : Y → Z) : Pair left right → Y :=
  fun pair => pair.val.2

theorem square (left : X → Z) (right : Y → Z) :
    left ∘ first left right = right ∘ second left right := by
  funext pair
  exact pair.property

def matching (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y) : Finset (Pair left right) := by
  classical
  exact (leftSuccessors.product rightSuccessors).subtype
    (fun coordinates => left coordinates.1 = right coordinates.2)

@[simp] theorem mem_matching (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y) (pair : Pair left right) :
    pair ∈ matching left right leftSuccessors rightSuccessors ↔
      pair.val.1 ∈ leftSuccessors ∧ pair.val.2 ∈ rightSuccessors := by
  classical
  simp only [matching, Finset.mem_subtype]
  exact Finset.mem_product

theorem matching_first (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y)
    (sameImage : map left leftSuccessors = map right rightSuccessors) :
    map (first left right) (matching left right leftSuccessors rightSuccessors) =
      leftSuccessors := by
  apply Finset.ext
  intro value
  rw [mem_map]
  constructor
  · rintro ⟨pair, member, rfl⟩
    exact (mem_matching left right leftSuccessors rightSuccessors pair).mp member |>.1
  · intro member
    have common : left value ∈ map right rightSuccessors := by
      rw [← sameImage, mem_map]
      exact ⟨value, member, rfl⟩
    obtain ⟨other, otherMember, same⟩ := (mem_map right rightSuccessors _).mp common
    refine ⟨⟨(value, other), same.symm⟩, ?_, rfl⟩
    exact (mem_matching left right leftSuccessors rightSuccessors _).mpr
      ⟨member, otherMember⟩

theorem matching_second (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y)
    (sameImage : map left leftSuccessors = map right rightSuccessors) :
    map (second left right) (matching left right leftSuccessors rightSuccessors) =
      rightSuccessors := by
  apply Finset.ext
  intro other
  rw [mem_map]
  constructor
  · rintro ⟨pair, member, rfl⟩
    exact (mem_matching left right leftSuccessors rightSuccessors pair).mp member |>.2
  · intro member
    have common : right other ∈ map left leftSuccessors := by
      rw [sameImage, mem_map]
      exact ⟨other, member, rfl⟩
    obtain ⟨value, valueMember, same⟩ := (mem_map left leftSuccessors _).mp common
    refine ⟨⟨(value, other), same⟩, ?_, rfl⟩
    exact (mem_matching left right leftSuccessors rightSuccessors _).mpr
      ⟨valueMember, member⟩

def comparison (left : X → Z) (right : Y → Z) :
    Finset (Pair left right) → Pair (map left) (map right) :=
  fun successors => ⟨(map (first left right) successors, map (second left right) successors), by
    rw [map_compose, map_compose, square]⟩

def matchingSection (left : X → Z) (right : Y → Z) :
    Pair (map left) (map right) → Finset (Pair left right) :=
  fun pair => matching left right pair.val.1 pair.val.2

theorem comparison_matching (left : X → Z) (right : Y → Z)
    (pair : Pair (map left) (map right)) :
    comparison left right (matchingSection left right pair) = pair := by
  apply Subtype.ext
  exact Prod.ext (matching_first left right pair.val.1 pair.val.2 pair.property)
    (matching_second left right pair.val.1 pair.val.2 pair.property)

theorem comparison_surjective (left : X → Z) (right : Y → Z) :
    Function.Surjective (comparison left right) :=
  fun pair => ⟨matchingSection left right pair, comparison_matching left right pair⟩

/-- The entire relation realizes two-sided matching coverage. -/
theorem related_iff_matching (left : X → Z) (right : Y → Z)
    (leftSuccessors : Finset X) (rightSuccessors : Finset Y) :
    Related (fun value other => left value = right other) leftSuccessors rightSuccessors ↔
      map left leftSuccessors = map right rightSuccessors := by
  constructor
  · intro held
    apply Finset.ext
    intro common
    rw [mem_map, mem_map]
    constructor
    · rintro ⟨value, member, rfl⟩
      obtain ⟨other, otherMember, same⟩ := held.1 value member
      exact ⟨other, otherMember, same.symm⟩
    · rintro ⟨other, member, rfl⟩
      obtain ⟨value, valueMember, same⟩ := held.2 other member
      exact ⟨value, valueMember, same⟩
  · intro same
    constructor
    · intro value member
      have common : left value ∈ map right rightSuccessors := by
        rw [← same, mem_map]
        exact ⟨value, member, rfl⟩
      obtain ⟨other, otherMember, equal⟩ := (mem_map right rightSuccessors _).mp common
      exact ⟨other, otherMember, equal.symm⟩
    · intro other member
      have common : right other ∈ map left leftSuccessors := by
        rw [same, mem_map]
        exact ⟨other, member, rfl⟩
      exact (mem_map left leftSuccessors _).mp common

end Mettapedia.CategoryTheory.FinitePowersetWeakPullback
