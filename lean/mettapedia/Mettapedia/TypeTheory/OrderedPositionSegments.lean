import Mathlib.Data.List.Basic

/-!
# Ordered segments of recursive child indices

A segment retains its length and child index. Flattening preserves repeated
indices as distinct positions; concatenation shifts later slots by the entire
preceding length. This is an ordered sequence, not a set of child indices.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.OrderedPositionSegments
universe u v
variable {Index : Type u}

abbrev Segment (Index : Type u) := Nat × Index

def flatten (segments : List (Segment Index)) : List Index :=
  segments.flatMap (fun segment => List.replicate segment.1 segment.2)

theorem flatten_nil : flatten ([] : List (Segment Index)) = [] := rfl

theorem flatten_cons (count : Nat) (index : Index) (rest : List (Segment Index)) :
    flatten ((count, index) :: rest) = List.replicate count index ++ flatten rest := rfl

theorem flatten_append (first second : List (Segment Index)) :
    flatten (first ++ second) = flatten first ++ flatten second := List.flatMap_append

theorem flatten_map {Target : Type v} (mapping : Index → Target) (segments : List (Segment Index)) :
    flatten (segments.map (fun segment => (segment.1, mapping segment.2))) =
      (flatten segments).map mapping := by
  induction segments with
  | nil => rfl
  | cons segment rest hypothesis =>
      rcases segment with ⟨count, index⟩
      simp only [List.map_cons, flatten_cons, List.map_append, List.map_replicate, hypothesis]

theorem length_flatten (segments : List (Segment Index)) :
    (flatten segments).length = (segments.map Prod.fst).sum := by
  induction segments with
  | nil => rfl
  | cons segment rest hypothesis =>
    rcases segment with ⟨count, index⟩
    simp only [flatten_cons, List.length_append, List.length_replicate, List.map_cons, List.sum_cons, hypothesis]

theorem lookup_cons (count : Nat) (index target : Index) (rest : List (Segment Index)) (slot : Nat) :
    (flatten ((count, index) :: rest))[slot]? = some target ↔
      (slot < count ∧ target = index) ∨
        ∃ offset, slot = count + offset ∧ (flatten rest)[offset]? = some target := by
  rw [flatten_cons]
  by_cases inside : slot < count
  · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using inside),
      List.getElem?_replicate_of_lt inside]
    constructor
    · intro same
      exact Or.inl ⟨inside, (Option.some.inj same).symm⟩
    · rintro (⟨_, rfl⟩ | ⟨offset, same, _⟩)
      · rfl
      · omega
  · rw [List.getElem?_append_right (by simpa only [List.length_replicate] using Nat.le_of_not_gt inside),
      List.length_replicate]
    constructor
    · intro valid
      exact Or.inr ⟨slot - count, by omega, valid⟩
    · rintro (⟨impossible, _⟩ | ⟨offset, rfl, valid⟩)
      · exact False.elim (inside impossible)
      · simpa only [Nat.add_sub_cancel_left] using valid

theorem lookup_functional (segments : List (Segment Index)) (slot : Nat) {first second : Index}
    (one : (flatten segments)[slot]? = some first) (two : (flatten segments)[slot]? = some second) :
    first = second := Option.some.inj (one.symm.trans two)

theorem active_iff (segments : List (Segment Index)) (slot : Nat) :
    (∃ index, (flatten segments)[slot]? = some index) ↔ slot < (flatten segments).length := by
  constructor
  · rintro ⟨index, present⟩
    exact ((List.getElem?_eq_some_iff).mp present).1
  · intro inside
    exact ⟨(flatten segments)[slot], List.getElem?_eq_getElem inside⟩

#print axioms lookup_cons
#print axioms lookup_functional
#print axioms active_iff
end Mettapedia.TypeTheory.OrderedPositionSegments
