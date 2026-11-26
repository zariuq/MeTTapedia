import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccursPrefix
import Mettapedia.Machines.TIsa.StoreInstructions.PackedSubstitution

/-!
# Detecting changed application edges without copying

A successful remap preserves every edge position. An allocation
is necessary in this representation exactly when some position
has a different handle. The first differing handle suffices to
decide this; the unchanged case needs no replacement array.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedRemapCoordinates

theorem coordinates (mapping words newer : Array Word) (remapped : PackedSubstitution.translate mapping words = some newer) :
    newer.size = words.size ∧ ∀ i : Fin words.size, mapping[words[i].toNat]? = newer[i.val]? := by
  unfold PackedSubstitution.translate at remapped
  obtain ⟨result, reads, exact⟩ := Option.map_eq_some_iff.mp remapped
  subst newer
  obtain ⟨width, access⟩ := PackedOccursPrefix.mapM_coordinates (fun handle : Word => mapping[handle.toNat]?)
    words.toList result reads
  refine ⟨by simpa only [List.size_toArray, Array.length_toList] using width, ?_⟩
  intro i
  have entry := access i.val
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem i.isLt, Option.bind_some] at entry
  change mapping[words[i.val].toNat]? = result.toArray[i.val]?
  simpa only [List.getElem?_toArray] using entry

theorem same_if_each_edge_keeps_its_handle (mapping words newer : Array Word)
    (remapped : PackedSubstitution.translate mapping words = some newer) :
    newer = words ↔ ∀ i : Fin words.size, mapping[words[i].toNat]? = some words[i] := by
  obtain ⟨width, lookup⟩ := coordinates mapping words newer remapped
  constructor
  · intro equal i
    rw [lookup i, equal, Array.getElem?_eq_getElem i.isLt]
    rfl
  · intro unchanged
    apply Array.ext width
    intro i _ inside
    have same := (lookup ⟨i, inside⟩).symm.trans (unchanged ⟨i, inside⟩)
    rw [Array.getElem?_eq_getElem (by omega : i < newer.size)] at same
    exact Option.some.inj same

theorem take_next_same {A : Type*} (left right : List A) (i : ℕ)
    (l : i < left.length) (r : i < right.length) :
    left.take (i + 1) = right.take (i + 1) ↔ left.take i = right.take i ∧ left[i] = right[i] := by
  constructor
  · intro agree
    have common := congrArg (List.take i) agree
    simp only [List.take_take, Nat.min_eq_left (by omega : i ≤ i + 1)] at common
    have atEnd := congrArg (fun xs : List A => xs[i]?) agree
    rw [List.getElem?_take_of_succ, List.getElem?_take_of_succ,
      List.getElem?_eq_getElem l, List.getElem?_eq_getElem r] at atEnd
    exact ⟨common, Option.some.inj atEnd⟩
  · rintro ⟨earlier, atEnd⟩
    rw [List.take_succ_eq_append_getElem l, List.take_succ_eq_append_getElem r, earlier, atEnd]

namespace Examples

theorem repeating_a_translated_handle_does_not_remove_a_position :
    PackedSubstitution.translate #[9, 9] #[0, 1, 0] = some #[9, 9, 9] := by decide +kernel

theorem a_previous_phase_cannot_supply_an_uninitialized_map_word :
    PackedSubstitution.translate #[9] #[0, 1] = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedRemapCoordinates
