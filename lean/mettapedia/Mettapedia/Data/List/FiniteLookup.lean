import Mettapedia.Data.Fin.OptionSequence
import Mathlib.Data.List.Basic

/-!
# Compiling a finite family of lookups to list positions

Each required value is assigned its first matching list position. Compilation
fails if any value is absent. The resulting positions remain valid when both
the list and requirements are mapped. Recompiling after a noninjective map
can choose different positions, so compiled positions must be retained when
occurrence identity matters.
-/

set_option autoImplicit false

namespace List

universe u v
variable {α : Type u} {β : Type v} {k : Nat}

/-- Reversing a search is harmless when every matching entry has the same
    value. This compares values, without identifying their occurrences. -/
theorem find?_reverse_of_unique_matches (entries : List α) (p : α → Bool)
    (unique : ∀ a ∈ entries, ∀ b ∈ entries, p a = true → p b = true → a = b) :
    entries.reverse.find? p = entries.find? p := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      have tail := ih (fun a ma b mb => unique a (mem_cons_of_mem first ma)
        b (mem_cons_of_mem first mb))
      rw [reverse_cons, find?_append, tail]
      by_cases head : p first = true
      · cases found : rest.find? p with
        | none => simp [head]
        | some chosen =>
            have same := unique chosen (mem_cons_of_mem first (mem_of_find?_eq_some found))
              first mem_cons_self (find?_some found) head
            cases same
            simp [head]
      · simp [head]

variable [DecidableEq α]

def findPositions (entries : List α) (required : Fin k → α) : Option (Fin k → Nat) :=
  Fin.sequenceOption k (fun index => entries.findIdx? (fun entry => decide (entry = required index)))

theorem findPositions_getElem? {entries : List α} {required : Fin k → α}
    {positions : Fin k → Nat} (compiled : findPositions entries required = some positions)
    (index : Fin k) : entries[positions index]? = some (required index) := by
  have located := Fin.sequenceOption_sound k compiled index
  have selected := List.of_findIdx?_eq_some located
  cases found : entries[positions index]? with
  | none => simp [found] at selected
  | some entry =>
      simp only [found, decide_eq_true_eq] at selected
      simp only [selected]

theorem findPositions_isSome_iff (entries : List α) (required : Fin k → α) :
    (findPositions entries required).isSome = true ↔ ∀ index, required index ∈ entries := by
  rw [findPositions, Fin.sequenceOption_isSome_iff]
  simp only [List.findIdx?_isSome, List.any_eq_true, decide_eq_true_eq]
  constructor
  · intro found index
    obtain ⟨entry, member, same⟩ := found index
    simpa only [same] using member
  · intro present index
    exact ⟨required index, present index, rfl⟩

/-- Mapping preserves the compiled occurrences, without an injectivity
hypothesis and without running the position search again. -/
theorem findPositions_map_getElem? {entries : List α} {required : Fin k → α}
    {positions : Fin k → Nat} (compiled : findPositions entries required = some positions)
    (f : α → β) (index : Fin k) :
    (entries.map f)[positions index]? = some (f (required index)) := by
  rw [List.getElem?_map, findPositions_getElem? compiled index, Option.map_some]

theorem findPositions_retains_first_duplicate :
    (findPositions [4, 9, 4] (fun _ : Fin 1 => 4)).map (fun positions => positions 0) = some 0 := by
  decide +kernel

theorem findPositions_missing_rejected :
    findPositions [4, 9, 4] (fun index : Fin 2 => if index = 0 then 4 else 7) = none := by
  decide +kernel

theorem noninjective_map_changes_recompiled_position :
    (findPositions [1, 2] (fun _ : Fin 1 => 2)).map (fun positions => positions 0) = some 1 ∧
    (findPositions ([1, 2].map fun _ => 0) (fun _ : Fin 1 => 0)).map
      (fun positions => positions 0) = some 0 := by
  decide +kernel

#print axioms findPositions_getElem?
#print axioms findPositions_isSome_iff
#print axioms findPositions_map_getElem?
#print axioms noninjective_map_changes_recompiled_position

end List
