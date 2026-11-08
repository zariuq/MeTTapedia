import Mettapedia.Languages.CHR.MachineSearchSound
import Mathlib.Data.List.Nodup

/-! The operational view of the machine's store. `contents` lists every slot's
occurrences as operational occurrences. A coherent store has distinct keys,
argument lists of each slot's arity, and distinct identifiers; an
operational occurrence of the store is then found in the slot of its key. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

def contents (store : Store) : List Occurrence :=
  store.flatMap fun entry => entry.2.map fun occurrence => (⟨occurrence.id, ⟨entry.1.1, occurrence.values⟩⟩ : Occurrence)

structure Coherent (store : Store) : Prop where
  keys : (store.map Prod.fst).Nodup
  arity : ∀ entry ∈ store, ∀ occurrence ∈ entry.2, occurrence.values.length = entry.1.2
  ids : ((contents store).map Occurrence.id).Nodup

theorem slot_of_member {store : Store} (keys : (store.map Prod.fst).Nodup) {key : Key}
    {occurrences : List Occ} (member : (key, occurrences) ∈ store) : slot key store = occurrences := by
  induction store with
  | nil => cases member
  | cons first rest ih =>
    rcases first with ⟨other, others⟩
    rw [List.map_cons, List.nodup_cons] at keys
    rcases List.mem_cons.mp member with same | later
    · cases same
      simp [slot]
    · have different : other ≠ key := by
        intro same
        subst same
        exact keys.1 (List.mem_map.mpr ⟨(other, occurrences), later, rfl⟩)
      simp [slot, different, ih keys.2 later]

theorem member_of_slot {store : Store} {key : Key} {occurrence : Occ}
    (member : occurrence ∈ slot key store) :
    (⟨occurrence.id, ⟨key.1, occurrence.values⟩⟩ : Occurrence) ∈ contents store := by
  induction store with
  | nil => cases member
  | cons first rest ih =>
    rcases first with ⟨other, others⟩
    unfold slot at member
    by_cases same : other = key
    · subst same
      simp only [if_true] at member
      simp only [contents, List.flatMap_cons, List.mem_append, List.mem_map]
      exact .inl ⟨occurrence, member, rfl⟩
    · simp only [same, if_false] at member
      simp only [contents, List.flatMap_cons, List.mem_append] at ih ⊢
      exact .inr (ih member)

/-- An operational occurrence of a coherent store is in the slot of its key. -/
theorem slot_of_contents {store : Store} (coherent : Coherent store) {occurrence : Occurrence}
    (member : occurrence ∈ contents store) :
    (⟨occurrence.id, occurrence.constraint.arguments⟩ : Occ) ∈
      slot (occurrence.constraint.name, occurrence.constraint.arguments.length) store := by
  simp only [contents, List.mem_flatMap, List.mem_map] at member
  obtain ⟨entry, inStore, stored, inSlot, rfl⟩ := member
  rcases entry with ⟨⟨name, arity⟩, occurrences⟩
  have length := coherent.arity _ inStore stored inSlot
  simp only at length ⊢
  rw [length, slot_of_member coherent.keys inStore]
  exact inSlot

/-- Distinct identifiers determine occurrences. -/
theorem contents_unique {store : Store} (coherent : Coherent store) {first second : Occurrence}
    (one : first ∈ contents store) (two : second ∈ contents store) (same : first.id = second.id) :
    first = second :=
  List.inj_on_of_nodup_map coherent.ids one two same

#print axioms slot_of_contents
#print axioms contents_unique

end Mettapedia.Languages.CHR.Machine
