import Mathlib.Data.List.Basic

/-!
# First-occurrence positions under a supported relabeling

An index names a value, not every occurrence of it: repeated occurrences share
their first position. Injective relabeling on the actual list support preserves
those indices. A total relabeling need not be injective outside that support.
-/

set_option autoImplicit false

namespace List.FirstOccurrence

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

theorem index_map (f : α → β) : ∀ (values : List α) (value : α), value ∈ values →
    (∀ first ∈ values, ∀ second ∈ values, f first = f second → first = second) →
    (values.map f).idxOf (f value) = values.idxOf value := by
  intro values
  induction values with
  | nil => intro value present _; cases present
  | cons first rest ih =>
      intro value present injective
      by_cases same : first = value
      · subst value
        simp
      · have tailMember : value ∈ rest := (List.mem_cons.mp present).resolve_left (Ne.symm same)
        have different : f first ≠ f value :=
          fun equal => same (injective first (by simp) value present equal)
        rw [List.map_cons,List.idxOf_cons_ne _ different,List.idxOf_cons_ne _ same]
        exact congrArg Nat.succ (ih value tailMember
          (fun left leftIn right rightIn => injective left (by simp [leftIn]) right (by simp [rightIn])))

theorem index_reflects_equality (values : List α) (first second : α) (present : first ∈ values) :
    values.idxOf first = values.idxOf second ↔ first = second := List.idxOf_inj present

def decode (values : List α) (fallback : α) (index : Nat) : α := (values[index]?).getD fallback

theorem decode_index (values : List α) (fallback value : α) (present : value ∈ values) :
    decode values fallback (values.idxOf value) = value := by
  simp only [decode,List.getElem?_idxOf present,Option.getD_some]

theorem index_is_bounded (values : List α) (value : α) (present : value ∈ values) :
    values.idxOf value < values.length := List.idxOf_lt_length_of_mem present

theorem a_merging_map_changes_indices :
    ((["a","b"].map (fun _ : String => "same")).idxOf "same") ≠ ["a","b"].idxOf "b" := by decide

end List.FirstOccurrence
