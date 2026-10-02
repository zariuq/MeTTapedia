import Mettapedia.Computability.RegularLanguages.Regex

/-!
# Literal words and finite character classes

These are elaborations into Mathlib's existing expression structure. Their
languages are specified directly as singleton words and sets of one-letter
words; no matching procedure occurs in either specification.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- An expression accepting exactly the supplied word. -/
def word : List α → Regex α
  | [] => 1
  | a :: rest => literal a * word rest

theorem mem_language_word (expected input : List α) :
    input ∈ language (word expected) ↔ input = expected := by
  induction expected generalizing input with
  | nil => exact Language.mem_one input
  | cons a rest ih =>
      change input ∈ language (literal a) * language (word rest) ↔ input = a :: rest
      rw [Language.mem_mul]
      constructor
      · rintro ⟨left, hl, right, hr, hword⟩
        have first : left = [a] := hl
        have tail : right = rest := (ih right).mp hr
        subst left
        subst right
        exact hword.symm
      · intro same
        subst input
        exact ⟨[a], rfl, rest, (ih rest).mpr rfl, rfl⟩

@[simp] theorem language_word (expected : List α) : language (word expected) = {expected} := by
  ext input
  exact mem_language_word expected input

/-- A finite character class. Duplicate members affect syntax but not its
accepted language. The empty class accepts no word. -/
def oneOf : List α → Regex α
  | [] => 0
  | a :: rest => literal a + oneOf rest

theorem mem_language_oneOf (letters input : List α) :
    input ∈ language (oneOf letters) ↔ ∃ a ∈ letters, input = [a] := by
  induction letters with
  | nil => simp [oneOf]
  | cons a rest ih =>
      change input ∈ language (literal a) + language (oneOf rest) ↔ _
      rw [Language.mem_add, ih]
      constructor
      · rintro (h | ⟨b, hb, hword⟩)
        · exact ⟨a, List.mem_cons_self, h⟩
        · exact ⟨b, List.mem_cons_of_mem _ hb, hword⟩
      · rintro ⟨b, hb, hword⟩
        rcases List.mem_cons.mp hb with same | member
        · subst b
          exact Or.inl hword
        · exact Or.inr ⟨b, member, hword⟩

theorem oneOf_rejects_empty (letters : List α) : [] ∉ language (oneOf letters) := by
  rw [mem_language_oneOf]
  rintro ⟨a, _, impossible⟩
  cases impossible

theorem fullMatch_word [DecidableEq α] (expected input : List α) :
    fullMatch (word expected) input = decide (input = expected) := by
  apply Bool.eq_iff_iff.mpr
  rw [fullMatch_correct, mem_language_word, decide_eq_true_eq]

end Mettapedia.Computability.RegularLanguages
