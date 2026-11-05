import Mettapedia.Computability.RegularLanguages.Regex
import Mettapedia.Algebra.Collections.SequencePatterns

/-!
# Regular patterns over the elements of a list

`re:match` matches a regular expression against the characters of a string.
Its list analogue matches a regular expression over an alphabet of elements
against the elements of a list: the regular expressions of
`Computability.RegularLanguages.Regex` are generic in their alphabet, with
literal elements and the wildcard as letters, and the derivative matcher is
sound and complete for the language of a pattern (`listMatch_iff`).

A sequence pattern read without the names of its variables is a regular
pattern (`erase`): a literal is itself, an element variable the wildcard, and
a sequence variable any sequence. Every instance of the pattern lies in the
language of its erasure (`instantiate_mem_erase`). The converse needs each
variable to occur once: a repeated variable is an equality between parts of
the list, which no regular pattern states (`Controls.repeated_variable_not_regular_reading`).
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.GSLT.LanguageDef.Collections.ElementPatterns

open Mettapedia.Computability.RegularLanguages
open Mettapedia.Algebra.Collections.SequencePatterns

variable {A E X : Type*}

/-- The list analogue of `re:match`. -/
def listMatch [DecidableEq A] (pattern : Regex A) (xs : List A) : Bool := fullMatch pattern xs

/-- **The list matcher is sound and complete** for the language of the pattern. -/
theorem listMatch_iff [DecidableEq A] (pattern : Regex A) (xs : List A) :
    listMatch pattern xs = true ↔ xs ∈ language pattern :=
  fullMatch_correct pattern xs

/-- A sequence pattern without the names of its variables. -/
def erase : List (Item A E X) → Regex A
  | [] => 1
  | .lit a :: rest => literal a * erase rest
  | .elem _ :: rest => any * erase rest
  | .seq _ :: rest => any.star * erase rest

theorem mem_any_star (xs : List A) : xs ∈ (language (any : Regex A))∗ := by
  rw [Language.mem_kstar]
  refine ⟨xs.map fun a => [a], ?_, ?_⟩
  · induction xs with
    | nil => rfl
    | cons a xs ih =>
        rw [List.map_cons, List.flatten_cons, List.singleton_append, ← ih]
  · intro y member
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp member
    exact ⟨a, rfl⟩

/-- **Every instance of a sequence pattern lies in the language of its erasure.** -/
theorem instantiate_mem_erase (σ : Assignment A E X) :
    ∀ pattern : List (Item A E X), instantiate σ pattern ∈ language (erase pattern)
  | [] => by simp [instantiate, erase]
  | .lit a :: rest => by
      rw [instantiate, erase, language_mul, Language.mem_mul]
      exact ⟨[a], Set.mem_singleton _, _, instantiate_mem_erase σ rest, rfl⟩
  | .elem y :: rest => by
      rw [instantiate, erase, language_mul, Language.mem_mul]
      exact ⟨[σ.elem y], ⟨σ.elem y, rfl⟩, _, instantiate_mem_erase σ rest, rfl⟩
  | .seq x :: rest => by
      rw [instantiate, erase, language_mul, Language.mem_mul, language_star]
      exact ⟨σ.seq x, mem_any_star _, _, instantiate_mem_erase σ rest, rfl⟩

namespace Controls

/-- `[1 (any) 3]` matches `[1 2 3]`; the literal `1` does not match `[2]`. -/
theorem literal_and_wildcard :
    listMatch (literal 1 * any * literal (3 : ℕ)) [1, 2, 3] = true ∧
      listMatch (literal (1 : ℕ)) [2] = false := by
  constructor
  · rw [listMatch_iff, language_mul, language_mul, Language.mem_mul]
    refine ⟨[1, 2], ?_, [3], Set.mem_singleton _, rfl⟩
    rw [Language.mem_mul]
    exact ⟨[1], Set.mem_singleton _, [2], ⟨2, rfl⟩, rfl⟩
  · rw [Bool.eq_false_iff, Ne, listMatch_iff, language_literal]
    intro member
    have same : ([2] : List ℕ) = [1] := member
    simp at same

/-- `[$xs $xs]` has no matcher against `[1 2]`, although `[1 2]` lies in the
language of its erasure. -/
theorem repeated_variable_not_regular_reading :
    matchFrom [.seq 0, .seq 0] [1, 2] (Partial.empty : Partial ℕ ℕ ℕ) = [] ∧
      ([1, 2] : List ℕ) ∈ language (erase ([.seq 0, .seq 0] : List (Item ℕ ℕ ℕ))) := by
  refine ⟨by decide, ?_⟩
  rw [erase, erase, erase, language_mul, language_mul, Language.mem_mul]
  exact ⟨[1, 2], by rw [language_star]; exact mem_any_star _, [], by
    rw [Language.mem_mul]; exact ⟨[], by rw [language_star]; exact mem_any_star _, [], by simp, rfl⟩,
    rfl⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.ElementPatterns
