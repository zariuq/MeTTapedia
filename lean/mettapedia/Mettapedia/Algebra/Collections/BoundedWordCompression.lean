import Mettapedia.Algebra.Collections.Unification
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Embedding

/-!
# Finite-support compression of substitution words

Input constants retain their literal identities. Every other supported token,
including a residual variable, receives one of finitely many residual names.
The completeness witness decodes those names back to the original tokens.
Neither the constant alphabet nor the variable type is assumed finite or
inhabited. This auxiliary construction is not a word-unification algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.BoundedWordCompression

open Unification (Word)

variable {A Y : Type*}

structure Encoding (constants : Finset A) (support : Finset (A ⊕ Y)) (capacity : Nat) where
  encode : A ⊕ Y → Option (constants ⊕ Fin capacity)
  lift : Fin capacity → Word A Y
  constant : ∀ (value : A) (member : value ∈ constants),
    encode (.inl value) = some (.inl ⟨value, member⟩)
  supported : ∀ token ∈ support, ∃ code, encode token = some code
  recovers : ∀ token code, encode token = some code →
    Sum.elim (fun value : constants => [Sum.inl value.val]) lift code = [token]

def Encoding.encodeWord {constants : Finset A} {support : Finset (A ⊕ Y)} {capacity : Nat}
    (encoding : Encoding constants support capacity) (word : Word A Y) : Word constants (Fin capacity) :=
  word.filterMap encoding.encode

def Encoding.decodeWord {constants : Finset A} {support : Finset (A ⊕ Y)} {capacity : Nat}
    (encoding : Encoding constants support capacity) (word : Word constants (Fin capacity)) : Word A Y :=
  word.flatMap (Sum.elim (fun value : constants => [Sum.inl value.val]) encoding.lift)

/-- A finite embedding supplies names only for the supported tokens. Unused
names decode to the empty word, so zero capacity needs no default token. -/
theorem exists_encoding (constants : Finset A) (support : Finset (A ⊕ Y)) (capacity : Nat)
    (bound : support.card ≤ capacity) : Nonempty (Encoding constants support capacity) := by
  classical
  have small : Fintype.card support ≤ capacity := by simpa using bound
  let index : support ↪ Fin capacity :=
    (Fintype.equivFin support).toEmbedding.trans (Fin.castLEEmb small)
  let lift : Fin capacity → Word A Y := fun name =>
    if found : ∃ token : support, index token = name then [(Classical.choose found).val] else []
  have lift_index (token : support) : lift (index token) = [token.val] := by
    have found : ∃ other : support, index other = index token := ⟨token, rfl⟩
    simp only [lift, dif_pos found]
    exact congrArg (fun value : support => [value.val]) (index.injective (Classical.choose_spec found))
  let foreign : A ⊕ Y → Option (constants ⊕ Fin capacity) := fun token =>
    if member : token ∈ support then some (.inr (index ⟨token, member⟩)) else none
  let encode : A ⊕ Y → Option (constants ⊕ Fin capacity)
    | .inl value => if member : value ∈ constants then some (.inl ⟨value, member⟩) else foreign (.inl value)
    | .inr slot => foreign (.inr slot)
  have foreign_recovers (token : A ⊕ Y) (code : constants ⊕ Fin capacity)
      (selected : foreign token = some code) :
      Sum.elim (fun value : constants => [Sum.inl value.val]) lift code = [token] := by
    dsimp only [foreign] at selected
    split at selected
    next member =>
      cases selected
      exact lift_index ⟨token, member⟩
    next => cases selected
  refine ⟨{encode, lift, constant := ?_, supported := ?_, recovers := ?_}⟩
  · intro value member
    simp only [encode, dif_pos member]
  · intro token member
    cases token with
    | inl value =>
        by_cases named : value ∈ constants
        · exact ⟨.inl ⟨value, named⟩, by simp only [encode, dif_pos named]⟩
        · exact ⟨.inr (index ⟨.inl value, member⟩), by simp only [encode, dif_neg named, foreign, dif_pos member]⟩
    | inr slot =>
        exact ⟨.inr (index ⟨.inr slot, member⟩), by simp only [encode, foreign, dif_pos member]⟩
  · intro token code selected
    cases token with
    | inl value =>
        dsimp only [encode] at selected
        split at selected
        · cases selected
          rfl
        · exact foreign_recovers (.inl value) code selected
    | inr slot => exact foreign_recovers (.inr slot) code selected

theorem Encoding.recover_word {constants : Finset A} {support : Finset (A ⊕ Y)} {capacity : Nat}
    (encoding : Encoding constants support capacity) (word : Word A Y)
    (supported : ∀ token ∈ word, token ∈ support) :
    encoding.decodeWord (encoding.encodeWord word) = word := by
  induction word with
  | nil => rfl
  | cons token word ih =>
      obtain ⟨code, selected⟩ := encoding.supported token (supported token List.mem_cons_self)
      have tail := ih (fun value member => supported value (List.mem_cons_of_mem _ member))
      change ((token :: word).filterMap encoding.encode).flatMap _ = token :: word
      rw [List.filterMap_cons, selected, List.flatMap_cons, encoding.recovers token code selected]
      simpa only [List.singleton_append, decodeWord, encodeWord] using congrArg (List.cons token) tail

theorem Encoding.encodeWord_length {constants : Finset A} {support : Finset (A ⊕ Y)} {capacity : Nat}
    (encoding : Encoding constants support capacity) (word : Word A Y)
    (supported : ∀ token ∈ word, token ∈ support) :
    (encoding.encodeWord word).length = word.length := by
  induction word with
  | nil => rfl
  | cons token word ih =>
      obtain ⟨code, selected⟩ := encoding.supported token (supported token List.mem_cons_self)
      have tail := ih (fun value member => supported value (List.mem_cons_of_mem _ member))
      simpa only [encodeWord, List.filterMap_cons, selected, List.length_cons] using congrArg Nat.succ tail

namespace Controls

theorem empty_types_need_no_default :
    Nonempty (Encoding (∅ : Finset Empty) (∅ : Finset (Empty ⊕ Empty)) 0) :=
  exists_encoding ∅ ∅ 0 (by simp)

theorem foreign_constant_and_variable_are_both_supported :
    Nonempty (Encoding ({0} : Finset Nat) ({Sum.inl 7, Sum.inr 7} : Finset (Nat ⊕ Nat)) 2) :=
  exists_encoding _ _ 2 (by decide)

theorem equal_payloads_with_different_tags_are_distinct :
    (Sum.inl 7 : Nat ⊕ Nat) ≠ .inr 7 := by decide

theorem foreign_token_cannot_use_an_empty_code_alphabet :
    ¬ Nonempty (Encoding (∅ : Finset Nat) ({Sum.inl 7} : Finset (Nat ⊕ Nat)) 0) := by
  rintro ⟨encoding⟩
  obtain ⟨code, _⟩ := encoding.supported (.inl 7) (by simp)
  cases code with
  | inl constant => exact Finset.notMem_empty constant.val constant.property
  | inr name => exact Fin.elim0 name

end Controls

#print axioms exists_encoding
#print axioms Encoding.recover_word
#print axioms Encoding.encodeWord_length

end Mettapedia.Algebra.Collections.BoundedWordCompression
