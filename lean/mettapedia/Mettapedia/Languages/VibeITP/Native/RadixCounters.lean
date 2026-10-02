import Mettapedia.GSLT.LanguageDef.NativeWord64
import Mettapedia.Languages.VibeITP.Spec.Basic
import Mathlib.Tactic

/-!
Little-endian word-array arithmetic for native symbol and revision identities.
The carry loop uses unsigned word operations; its decoded value is an unbounded
natural number. Allocation and storage publication are separate interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.RadixCounters

abbrev Words := List (BitVec 64)

def value : Words → Nat
  | [] => 0
  | word :: rest => word.toNat + Spec.wordBound * value rest

/-- Carry, return on the first nonzero result, or grow by one final word. -/
def advance : Words → Words
  | [] => [1]
  | word :: rest =>
    let next := word + 1
    if next = 0 then 0 :: advance rest else next :: rest

theorem word_increment_zero_iff (word : BitVec 64) :
    word + 1 = 0 ↔ word.toNat + 1 = Spec.wordBound := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl]
  have bounded := word.isLt
  norm_num [Spec.wordBound] at bounded ⊢
  constructor <;> intro hypothesis <;> omega

theorem word_increment_no_carry (word : BitVec 64) (nonzero : word + 1 ≠ 0) :
    (word + 1).toNat = word.toNat + 1 := by
  have bounded := word.isLt
  have noCarry := (word_increment_zero_iff word).not.mp nonzero
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl]
  apply Nat.mod_eq_of_lt
  change word.toNat + 1 < Spec.wordBound
  change word.toNat < Spec.wordBound at bounded
  omega

theorem advance_value (words : Words) : value (advance words) = value words + 1 := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    unfold advance
    dsimp only
    by_cases carry : word + 1 = 0
    · rw [if_pos carry]
      have full := (word_increment_zero_iff word).mp carry
      simp only [value, show (0 : BitVec 64).toNat = 0 from rfl, zero_add, ih]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [if_neg carry]
      simp only [value, word_increment_no_carry word carry]
      omega

theorem advance_nonempty (words : Words) : advance words ≠ [] := by
  cases words with
  | nil => simp [advance]
  | cons word rest =>
    unfold advance
    dsimp only
    split <;> simp

theorem advance_length (words : Words) :
    (advance words).length = words.length ∨ (advance words).length = words.length + 1 := by
  induction words with
  | nil => simp [advance]
  | cons word rest ih =>
    unfold advance
    dsimp only
    split
    · simp only [List.length_cons]
      rcases ih with same | grown <;> omega
    · exact Or.inl rfl

theorem advance_strictly_increases (words : Words) : value words < value (advance words) := by
  rw [advance_value]
  omega

theorem advance_ne_self (words : Words) : advance words ≠ words := by
  intro same
  have changed := advance_strictly_increases words
  rw [same] at changed
  omega

def steps : Nat → Words → Words
  | 0, words => words
  | count + 1, words => steps count (advance words)

theorem steps_value (count : Nat) (words : Words) : value (steps count words) = value words + count := by
  induction count generalizing words with
  | zero => simp [steps]
  | succ count ih =>
    rw [steps, ih, advance_value]
    omega

theorem epochs_distinct (words : Words) {earlier later : Nat} (ordered : earlier < later) :
    steps earlier words ≠ steps later words := by
  intro same
  have values := congrArg value same
  rw [steps_value, steps_value] at values
  omega

def initialSymbols : Words := [13]
def initialRevision : Words := [0]

theorem symbol_epoch_value (count : Nat) : value (steps count initialSymbols) = 13 + count := by
  rw [steps_value]
  rfl

theorem revision_epoch_value (count : Nat) : value (steps count initialRevision) = count := by
  rw [steps_value]
  simp [initialRevision, value]

theorem builtin_slot_upper (builtin : Spec.Builtin) : builtin.slot ≤ 12 := by
  cases builtin <;> decide +kernel

theorem builtin_slot_injective : Function.Injective Spec.Builtin.slot := by
  intro left right same
  cases left <;> cases right <;> simp_all [Spec.Builtin.slot]

def symbolIdentity : Spec.SymId → Nat
  | .builtin builtin => builtin.slot
  | .fresh index => 13 + index

theorem symbolIdentity_injective : Function.Injective symbolIdentity := by
  intro left right same
  cases left with
  | builtin left =>
    cases right with
    | builtin right => exact congrArg Spec.SymId.builtin (builtin_slot_injective same)
    | fresh index =>
      have upper := builtin_slot_upper left
      simp only [symbolIdentity] at same
      omega
  | fresh index =>
    cases right with
    | builtin right =>
      have upper := builtin_slot_upper right
      simp only [symbolIdentity] at same
      omega
    | fresh other =>
      apply congrArg Spec.SymId.fresh
      simpa only [symbolIdentity, Nat.add_left_cancel_iff] using same

theorem allocated_symbol_identity (count : Nat) :
    value (steps count initialSymbols) = symbolIdentity (.fresh count) := symbol_epoch_value count

theorem fresh_epoch_avoids_builtins (count : Nat) (builtin : Spec.Builtin) :
    value (steps count initialSymbols) ≠ builtin.slot := by
  rw [symbol_epoch_value]
  have upper := builtin_slot_upper builtin
  omega

theorem one_word_carry_grows : advance [BitVec.allOnes 64] = [0, 1] := rfl

theorem two_word_carry_grows : advance [BitVec.allOnes 64, BitVec.allOnes 64] = [0, 0, 1] := rfl

theorem one_word_boundary_is_not_truncated : value (advance [BitVec.allOnes 64]) = Spec.wordBound := by
  rw [one_word_carry_grows]
  rfl

theorem carry_returns_before_later_words : advance [0, BitVec.allOnes 64] = [1, BitVec.allOnes 64] := rfl

end Mettapedia.Languages.VibeITP.Native.RadixCounters
