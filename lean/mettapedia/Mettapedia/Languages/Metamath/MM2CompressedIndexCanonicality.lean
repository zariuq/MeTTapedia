import Mettapedia.Languages.Metamath.MM2CompressedIndexSpine

/-!
# Canonicality of compact Appendix-B indices

The executable compressed-proof scanner constructs an index code from a
least-significant-first prefix and one terminal digit.  The natural-number
view used by semantic heap lookup is faithful exactly on valid codes: prefix
digits lie in `1..5` and the terminal digit lies in `0..19`.

These results connect scanner-built codes to `CompressedIndexCode.ofNat`.
They are structural arithmetic theorems, independent of any MM2 fixture.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedIndexCanonicality

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution

/-- Least-significant-first bijective-base-5 prefixes have unique values when
every digit is in the authored `1..5` range. -/
theorem compressedPrefixValue_injective_of_valid
    {left right : List Nat}
    (leftValid : ∀ digit, digit ∈ left -> 1 ≤ digit ∧ digit ≤ 5)
    (rightValid : ∀ digit, digit ∈ right -> 1 ≤ digit ∧ digit ≤ 5)
    (valueEqual : compressedPrefixValue left = compressedPrefixValue right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have headValid := rightValid head (by simp)
          simp only [compressedPrefixValue, List.foldr] at valueEqual
          omega
  | cons leftHead leftTail induction =>
      cases right with
      | nil =>
          have headValid := leftValid leftHead (by simp)
          simp only [compressedPrefixValue, List.foldr] at valueEqual
          omega
      | cons rightHead rightTail =>
          have leftHeadValid := leftValid leftHead (by simp)
          have rightHeadValid := rightValid rightHead (by simp)
          have leftTailValid :
              ∀ digit, digit ∈ leftTail -> 1 ≤ digit ∧ digit ≤ 5 := by
            intro digit member
            exact leftValid digit (by simp [member])
          have rightTailValid :
              ∀ digit, digit ∈ rightTail -> 1 ≤ digit ∧ digit ≤ 5 := by
            intro digit member
            exact rightValid digit (by simp [member])
          change
            5 * compressedPrefixValue leftTail + leftHead =
              5 * compressedPrefixValue rightTail + rightHead at valueEqual
          have headEqual : leftHead = rightHead := by omega
          have tailValueEqual :
              compressedPrefixValue leftTail =
                compressedPrefixValue rightTail := by
            omega
          subst rightHead
          congr
          exact induction leftTailValid rightTailValid tailValueEqual

/-- The complete compact code is injective on its valid subspace. -/
theorem CompressedIndexCode.eq_of_valid_of_value_eq
    {left right : CompressedIndexCode}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (valueEqual : left.value = right.value) :
    left = right := by
  rcases left with ⟨leftPrefix, leftTerminal⟩
  rcases right with ⟨rightPrefix, rightTerminal⟩
  rcases leftValid with ⟨leftPrefixValid, leftTerminalValid⟩
  rcases rightValid with ⟨rightPrefixValid, rightTerminalValid⟩
  change ∀ digit ∈ leftPrefix, 1 ≤ digit ∧ digit ≤ 5 at leftPrefixValid
  change leftTerminal < 20 at leftTerminalValid
  change ∀ digit ∈ rightPrefix, 1 ≤ digit ∧ digit ≤ 5 at rightPrefixValid
  change rightTerminal < 20 at rightTerminalValid
  change
    20 * compressedPrefixValue leftPrefix + leftTerminal =
      20 * compressedPrefixValue rightPrefix + rightTerminal at valueEqual
  have terminalEqual : leftTerminal = rightTerminal := by omega
  have prefixValueEqual :
      compressedPrefixValue leftPrefix =
        compressedPrefixValue rightPrefix := by
    omega
  have prefixEqual := compressedPrefixValue_injective_of_valid
    leftPrefixValid rightPrefixValid prefixValueEqual
  cases prefixEqual
  cases terminalEqual
  rfl

/-- Every valid scanner-built code is the canonical code for its denoted
natural number. -/
theorem CompressedIndexCode.eq_ofNat_value
    (code : CompressedIndexCode) (valid : code.Valid) :
    code = CompressedIndexCode.ofNat code.value := by
  apply CompressedIndexCode.eq_of_valid_of_value_eq valid
    (CompressedIndexCode.ofNat_valid code.value)
  rw [CompressedIndexCode.ofNat_value]

/-- Equal values of valid codes yield byte-identical MM2 atoms. -/
theorem CompressedIndexCode.atom_eq_of_valid_of_value_eq
    {left right : CompressedIndexCode}
    (leftValid : left.Valid) (rightValid : right.Valid)
    (valueEqual : left.value = right.value) :
    left.atom = right.atom := by
  rw [CompressedIndexCode.eq_of_valid_of_value_eq leftValid rightValid
    valueEqual]

/-! ## Necessity of the validity boundary -/

def noncanonicalTwenty : CompressedIndexCode where
  reversePrefixDigits := []
  terminalDigit := 20

def canonicalTwenty : CompressedIndexCode where
  reversePrefixDigits := [1]
  terminalDigit := 0

/-- Invalid terminal digits admit structural aliases, so the validity premise
of the injectivity theorem is load-bearing. -/
theorem invalid_code_alias_control :
    noncanonicalTwenty.value = canonicalTwenty.value ∧
      noncanonicalTwenty ≠ canonicalTwenty ∧
      ¬ noncanonicalTwenty.Valid ∧ canonicalTwenty.Valid := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · decide
  · simp [noncanonicalTwenty, CompressedIndexCode.Valid]
  · simp [canonicalTwenty, CompressedIndexCode.Valid]

#print axioms compressedPrefixValue_injective_of_valid
#print axioms CompressedIndexCode.eq_of_valid_of_value_eq
#print axioms CompressedIndexCode.eq_ofNat_value
#print axioms CompressedIndexCode.atom_eq_of_valid_of_value_eq
#print axioms invalid_code_alias_control

end Mettapedia.Languages.Metamath.MM2CompressedIndexCanonicality
