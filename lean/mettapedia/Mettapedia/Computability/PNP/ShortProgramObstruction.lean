import Mettapedia.Computability.PNP.HypothesisClass
import Mathlib.Data.Nat.Log

/-!
# P vs NP crux: short global programs do not shrink the local rule class

One plausible reply to the locality/counting obstructions is:

> "The switched predictor is induced by a short global decoder, so only a tiny
> subclass of local rules is relevant."

This file shows that this is false without a much stronger restriction.  If the
post-switch input surface has `n` visible bits, then *every* local Boolean rule
on those `n` bits can be hard-wired by a truth table of length `2^n`.  Thus a
polynomial-size global description already suffices to realize the full local
rule class whenever `n = O(log m)`.
-/

namespace Mettapedia.Computability.PNP

noncomputable section

/-- Enumerate the `2^n` visible inputs by `Fin (2^n)`. -/
def visibleBitsEquivFin (n : ℕ) : VisibleBits n ≃ Fin (2 ^ n) := by
  simpa [card_visibleBits] using (Fintype.equivFin (VisibleBits n))

/-- Decode a `2^n`-bit truth table into the corresponding local rule on `n`
visible bits. -/
def truthTableDecode (n : ℕ) : BitCode (2 ^ n) → LocalRule n :=
  fun code x => code (visibleBitsEquivFin n x)

/-- Encode a local rule on `n` visible bits by its full truth table. -/
def truthTableEncode (n : ℕ) : LocalRule n → BitCode (2 ^ n) :=
  fun rule i => rule ((visibleBitsEquivFin n).symm i)

lemma truthTableDecode_encode (n : ℕ) (rule : LocalRule n) :
    truthTableDecode n (truthTableEncode n rule) = rule := by
  funext x
  simp [truthTableDecode, truthTableEncode]

lemma truthTableEncode_decode (n : ℕ) (code : BitCode (2 ^ n)) :
    truthTableEncode n (truthTableDecode n code) = code := by
  funext i
  simp [truthTableDecode, truthTableEncode]

/-- Full local-rule space is already realizable by `2^n` bits via truth tables. -/
theorem truthTableDecode_surjective (n : ℕ) :
    Function.Surjective (truthTableDecode n) := by
  intro rule
  exact ⟨truthTableEncode n rule, truthTableDecode_encode n rule⟩

/-- Truth-table coding is in fact a bijection. -/
theorem truthTableDecode_bijective (n : ℕ) :
    Function.Bijective (truthTableDecode n) := by
  refine ⟨?_, truthTableDecode_surjective n⟩
  intro c₁ c₂ h
  have := congrArg (truthTableEncode n) h
  simpa [truthTableEncode_decode] using this

/-- The explicit bit-encoded family that realizes every local rule by hard-wiring
its truth table. -/
def truthTableFamily (n : ℕ) : BitEncodedClassifierFamily (VisibleBits n) (2 ^ n) where
  decode := truthTableDecode n

/-- Therefore the realized class of the truth-table family is the full local-rule
space. -/
theorem truthTableFamily_realizes_all (n : ℕ) :
    EncodedFamily.realized (truthTableFamily n).toEncodedFamily = Set.univ := by
  ext rule
  constructor
  · intro _
    trivial
  · intro _
    rcases truthTableDecode_surjective n rule with ⟨code, rfl⟩
    exact ⟨code, rfl⟩

/-- Its realized classifier class has exactly the full local-rule cardinality
`2^(2^n)`. -/
theorem card_realized_truthTableFamily (n : ℕ) :
    Fintype.card (EncodedFamily.realized (truthTableFamily n).toEncodedFamily) = 2 ^ (2 ^ n) := by
  simpa [truthTableFamily_realizes_all] using card_localRule n

/-- At binary-log input width, the full truth table already fits in at most `2m`
bits.  So a merely linear-size global program budget can realize *every* local
rule on `log₂ m + 1` visible bits. -/
theorem truthTableBits_binaryLogWidth_le_twoMul {m : ℕ} (hm : m ≠ 0) :
    2 ^ (Nat.log 2 m + 1) ≤ 2 * m := by
  rw [Nat.pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hm)

/-- Specialized obstruction: on `log₂ m + 1` visible bits, the full local-rule
class is already realizable by a truth table of linear size in `m`. -/
theorem binaryLogWidth_fullLocalRule_realizable_by_linear_bits {m : ℕ} (hm : m ≠ 0) :
    ∃ decode : BitCode (2 ^ (Nat.log 2 m + 1)) → LocalRule (Nat.log 2 m + 1),
      Function.Surjective decode ∧ 2 ^ (Nat.log 2 m + 1) ≤ 2 * m := by
  refine ⟨truthTableDecode (Nat.log 2 m + 1), truthTableDecode_surjective _, ?_⟩
  exact truthTableBits_binaryLogWidth_le_twoMul hm

end

end Mettapedia.Computability.PNP
