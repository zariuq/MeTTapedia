import Mettapedia.Computability.PNP.LocalityObstruction

/-!
# P vs NP crux: arbitrary local rules do not admit short uniform encodings

This file isolates the missing compression theorem behind the Goertzel switching step.

Once a decoder is only known to be "local" on `n` visible bits, the unconstrained class of
local rules is the full Boolean function space `(Fin n → Bool) → Bool`, which has cardinality
`2^(2^n)`. Therefore no uniform `s`-bit code can represent all such local rules unless
`s ≥ 2^n`.

Combined with `LocalityObstruction`, this shows that on bounded-degree neighborhoods of radius
`Θ(log m)`, a generic local rule requires exponentially many code bits in `m`, not polylogarithmically
many. Any recovery of a `poly(log m)` hypothesis class must therefore prove a strong extra
compression property.
-/

namespace Mettapedia.Computability.PNP

/-- `n` visible Boolean features. -/
abbrev VisibleBits (n : ℕ) := Fin n → Bool

/-- A local rule on `n` visible bits. -/
abbrev LocalRule (n : ℕ) := VisibleBits n → Bool

/-- A uniform `s`-bit code space. -/
abbrev BitCode (s : ℕ) := Fin s → Bool

/-- There are `2^n` visible Boolean inputs of width `n`. -/
theorem card_visibleBits (n : ℕ) : Fintype.card (VisibleBits n) = 2 ^ n := by
  simp [VisibleBits]

/-- There are `2^(2^n)` Boolean rules on `n` visible bits. -/
theorem card_localRule (n : ℕ) : Fintype.card (LocalRule n) = 2 ^ (2 ^ n) := by
  simp [LocalRule, VisibleBits]

/-- An `s`-bit code space has cardinality `2^s`. -/
theorem card_bitCode (s : ℕ) : Fintype.card (BitCode s) = 2 ^ s := by
  simp [BitCode]

/-- If `s < 2^n`, then `s`-bit codes cannot injectively represent all local rules on `n` bits. -/
theorem no_injective_bitCode_of_lt {n s : ℕ} (hs : s < 2 ^ n) :
    ¬ ∃ f : LocalRule n → BitCode s, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard : Fintype.card (LocalRule n) ≤ Fintype.card (BitCode s) :=
    Fintype.card_le_of_injective f hf
  rw [card_localRule, card_bitCode] at hcard
  have hlt : 2 ^ s < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact Nat.not_le_of_lt hlt hcard

/-- In particular, the full rule class on a radius-`log₂ m` bounded-degree neighborhood cannot be
uniformly encoded with fewer than `2^m` bits. -/
  theorem no_uniform_code_below_expInput_for_binaryLogNeighborhood {d m s : ℕ}
    (hd : 2 ≤ d) (hs : s < 2 ^ m) :
    ¬ ∃ f : LocalRule (d ^ (Nat.log 2 m + 1)) → BitCode s, Function.Injective f := by
  apply no_injective_bitCode_of_lt
  have hneigh : m ≤ d ^ (Nat.log 2 m + 1) :=
    inputSize_le_neighborhoodSize_at_binaryLogRadius hd
  exact lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide : 0 < 2) hneigh)

/-- A sharper restatement: the full local-rule class at binary-log radius already has at least
`2^(2^m)` elements. -/
theorem expExpInput_le_card_localRule_binaryLogNeighborhood {d m : ℕ} (hd : 2 ≤ d) :
    2 ^ (2 ^ m) ≤ Fintype.card (LocalRule (d ^ (Nat.log 2 m + 1))) := by
  rw [card_localRule]
  have hneigh : m ≤ d ^ (Nat.log 2 m + 1) :=
    inputSize_le_neighborhoodSize_at_binaryLogRadius hd
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hneigh)

end Mettapedia.Computability.PNP
