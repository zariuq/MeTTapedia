import Mettapedia.Computability.PNP.ShortProgramObstruction

/-!
# P vs NP crux: exact metagraph/interface quotients have state explosion

The most creative remaining rescue route is that the switched local neighborhood
does not matter as raw bits, but only through a small canonical metagraph or
message-passing quotient.  This file isolates a generic obstruction to that
strategy.

If a quotient state must capture the *exact interface behavior* of a local
gadget on `k` visible boundary bits, then the relevant semantic object is a
boundary transducer

`(Fin k → Bool) → (Fin k → Bool)`.

There are `2^(k * 2^k)` such transducers.  Therefore no exact `s`-bit
metagraph/message quotient can cover the full interface-semantic space unless
`s ≥ k * 2^k`.  At binary-log width this already forces at least linear size in
the ambient parameter `m`, so the quotient cannot be finite-state or polylog by
default.
-/

namespace Mettapedia.Computability.PNP

/-- `k` visible boundary bits. -/
abbrev BoundaryBits (k : ℕ) := VisibleBits k

/-- Exact interface behavior on `k` boundary bits. -/
abbrev BoundaryMap (k : ℕ) := BoundaryBits k → BoundaryBits k

/-- There are `2^k` possible boundary assignments of width `k`. -/
theorem card_boundaryBits (k : ℕ) : Fintype.card (BoundaryBits k) = 2 ^ k :=
  card_visibleBits k

/-- Exact boundary transducers on `k` bits form a class of size `2^(k * 2^k)`. -/
theorem card_boundaryMap (k : ℕ) : Fintype.card (BoundaryMap k) = 2 ^ (k * 2 ^ k) := by
  calc
    Fintype.card (BoundaryMap k)
        = (Fintype.card (BoundaryBits k)) ^ Fintype.card (BoundaryBits k) := by
            simp [BoundaryMap]
    _ = (2 ^ k) ^ (2 ^ k) := by simp
    _ = 2 ^ (k * 2 ^ k) := by rw [← Nat.pow_mul]

/-- No `s`-bit code can surject onto the full class of exact boundary transducers
once `s < k * 2^k`. -/
theorem no_surjective_bitCode_to_boundaryMap_of_lt {k s : ℕ}
    (decode : BitCode s → BoundaryMap k) (hs : s < k * 2 ^ k) :
    ¬ Function.Surjective decode := by
  intro hsurj
  have hcard : Fintype.card (BoundaryMap k) ≤ Fintype.card (BitCode s) :=
    Fintype.card_le_of_surjective decode hsurj
  rw [card_boundaryMap, card_bitCode] at hcard
  have hlt : 2 ^ s < 2 ^ (k * 2 ^ k) := Nat.pow_lt_pow_right Nat.one_lt_two hs
  exact Nat.not_le_of_lt hlt hcard

/-- At binary-log width, exact interface transducer semantics already require at
least `m` code bits. -/
theorem inputSize_le_boundaryMapBits_binaryLogWidth {m : ℕ} :
    m ≤ (Nat.log 2 m + 1) * 2 ^ (Nat.log 2 m + 1) := by
  let k := Nat.log 2 m + 1
  have hpow : m < 2 ^ k := by
    simpa [k] using Nat.lt_pow_succ_log_self Nat.one_lt_two m
  have hk : 1 ≤ k := by
    dsimp [k]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hmul : 2 ^ k ≤ k * 2 ^ k := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right (2 ^ k) hk
  exact le_trans hpow.le hmul

/-- Therefore, on a `log₂ m + 1` boundary interface, there is no exact
metagraph/message quotient with fewer than `m` code bits. -/
theorem no_exact_metagraphQuotient_below_inputSize_binaryLogWidth {m s : ℕ}
    (decode : BitCode s → BoundaryMap (Nat.log 2 m + 1)) (hs : s < m) :
    ¬ Function.Surjective decode := by
  apply no_surjective_bitCode_to_boundaryMap_of_lt decode
  exact lt_of_lt_of_le hs inputSize_le_boundaryMapBits_binaryLogWidth

end Mettapedia.Computability.PNP
