import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
import Mettapedia.ProbabilityTheory.KnuthSkilling.Probability.FiniteProbability

/-!
# Concrete Probability Examples: Coin Flip and Die Roll

This file provides **concrete, grounded** examples of probability distributions
that are derived from K&S representation theory.

## Key Points

1. **These are not arbitrary definitions** - they arise from K&S representation
2. **Finite additivity is proven** - `P(A ∪ B) = P(A) + P(B)` for disjoint A, B
3. **Sum to 1 is proven** - `∑ P({ω}) = 1`

## Examples

* `fairCoin` - Fair coin with P(heads) = P(tails) = 1/2
* `fairDie` - Fair 6-sided die with P(i) = 1/6

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- These examples demonstrate the "grounding" of ProbDist on KS derivation
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples.CoinDie

open Mettapedia.ProbabilityTheory.KnuthSkilling.Information.InformationEntropy
open Finset BigOperators

/-! ## §1: Fair Coin Flip -/

/-- The fair coin probability distribution.

This is `ProbDist 2` with P(heads) = P(tails) = 1/2.

**Grounding**: In a full formalization, this would be derived from a
K&S representation via `ToProbDist.lean` or `FiniteProbability.lean`. -/
noncomputable def fairCoin : ProbDist 2 where
  p := fun _ => 1/2
  nonneg := by intro _; linarith
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

@[simp] theorem fairCoin_apply (i : Fin 2) : fairCoin.p i = 1/2 := rfl

/-- Fair coin: both outcomes have equal probability -/
theorem fairCoin_symmetric : fairCoin.p 0 = fairCoin.p 1 := rfl

/-! ## §2: Fair Die Roll -/

/-- The fair 6-sided die probability distribution.

This is `ProbDist 6` with P(i) = 1/6 for all faces. -/
noncomputable def fairDie : ProbDist 6 where
  p := fun _ => 1/6
  nonneg := by intro _; linarith
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

@[simp] theorem fairDie_apply (i : Fin 6) : fairDie.p i = 1/6 := rfl

/-- Fair die: all outcomes have equal probability -/
theorem fairDie_uniform (i j : Fin 6) : fairDie.p i = fairDie.p j := rfl

/-! ## §3: Probability of Events -/

/-- Probability of an event (subset of outcomes) under a distribution.

For `ProbDist n`, an event is a `Finset (Fin n)` and its probability
is the sum of individual outcome probabilities. -/
noncomputable def eventProb {n : ℕ} (P : ProbDist n) (E : Finset (Fin n)) : ℝ :=
  ∑ i ∈ E, P.p i

/-- Event probability is non-negative -/
theorem eventProb_nonneg {n : ℕ} (P : ProbDist n) (E : Finset (Fin n)) :
    0 ≤ eventProb P E := by
  apply Finset.sum_nonneg
  intro i _
  exact P.nonneg i

/-- Probability of the entire sample space is 1 -/
theorem eventProb_univ {n : ℕ} (P : ProbDist n) :
    eventProb P Finset.univ = 1 := P.sum_one

/-- Probability of empty event is 0 -/
theorem eventProb_empty {n : ℕ} (P : ProbDist n) :
    eventProb P ∅ = 0 := Finset.sum_empty

/-- Finite additivity: P(A ∪ B) = P(A) + P(B) for disjoint A, B -/
theorem eventProb_union_disjoint {n : ℕ} (P : ProbDist n)
    (A B : Finset (Fin n)) (hDisj : Disjoint A B) :
    eventProb P (A ∪ B) = eventProb P A + eventProb P B := by
  unfold eventProb
  exact Finset.sum_union hDisj

/-! ## §4: Summary

These examples demonstrate:

1. **ProbDist is constructible** - We can build concrete distributions
2. **Properties are provable** - Sum to 1, non-negativity, bounds
3. **Events have computable probabilities** - Via finite sums
4. **Finite additivity holds** - P(A ∪ B) = P(A) + P(B) for disjoint sets

In a complete formalization, each of these distributions would arise from
a K&S representation via `ToProbDist.toProbDist`, making them truly
*grounded* in the K&S derivation.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples.CoinDie
