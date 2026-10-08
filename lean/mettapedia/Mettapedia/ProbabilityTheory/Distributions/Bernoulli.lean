import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bernoulli Distribution

This file defines the Bernoulli distribution for binary outcomes.

## Main Definitions

* `BernoulliDist`: Bernoulli distribution with parameter p ∈ [0,1]
* `BernoulliDist.prob`: Probability mass function

## Main Theorems

* `prob_nonneg`: Probabilities are non-negative
* `prob_sum_one`: Probabilities sum to 1

-/

namespace Mettapedia.ProbabilityTheory

/-- Bernoulli distribution with parameter p ∈ [0,1].

    Represents a binary random variable that takes value 1 (true) with
    probability p and value 0 (false) with probability 1-p.
-/
structure BernoulliDist where
  p : ℝ
  p_nonneg : 0 ≤ p
  p_le_one : p ≤ 1

namespace BernoulliDist

/-- Probability mass function for Bernoulli(p).

    * prob(true) = p
    * prob(false) = 1 - p
-/
def prob (d : BernoulliDist) (b : Bool) : ℝ :=
  if b then d.p else 1 - d.p

/-- Probabilities are non-negative. -/
theorem prob_nonneg (d : BernoulliDist) (b : Bool) : 0 ≤ d.prob b := by
  unfold prob
  split_ifs with h
  · exact d.p_nonneg
  · linarith [d.p_le_one]

/-- Probabilities sum to 1. -/
theorem prob_sum_one (d : BernoulliDist) : d.prob true + d.prob false = 1 := by
  unfold prob
  simp

/-- Expected value of Bernoulli(p) is p. -/
theorem mean (d : BernoulliDist) :
    1 * d.prob true + 0 * d.prob false = d.p := by
  unfold prob
  simp

/-- The centered second moment is the variance. Reusing a draw has this
moment; drawing twice instead requires an independent product law. -/
theorem variance (d : BernoulliDist) :
    (1 - d.p)^2 * d.prob true + (0 - d.p)^2 * d.prob false = d.p * (1-d.p) := by
  simp [prob]
  ring

/-- The two outcome masses are complementary. -/
theorem false_mass_complement (d : BernoulliDist) : d.prob false = 1-d.prob true := by
  simp [prob]

end BernoulliDist

end Mettapedia.ProbabilityTheory
