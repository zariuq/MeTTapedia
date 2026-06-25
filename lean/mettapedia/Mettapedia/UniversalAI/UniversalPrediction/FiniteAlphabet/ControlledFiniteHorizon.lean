import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledPrefixMeasure
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.FiniteHorizon

/-!
# Controlled Finite-Horizon Relative Entropy (Finite Alphabet)

This file lifts the ordinary finite-alphabet dominance→regret theorem to the
action-conditioned setting by conditioning a controlled prefix law on an action
stream.

Positive example:
* any controlled predictor dominating a controlled environment law yields the
  usual finite-horizon log-loss regret bound along every fixed action stream.

Negative example:
* this file still does not define a controlled Solomonoff universal mixture.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

namespace ControlledFiniteHorizon

variable {Action : Type*} {Y : Type*} [Fintype Y]

/-- Finite-horizon relative entropy of a controlled predictor against a
controlled environment law, evaluated along a fixed action stream. -/
noncomputable def relEntropy
    (μ : ControlledPrefixMeasure Action Y)
    (ξ : ControlledSemimeasure Action Y)
    (u : ℕ → Action)
    (n : ℕ) : Real :=
  FiniteHorizon.relEntropy (μ.conditionOnActionStream u) (ξ.conditionOnActionStream u) n

/-- Controlled dominance implies the standard finite-horizon log-loss regret
bound along every fixed action stream. -/
theorem relEntropy_le_log_inv_of_dominates
    (μ : ControlledPrefixMeasure Action Y)
    (ξ : ControlledSemimeasure Action Y)
    {c : ENNReal}
    (hdom : ControlledDominates ξ μ c)
    (hc0 : c ≠ 0)
    (u : ℕ → Action)
    (n : ℕ) :
    relEntropy μ ξ u n ≤ Real.log (1 / c.toReal) := by
  unfold relEntropy
  exact FiniteHorizon.relEntropy_le_log_inv_of_dominates
    (μ := μ.conditionOnActionStream u)
    (ξ := ξ.conditionOnActionStream u)
    (hdom := controlledDominates_conditionOnActionStream hdom u)
    (hc0 := hc0)
    n

end ControlledFiniteHorizon

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
