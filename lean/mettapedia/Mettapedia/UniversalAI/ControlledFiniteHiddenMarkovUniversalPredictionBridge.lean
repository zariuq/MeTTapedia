import Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovObservedInference
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledSolomonoffBridge

/-!
# Controlled Finite HMM → Controlled Universal Prediction Bridge

This file packages the observed action-conditioned law of a controlled finite
HMM as a generic controlled prefix measure, making it available to the
dominance→regret machinery for controlled prediction.

Positive example:
* every controlled finite HMM induces a controlled prefix law on completed
  action-observation traces.

Negative example:
* this bridge still does not define a controlled Solomonoff universal mixture.
-/

noncomputable section

namespace Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge

open Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovModel
open Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovObservedInference
open Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
open scoped BigOperators ENNReal

universe uA

variable {Action : Type uA} {latent obs : ℕ}

/-- The observed trace law of a controlled finite HMM as a controlled prefix
measure. -/
noncomputable def toControlledPrefixMeasure
    (θ : ControlledFiniteHMMParam Action latent obs) :
    ControlledPrefixMeasure Action (Fin obs) where
  toFun := observedCycleProb θ
  root_eq_one' := by
    simp [observedCycleProb_nil]
  additive' := by
    intro zs a
    calc
      (∑ y : Fin obs, observedCycleProb θ (zs ++ [(a, y)]))
        = ∑ y : Fin obs,
            observationMassGivenAction θ (filteringMass θ zs) a y := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              exact observedCycleProb_append_singleton θ zs a y
      _ = ∑ x : Fin latent, filteringMass θ zs x := by
            exact observationMassGivenAction_sum_eq θ (filteringMass θ zs) a
      _ = observedCycleProb θ zs := by
            rfl

/-- A controlled finite HMM together with the lower-semicomputability witnesses
needed to apply the fixed-action-stream Solomonoff regret theorem uniformly
over all action streams.  This packages the genuine computability side
condition instead of pretending it follows automatically from the raw parameter
record. -/
structure LSCControlledFiniteHMMParam (Action : Type uA) (latent obs : ℕ) where
  toParam : ControlledFiniteHMMParam Action latent obs
  lsc_conditionOnActionStream :
    ∀ u : ℕ → Action,
      LowerSemicomputablePrefixMeasure (α := Fin obs)
        ((toControlledPrefixMeasure toParam).conditionOnActionStream u)

instance : Coe (LSCControlledFiniteHMMParam Action latent obs)
    (ControlledFiniteHMMParam Action latent obs) where
  coe θ := θ.toParam

/-- Any controlled predictor dominating the observed law of a controlled finite
HMM inherits the standard finite-horizon controlled regret bound along every
fixed action stream. -/
theorem relEntropy_le_log_inv_of_dominates
    (θ : ControlledFiniteHMMParam Action latent obs)
    (ξ : ControlledSemimeasure Action (Fin obs))
    {c : ENNReal}
    (hdom : ControlledDominates ξ (toControlledPrefixMeasure θ) c)
    (hc0 : c ≠ 0)
    (u : ℕ → Action)
    (n : ℕ) :
    ControlledFiniteHorizon.relEntropy (toControlledPrefixMeasure θ) ξ u n ≤
      Real.log (1 / c.toReal) := by
  exact ControlledFiniteHorizon.relEntropy_le_log_inv_of_dominates
    (μ := toControlledPrefixMeasure θ)
    (ξ := ξ)
    (hdom := hdom)
    (hc0 := hc0)
    (u := u)
    (n := n)

/-- Concrete controlled Solomonoff regret bound for a controlled finite HMM,
assuming the observation law induced by the chosen action stream is
lower semicomputable.

This computability hypothesis is a genuine domain condition: the current
`ControlledFiniteHMMParam` surface allows arbitrary probability measures, so
lower semicomputability is not automatic from the raw parameter record alone.
-/
theorem relEntropy_le_log_inv_controlledM₂
    (θ : ControlledFiniteHMMParam Action latent obs)
    (u : ℕ → Action)
    (hμ :
      LowerSemicomputablePrefixMeasure (α := Fin obs)
        ((toControlledPrefixMeasure θ).conditionOnActionStream u))
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates
          ((ControlledSolomonoffBridge.M₂ (Action := Action) (Y := Fin obs)).conditionOnActionStream u)
          ((toControlledPrefixMeasure θ).conditionOnActionStream u) c ∧
      ControlledFiniteHorizon.relEntropy
          (toControlledPrefixMeasure θ)
          (ControlledSolomonoffBridge.M₂ (Action := Action) (Y := Fin obs))
          u n ≤
        Real.log (1 / c.toReal) := by
  simpa using
    ControlledSolomonoffBridge.relEntropy_le_log_inv_M₂
      (μ := toControlledPrefixMeasure θ) (u := u) (hμ := hμ) (n := n)

/-- Packaged version of the controlled Solomonoff regret theorem for controlled
finite HMMs whose fixed-stream observation laws are lower semicomputable by
construction. -/
theorem relEntropy_le_log_inv_controlledM₂_of_lscParam
    (θ : LSCControlledFiniteHMMParam Action latent obs)
    (u : ℕ → Action)
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates
          ((ControlledSolomonoffBridge.M₂ (Action := Action) (Y := Fin obs)).conditionOnActionStream u)
          ((toControlledPrefixMeasure (θ : ControlledFiniteHMMParam Action latent obs)).conditionOnActionStream u) c ∧
      ControlledFiniteHorizon.relEntropy
          (toControlledPrefixMeasure (θ : ControlledFiniteHMMParam Action latent obs))
          (ControlledSolomonoffBridge.M₂ (Action := Action) (Y := Fin obs))
          u n ≤
        Real.log (1 / c.toReal) := by
  exact relEntropy_le_log_inv_controlledM₂
    (θ := (θ : ControlledFiniteHMMParam Action latent obs))
    (u := u)
    (hμ := θ.lsc_conditionOnActionStream u)
    (n := n)

end Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge
