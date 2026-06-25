import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledFiniteHorizon
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge

/-!
# Controlled Solomonoff Bridge (Finite Alphabet)

This file packages a concrete controlled semimeasure by lifting the ordinary
finite-alphabet Solomonoff mixture on observations into the controlled setting.

The resulting predictor is deliberately conservative:
it inhabits `ControlledSemimeasure Action Y`, but it ignores actions and uses
the observation-only universal mixture.

Positive example:
* along any fixed action stream `u`, the conditioned predictor is exactly the
  ordinary observation-alphabet Solomonoff semimeasure `M₂`.

Negative example:
* this file does not yet define a genuinely action-aware universal mixture.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledSolomonoffBridge

open scoped Classical BigOperators ENNReal

open Mettapedia.Computability.Hutter
open Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
open Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledFiniteHorizon
open Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge

variable {Action : Type*} {Y : Type*} [Fintype Y] [Primcodable Y]

/-- A concrete controlled Solomonoff-style semimeasure obtained by lifting the
ordinary observation-alphabet universal mixture and ignoring actions. -/
noncomputable abbrev M₂ : ControlledSemimeasure Action Y :=
  ControlledSemimeasure.ofObservationSemimeasure
    (Action := Action) (ξ := Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂ (α := Y))

@[simp] theorem conditionOnActionStream_M₂_apply
    (u : ℕ → Action)
    (ys : Word Y) :
    (M₂ (Action := Action) (Y := Y)).conditionOnActionStream u ys =
      Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂ (α := Y) ys := by
  simp [M₂]

@[simp] theorem relEntropy_M₂_eq
    (μ : ControlledPrefixMeasure Action Y)
    (u : ℕ → Action)
    (n : ℕ) :
    ControlledFiniteHorizon.relEntropy μ (M₂ (Action := Action) (Y := Y)) u n =
      FiniteHorizon.relEntropy
        (μ.conditionOnActionStream u)
        (Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.M₂ (α := Y))
        n := by
  unfold ControlledFiniteHorizon.relEntropy FiniteHorizon.relEntropy
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp

/-- Along any fixed action stream, the controlled Solomonoff predictor
dominates any lower-semicomputable conditioned controlled law. -/
theorem dominates_conditionOnActionStream_M₂
    (μ : ControlledPrefixMeasure Action Y)
    (u : ℕ → Action)
    (hμ : LowerSemicomputablePrefixMeasure (α := Y) (μ.conditionOnActionStream u)) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates ((M₂ (Action := Action) (Y := Y)).conditionOnActionStream u)
        (μ.conditionOnActionStream u) c := by
  obtain ⟨c, hc0, hdom, _⟩ :=
    Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.relEntropy_le_log_inv_M₂
      (μ := μ.conditionOnActionStream u) hμ 0
  refine ⟨c, hc0, ?_⟩
  intro ys
  simpa [conditionOnActionStream_M₂_apply] using hdom ys

/-- Concrete controlled Solomonoff regret bound: along any fixed action stream,
the lifted observation-alphabet universal mixture inherits the standard
finite-horizon log-loss guarantee against any lower-semicomputable conditioned
controlled law. -/
theorem relEntropy_le_log_inv_M₂
    (μ : ControlledPrefixMeasure Action Y)
    (u : ℕ → Action)
    (hμ : LowerSemicomputablePrefixMeasure (α := Y) (μ.conditionOnActionStream u))
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Dominates ((M₂ (Action := Action) (Y := Y)).conditionOnActionStream u)
        (μ.conditionOnActionStream u) c ∧
      ControlledFiniteHorizon.relEntropy μ (M₂ (Action := Action) (Y := Y)) u n ≤
        Real.log (1 / c.toReal) := by
  obtain ⟨c, hc0, hdom, hbound⟩ :=
    Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge.relEntropy_le_log_inv_M₂
      (μ := μ.conditionOnActionStream u) hμ n
  refine ⟨c, hc0, ?_, ?_⟩
  · intro ys
    simpa [conditionOnActionStream_M₂_apply] using hdom ys
  · simpa [relEntropy_M₂_eq] using hbound

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledSolomonoffBridge
