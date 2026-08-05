import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ZILExactness

/-!
# Hidden precision under fixed-prediction predictive coding

Rosenbaum, *On the relationship between predictive coding and
backpropagation*, proves that hidden-layer precision matrices do not change
the converged parameter update under the fixed-prediction assumption.  The
source is pinned to arXiv:2106.13082v6, with PDF SHA-256
`d7f9ddb9e16941893042a5bba6e686061c45c36086dc48334ea7ae18057e6ec3`.

The key object is the precision-weighted error, not the raw state deviation.
At a fixed point it obeys the ordinary reverse recursion from the output
boundary.  This file proves that fact for an arbitrary signal type and
arbitrary reverse maps: no matrix representation or commutativity assumption
is needed.

The development also makes the source's scope conditions explicit.  Exact
right inverses of the hidden precisions construct an equilibrium; injective
precisions make the raw deviation unique.  Two different hidden precisions
can produce different raw deviations while inducing the same weighted error
and parameter update.  In contrast, changing output precision changes the
boundary signal and can change every downstream update.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

variable {Signal Parameter : Type*}

/-- Output-first reverse recursion.  Index zero is the output signal, and
index `n + 1` is obtained by pulling index `n` through the next layer. -/
def fixedPredictionWeightedError
    (pullback : ℕ → Signal → Signal) (outputGradient : Signal) : ℕ → Signal
  | 0 => outputGradient
  | n + 1 => pullback n (fixedPredictionWeightedError pullback outputGradient n)

/-- Fixed-prediction equilibrium equations through a finite depth.  `precision
n (deviation n)` is the precision-weighted error at reverse-depth `n`. -/
def FixedPredictionPrecisionEquilibrium
    (depth : ℕ) (pullback precision : ℕ → Signal → Signal)
    (deviation : ℕ → Signal) (outputGradient : Signal) : Prop :=
  precision 0 (deviation 0) = outputGradient ∧
    ∀ n, n < depth →
      precision (n + 1) (deviation (n + 1)) =
        pullback n (precision n (deviation n))

/-- Every bounded equilibrium precision-weighted error is forced to equal the
ordinary reverse recursion, independently of the hidden precision maps. -/
theorem fixedPrediction_equilibrium_weightedError_eq
    (depth : ℕ) (pullback precision : ℕ → Signal → Signal)
    (deviation : ℕ → Signal) (outputGradient : Signal)
    (hequilibrium :
      FixedPredictionPrecisionEquilibrium depth pullback precision deviation
        outputGradient)
    (n : ℕ) (hn : n ≤ depth) :
    precision n (deviation n) =
      fixedPredictionWeightedError pullback outputGradient n := by
  induction n with
  | zero =>
      simpa [fixedPredictionWeightedError] using hequilibrium.1
  | succ n ih =>
      rw [hequilibrium.2 n (by omega), fixedPredictionWeightedError,
        ih (by omega)]

/-- A local parameter update reads only the precision-weighted error.  The
map includes any sign and parameter-Jacobian convention. -/
def fixedPredictionParameterUpdate
    (parameterPullback : ℕ → Signal → Parameter)
    (precision : ℕ → Signal → Signal) (deviation : ℕ → Signal)
    (n : ℕ) : Parameter :=
  parameterPullback n (precision n (deviation n))

/-- The corresponding ordinary reverse-mode parameter update. -/
def reverseModeParameterUpdate
    (parameterPullback : ℕ → Signal → Parameter)
    (pullback : ℕ → Signal → Signal) (outputGradient : Signal)
    (n : ℕ) : Parameter :=
  parameterPullback n
    (fixedPredictionWeightedError pullback outputGradient n)

/-- At fixed prediction equilibrium, every bounded local parameter update is
exactly the ordinary reverse-mode update. -/
theorem fixedPrediction_parameterUpdate_eq_reverseMode
    (depth : ℕ) (pullback precision : ℕ → Signal → Signal)
    (parameterPullback : ℕ → Signal → Parameter)
    (deviation : ℕ → Signal) (outputGradient : Signal)
    (hequilibrium :
      FixedPredictionPrecisionEquilibrium depth pullback precision deviation
        outputGradient)
    (n : ℕ) (hn : n ≤ depth) :
    fixedPredictionParameterUpdate parameterPullback precision deviation n =
      reverseModeParameterUpdate parameterPullback pullback outputGradient n := by
  simp only [fixedPredictionParameterUpdate, reverseModeParameterUpdate]
  rw [fixedPrediction_equilibrium_weightedError_eq depth pullback precision
    deviation outputGradient hequilibrium n hn]

/-- Hidden precision independence: any two equilibrium realizations with the
same output boundary and reverse maps induce exactly the same parameter
updates, even when their raw deviations differ. -/
theorem fixedPrediction_hiddenPrecision_parameterUpdate_independent
    (depth : ℕ) (pullback precision₁ precision₂ : ℕ → Signal → Signal)
    (parameterPullback : ℕ → Signal → Parameter)
    (deviation₁ deviation₂ : ℕ → Signal) (outputGradient : Signal)
    (hequilibrium₁ :
      FixedPredictionPrecisionEquilibrium depth pullback precision₁ deviation₁
        outputGradient)
    (hequilibrium₂ :
      FixedPredictionPrecisionEquilibrium depth pullback precision₂ deviation₂
        outputGradient)
    (n : ℕ) (hn : n ≤ depth) :
    fixedPredictionParameterUpdate parameterPullback precision₁ deviation₁ n =
      fixedPredictionParameterUpdate parameterPullback precision₂ deviation₂ n := by
  rw [fixedPrediction_parameterUpdate_eq_reverseMode depth pullback precision₁
      parameterPullback deviation₁ outputGradient hequilibrium₁ n hn,
    fixedPrediction_parameterUpdate_eq_reverseMode depth pullback precision₂
      parameterPullback deviation₂ outputGradient hequilibrium₂ n hn]

/-- Construct raw deviations by applying a declared precision inverse to the
reverse-mode weighted errors. -/
def fixedPredictionDeviation
    (precisionInverse : ℕ → Signal → Signal)
    (pullback : ℕ → Signal → Signal) (outputGradient : Signal) :
    ℕ → Signal :=
  fun n =>
    precisionInverse n
      (fixedPredictionWeightedError pullback outputGradient n)

/-- Exact right inverses of the precision maps are sufficient to construct a
fixed-prediction equilibrium at every finite depth. -/
theorem fixedPredictionDeviation_is_equilibrium
    (depth : ℕ) (pullback precision precisionInverse : ℕ → Signal → Signal)
    (outputGradient : Signal)
    (hright : ∀ n signal, precision n (precisionInverse n signal) = signal) :
    FixedPredictionPrecisionEquilibrium depth pullback precision
      (fixedPredictionDeviation precisionInverse pullback outputGradient)
      outputGradient := by
  constructor
  · simp [fixedPredictionDeviation, fixedPredictionWeightedError, hright]
  · intro n hn
    simp [fixedPredictionDeviation, fixedPredictionWeightedError, hright]

/-- If each precision map is injective, the raw deviation realizing a fixed
weighted-error recursion is unique through the declared depth. -/
theorem fixedPrediction_deviation_unique_of_precision_injective
    (depth : ℕ) (pullback precision : ℕ → Signal → Signal)
    (deviation₁ deviation₂ : ℕ → Signal) (outputGradient : Signal)
    (hinjective : ∀ n, Function.Injective (precision n))
    (hequilibrium₁ :
      FixedPredictionPrecisionEquilibrium depth pullback precision deviation₁
        outputGradient)
    (hequilibrium₂ :
      FixedPredictionPrecisionEquilibrium depth pullback precision deviation₂
        outputGradient)
    (n : ℕ) (hn : n ≤ depth) :
    deviation₁ n = deviation₂ n := by
  apply hinjective n
  rw [fixedPrediction_equilibrium_weightedError_eq depth pullback precision
      deviation₁ outputGradient hequilibrium₁ n hn,
    fixedPrediction_equilibrium_weightedError_eq depth pullback precision
      deviation₂ outputGradient hequilibrium₂ n hn]

/-! ## Exact scalar fixtures -/

def unitSignalPullback (_n : ℕ) (signal : ℝ) : ℝ :=
  signal

def identitySignalPrecision (_n : ℕ) (signal : ℝ) : ℝ :=
  signal

/-- Output precision is unchanged, while every hidden precision is doubled. -/
def doubledHiddenPrecision (n : ℕ) (signal : ℝ) : ℝ :=
  if n = 0 then signal else 2 * signal

def identityPrecisionDeviation (_n : ℕ) : ℝ :=
  2

def doubledHiddenPrecisionDeviation (n : ℕ) : ℝ :=
  if n = 0 then 2 else 1

theorem identityPrecisionDeviation_is_equilibrium :
    FixedPredictionPrecisionEquilibrium 1 unitSignalPullback
      identitySignalPrecision identityPrecisionDeviation 2 := by
  constructor
  · norm_num [identitySignalPrecision, identityPrecisionDeviation]
  · intro n hn
    have : n = 0 := by omega
    subst n
    norm_num [identitySignalPrecision, identityPrecisionDeviation,
      unitSignalPullback]

theorem doubledHiddenPrecisionDeviation_is_equilibrium :
    FixedPredictionPrecisionEquilibrium 1 unitSignalPullback
      doubledHiddenPrecision doubledHiddenPrecisionDeviation 2 := by
  constructor
  · norm_num [doubledHiddenPrecision, doubledHiddenPrecisionDeviation]
  · intro n hn
    have : n = 0 := by omega
    subst n
    norm_num [doubledHiddenPrecision, doubledHiddenPrecisionDeviation,
      unitSignalPullback]

/-- Positive source fixture: changing the hidden precision changes the raw
hidden deviation. -/
theorem hiddenPrecision_changes_rawDeviation :
    identityPrecisionDeviation 1 ≠ doubledHiddenPrecisionDeviation 1 := by
  norm_num [identityPrecisionDeviation, doubledHiddenPrecisionDeviation]

/-- Nevertheless the hidden weighted errors are exactly equal. -/
theorem hiddenPrecision_preserves_weightedError :
    identitySignalPrecision 1 (identityPrecisionDeviation 1) =
      doubledHiddenPrecision 1 (doubledHiddenPrecisionDeviation 1) := by
  norm_num [identitySignalPrecision, identityPrecisionDeviation,
    doubledHiddenPrecision, doubledHiddenPrecisionDeviation]

/-- Consequently an identity parameter pullback reads the same update from
both precision systems. -/
theorem hiddenPrecision_preserves_parameterUpdate :
    fixedPredictionParameterUpdate unitSignalPullback
        identitySignalPrecision identityPrecisionDeviation 1 =
      fixedPredictionParameterUpdate unitSignalPullback
        doubledHiddenPrecision doubledHiddenPrecisionDeviation 1 := by
  exact fixedPrediction_hiddenPrecision_parameterUpdate_independent
    1 unitSignalPullback identitySignalPrecision doubledHiddenPrecision
      unitSignalPullback identityPrecisionDeviation
      doubledHiddenPrecisionDeviation 2
      identityPrecisionDeviation_is_equilibrium
      doubledHiddenPrecisionDeviation_is_equilibrium 1 (by omega)

/-- Negative boundary: output precision changes the reverse-recursion boundary,
so it can change hidden credit even though hidden precision cannot. -/
theorem outputPrecision_changes_hiddenCredit :
    fixedPredictionWeightedError unitSignalPullback (2 * (1 : ℝ)) 1 ≠
      fixedPredictionWeightedError unitSignalPullback 1 1 := by
  norm_num [fixedPredictionWeightedError, unitSignalPullback]

#print axioms fixedPrediction_equilibrium_weightedError_eq
#print axioms fixedPrediction_hiddenPrecision_parameterUpdate_independent
#print axioms fixedPredictionDeviation_is_equilibrium
#print axioms fixedPrediction_deviation_unique_of_precision_injective
#print axioms outputPrecision_changes_hiddenCredit

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
