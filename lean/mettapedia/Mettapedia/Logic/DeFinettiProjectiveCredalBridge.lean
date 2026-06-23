import Mettapedia.Logic.DeFinetti
import Mettapedia.CategoryTheory.DeFinettiCategoricalInterface
import Mettapedia.CategoryTheory.DeFinettiKleisliGirySkeleton
import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveFiniteWindowRealization
import Exchangeability.Core
import Exchangeability.Probability.InfiniteProduct

/-!
# de Finetti Projective Credal Bridge

This file adapts the existing de Finetti factorization surface to the shared
projective credal abstraction.

The bridge is intentionally explicit: a de Finetti mixture becomes a compatible
global precise prevision only after the caller supplies the interpretation map
from mixture objects to precise previsions over the chosen global state space.
-/

namespace Mettapedia.Logic.DeFinettiProjectiveCredalBridge

open MeasureTheory
open Mettapedia.Logic.DeFinetti
open Mettapedia.Logic.Exchangeability
open Mettapedia.CategoryTheory
open Mettapedia.ProbabilityTheory.HigherOrderProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

variable {Ω Window Global : Type*} [MeasurableSpace Ω] [LE Window]

/-! ## Concrete Bernoulli-prefix prevision adapters -/

/-- Explicit finite prefix-law obligations for a Bernoulli mixture.  The
analysis theorem that mixture integrals are nonnegative and sum to one is kept
as an explicit gate here; this adapter is the algebraic handoff into Walley
previsions once that gate is available. -/
structure BernoulliMixturePrefixLaw
    (M : BernoulliMixture) (n : ℕ) where
  nonneg : ∀ xs : Fin n → Bool, 0 ≤ M.prob xs
  total : ∑ xs : (Fin n → Bool), M.prob xs = 1

namespace BernoulliMixturePrefixLaw

/-- A proved finite Bernoulli prefix law gives finite probability weights. -/
noncomputable def toFiniteWeights
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n) :
    PrecisePrevision.FiniteWeights (Fin n → Bool) where
  weight xs := M.prob xs
  nonneg := h.nonneg
  total := h.total

/-- A proved finite Bernoulli prefix law gives a precise prevision on prefix
gambles. -/
noncomputable def toPrecisePrevision
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n) :
    PrecisePrevision (Fin n → Bool) :=
  h.toFiniteWeights.toPrecisePrevision

@[simp] theorem toPrecisePrevision_apply
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    h.toPrecisePrevision X = ∑ xs, M.prob xs * X xs :=
  rfl

theorem toPrecisePrevision_precise
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n) :
    h.toPrecisePrevision.toLowerPrevision.isPrecise :=
  PrecisePrevision.FiniteWeights.toPrecisePrevision_precise h.toFiniteWeights

theorem toPrecisePrevision_atomGamble
    {M : BernoulliMixture} {n : ℕ}
    (h : BernoulliMixturePrefixLaw M n) (xs : Fin n → Bool) :
    h.toPrecisePrevision (PrecisePrevision.FiniteWeights.atomGamble xs) =
      M.prob xs := by
  classical
  change
    h.toFiniteWeights.toPrecisePrevision
        (PrecisePrevision.FiniteWeights.atomGamble xs) =
      h.toFiniteWeights.weight xs
  have hweights :=
    PrecisePrevision.FiniteWeights.ofPrecisePrevision_toPrecisePrevision
      h.toFiniteWeights
  exact congrArg (fun w => w.weight xs) hweights

end BernoulliMixturePrefixLaw

/-! ### One-bit predictive prefix gambles -/

/-- The one-bit prefix in which the next Boolean observation is true. -/
def oneBitTruePrefix : Fin 1 → Bool := fun _ => true

/-- The one-bit prefix in which the next Boolean observation is false. -/
def oneBitFalsePrefix : Fin 1 → Bool := fun _ => false

/-- Atomic finite-prefix gamble selecting the one-bit true observation. -/
def oneBitTrueGamble : Gamble (Fin 1 → Bool) :=
  PrecisePrevision.FiniteWeights.atomGamble oneBitTruePrefix

/-- Atomic finite-prefix gamble selecting the one-bit false observation. -/
def oneBitFalseGamble : Gamble (Fin 1 → Bool) :=
  PrecisePrevision.FiniteWeights.atomGamble oneBitFalsePrefix

theorem oneBitPrefix_cases (xs : Fin 1 → Bool) :
    xs = oneBitTruePrefix ∨ xs = oneBitFalsePrefix := by
  cases hxs : xs 0 with
  | false =>
      right
      ext i
      fin_cases i
      simpa [oneBitFalsePrefix] using hxs
  | true =>
      left
      ext i
      fin_cases i
      simpa [oneBitTruePrefix] using hxs

theorem oneBitTruePrefix_ne_oneBitFalsePrefix :
    oneBitTruePrefix ≠ oneBitFalsePrefix := by
  intro h
  have h0 := congrArg (fun f => f 0) h
  simp [oneBitTruePrefix, oneBitFalsePrefix] at h0

theorem oneBitTrueGamble_add_oneBitFalseGamble :
    oneBitTrueGamble + oneBitFalseGamble = Gamble.const (1 : ℝ) := by
  funext xs
  change oneBitTrueGamble xs + oneBitFalseGamble xs = 1
  rcases oneBitPrefix_cases xs with rfl | rfl
  · have hCross :
        PrecisePrevision.FiniteWeights.atomGamble oneBitFalsePrefix oneBitTruePrefix = 0 := by
      rw [PrecisePrevision.FiniteWeights.atomGamble]
      simp [oneBitTruePrefix_ne_oneBitFalsePrefix]
    simp [oneBitTrueGamble, oneBitFalseGamble, hCross]
  · have hCross :
        PrecisePrevision.FiniteWeights.atomGamble oneBitTruePrefix oneBitFalsePrefix = 0 := by
      rw [PrecisePrevision.FiniteWeights.atomGamble]
      simp [oneBitTruePrefix_ne_oneBitFalsePrefix.symm]
    simp [oneBitTrueGamble, oneBitFalseGamble, hCross]

/-- Bernoulli mixtures analytically induce finite prefix laws.  Nonnegativity
comes from the nonnegative Bernoulli-product integrand on `[0,1]`; normalization
comes from the finite product PMF and Kyburg flattening. -/
theorem bernoulliMixturePrefixLaw_analytic
    (M : BernoulliMixture) (n : ℕ) :
    BernoulliMixturePrefixLaw M n where
  nonneg := DeFinettiConnection.bernoulliMixture_prob_nonneg M n
  total := DeFinettiConnection.bernoulliMixture_prob_total M n

/-- The finite-prefix prevision obtained by flattening the Kyburg/de Finetti
parameterized Bernoulli-product kernel. -/
noncomputable def bernoulliMixtureKyburgPrefixPrevision
    (M : BernoulliMixture) (n : ℕ) :
    PrecisePrevision (Fin n → Bool) := by
  let μprefix : Measure (Fin n → Bool) :=
    ParametrizedDistribution.flatten (DeFinettiConnection.pd M n)
  haveI : IsProbabilityMeasure μprefix := by
    dsimp [μprefix]
    infer_instance
  exact PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision
    μprefix

/-- The analytic finite-prefix law used by the projective credal adapter is
exactly the finite probability-measure prevision obtained from Kyburg
flattening of the de Finetti Bernoulli-product kernel. -/
theorem bernoulliMixturePrefixPrevision_eq_kyburgFlatten
    (M : BernoulliMixture) (n : ℕ) :
    (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision =
      bernoulliMixtureKyburgPrefixPrevision M n := by
  ext X
  simp [bernoulliMixtureKyburgPrefixPrevision]
  apply Finset.sum_congr rfl
  intro xs _hxs
  rw [DeFinettiConnection.flatten_apply_singleton]
  rw [ENNReal.toReal_ofReal]
  exact DeFinettiConnection.bernoulliMixture_prob_nonneg M n xs

/-- Posterior specialization of the finite-prefix Kyburg bridge.  This keeps
the remaining process-carrier gap focused on the infinite/external realization,
not on finite-prefix probability-measure canonicality. -/
theorem posteriorBernoulliMixturePrefixPrevision_eq_kyburgFlatten
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision =
      bernoulliMixtureKyburgPrefixPrevision
        (M.posteriorBernoulliMixture k l hZ) n :=
  bernoulliMixturePrefixPrevision_eq_kyburgFlatten
    (M.posteriorBernoulliMixture k l hZ) n

/-- Shorter Boolean prefix gambles are exact marginals of longer
Bernoulli-mixture prefix previsions under canonical prefix truncation. -/
theorem bernoulliMixturePrefixPrevision_takePrefix_eq
    (M : BernoulliMixture) {m n : ℕ} (hmn : m ≤ n)
    (X : Gamble (Fin m → Bool)) :
    (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision
        (fun ys => X (Exchangeability.takePrefix (α := Bool) hmn ys)) =
      (bernoulliMixturePrefixLaw_analytic M m).toPrecisePrevision X := by
  classical
  rw [bernoulliMixturePrefixPrevision_eq_kyburgFlatten,
    bernoulliMixturePrefixPrevision_eq_kyburgFlatten]
  unfold bernoulliMixtureKyburgPrefixPrevision
  let μn : Measure (Fin n → Bool) :=
    ParametrizedDistribution.flatten (DeFinettiConnection.pd M n)
  haveI : IsProbabilityMeasure μn := by
    dsimp [μn]
    infer_instance
  let μm : Measure (Fin m → Bool) :=
    ParametrizedDistribution.flatten (DeFinettiConnection.pd M m)
  haveI : IsProbabilityMeasure μm := by
    dsimp [μm]
    infer_instance
  have hmap :
      Measure.map (Exchangeability.takePrefix (α := Bool) hmn) μn = μm := by
    simpa [μn, μm] using
      DeFinettiConnection.flatten_map_takePrefix_eq (M := M) (hmn := hmn)
  change
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision μn
        (fun ys => X (Exchangeability.takePrefix (α := Bool) hmn ys)) =
      PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision μm X
  symm
  simpa [hmap] using
    (PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_map_apply
      μn (Exchangeability.takePrefix (α := Bool) hmn)
      (Exchangeability.takePrefix_measurable (α := Bool) hmn) X)

/-- The analytic one-bit true prefix prevision is the Bernoulli-mixture
count-evidence mass for one success and no failures. -/
theorem bernoulliMixturePrefixPrevision_oneBitTrue_eq_countEvidenceMass
    (M : BernoulliMixture) :
    (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
        oneBitTrueGamble =
      M.countEvidenceMass 1 0 := by
  rw [oneBitTrueGamble,
    BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  symm
  simpa [oneBitTruePrefix, Mettapedia.Logic.Exchangeability.countTrue,
    Mettapedia.Logic.Exchangeability.countFalse] using
    (BernoulliMixture.countEvidenceMass_eq_prob_of_counts M oneBitTruePrefix)

/-- The analytic one-bit false prefix prevision is the Bernoulli-mixture
count-evidence mass for no successes and one failure. -/
theorem bernoulliMixturePrefixPrevision_oneBitFalse_eq_countEvidenceMass
    (M : BernoulliMixture) :
    (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
        oneBitFalseGamble =
      M.countEvidenceMass 0 1 := by
  rw [oneBitFalseGamble,
    BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  symm
  simpa [oneBitFalsePrefix, Mettapedia.Logic.Exchangeability.countTrue,
    Mettapedia.Logic.Exchangeability.countFalse] using
    (BernoulliMixture.countEvidenceMass_eq_prob_of_counts M oneBitFalsePrefix)

/-! ### Posterior predictive revision beyond the Beta subfamily -/

/-- Updating a general de-Finetti Bernoulli mixture by observed counts and then
asking the one-bit Kyburg/projective prefix prevision for `true` gives the
posterior predictive success probability.  No Beta-parametric assumption is
used here. -/
theorem posteriorBernoulliMixturePrefixPrevision_oneBitTrue_eq_posteriorPredictiveTrue
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitTrueGamble =
      M.posteriorPredictiveTrue k l := by
  rw [bernoulliMixturePrefixPrevision_oneBitTrue_eq_countEvidenceMass]
  exact
    BernoulliMixture.posteriorBernoulliMixture_countEvidenceMass_true_eq_posteriorPredictiveTrue
      M k l hZ

/-- Updating a general de-Finetti Bernoulli mixture by observed counts and then
asking the one-bit Kyburg/projective prefix prevision for `false` gives the
posterior predictive failure probability. -/
theorem posteriorBernoulliMixturePrefixPrevision_oneBitFalse_eq_posteriorPredictiveFalse
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitFalseGamble =
      M.posteriorPredictiveFalse k l := by
  rw [bernoulliMixturePrefixPrevision_oneBitFalse_eq_countEvidenceMass]
  exact
    BernoulliMixture.posteriorBernoulliMixture_countEvidenceMass_false_eq_posteriorPredictiveFalse
      M k l hZ

/-- General de-Finetti revision read as a count-evidence Bayes ratio through
the one-bit Kyburg/projective prefix prevision.  This is the broad semantic
update law of which Beta-Bernoulli conjugacy is only one convenient subfamily. -/
theorem posteriorBernoulliMixturePrefixPrevision_oneBitTrue_eq_countEvidenceMass_ratio
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitTrueGamble =
      M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l := by
  rw [posteriorBernoulliMixturePrefixPrevision_oneBitTrue_eq_posteriorPredictiveTrue
    M k l hZ]
  exact BernoulliMixture.posteriorPredictiveTrue_eq_countEvidenceMass_ratio M k l

/-- General de-Finetti revision read as a count-evidence Bayes ratio for the
next failure event through the one-bit Kyburg/projective prefix prevision. -/
theorem posteriorBernoulliMixturePrefixPrevision_oneBitFalse_eq_countEvidenceMass_ratio
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitFalseGamble =
      M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l := by
  rw [posteriorBernoulliMixturePrefixPrevision_oneBitFalse_eq_posteriorPredictiveFalse
    M k l hZ]
  exact BernoulliMixture.posteriorPredictiveFalse_eq_countEvidenceMass_ratio M k l

/-! ## External exchangeability prefix adapters -/

/-- The vendored exchangeability library's `iidProduct` has the expected finite
prefix product marginal.  This is the bridge point from the external
Kolmogorov/i.i.d. construction into the projective-credal prefix surface. -/
theorem externalIIDProductPrefixMeasure_eq_product
    (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ) :
    (Exchangeability.Probability.iidProduct ν).map
        (Exchangeability.prefixProj (α := Bool) n) =
      Measure.pi fun _ : Fin n => ν := by
  exact Exchangeability.Probability.iidProduct.cylinder_fintype ν

/-- A finite prefix marginal of an external i.i.d. product measure induces a
precise prevision on prefix gambles. -/
noncomputable def externalIIDProductPrefixPrevision
    (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ) :
    PrecisePrevision (Fin n → Bool) :=
  let μprefix : Measure (Fin n → Bool) :=
    (Exchangeability.Probability.iidProduct ν).map
      (Exchangeability.prefixProj (α := Bool) n)
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision μprefix

theorem externalIIDProductPrefixPrevision_precise
    (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ) :
    (externalIIDProductPrefixPrevision ν n).toLowerPrevision.isPrecise := by
  let μprefix : Measure (Fin n → Bool) :=
    (Exchangeability.Probability.iidProduct ν).map
      (Exchangeability.prefixProj (α := Bool) n)
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  change
    (PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision
      μprefix).toLowerPrevision.isPrecise
  exact
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_precise
      μprefix

/-! ## External path-law prefix adapters -/

/-- The vendored exchangeability path-law construction restricts to the
finite-prefix law of the observed process.  Unlike the i.i.d. adapter above,
this works for an arbitrary measurable process. -/
theorem externalPathLawPrefixMeasure_eq_processPrefix
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → Bool)
    (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ) :
    Measure.map (Exchangeability.prefixProj (α := Bool) n)
        (Exchangeability.pathLaw (α := Bool) μ X) =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ :=
  Exchangeability.pathLaw_map_prefix (α := Bool) μ X hX n

/-- Prefix-cylinder evaluation for the external path-law construction. -/
theorem externalPathLawPrefixCylinder_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → Bool)
    (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ)
    (S : Set (Fin n → Bool)) (hS : MeasurableSet S) :
    Exchangeability.pathLaw (α := Bool) μ X
        (Exchangeability.prefixCylinder (α := Bool) S) =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ S := by
  have hprefix :=
    externalPathLawPrefixMeasure_eq_processPrefix
      (μ := μ) (X := X) hX n
  have hmap :
      Measure.map (Exchangeability.prefixProj (α := Bool) n)
          (Exchangeability.pathLaw (α := Bool) μ X) S =
        Exchangeability.pathLaw (α := Bool) μ X
          (Exchangeability.prefixCylinder (α := Bool) S) := by
    rw [Measure.map_apply
      (Exchangeability.measurable_prefixProj (α := Bool) (n := n)) hS]
    rfl
  rw [← hmap]
  exact congrArg (fun ν : Measure (Fin n → Bool) => ν S) hprefix

/-- Every finite Boolean prefix gamble is a bounded measurable observable. -/
noncomputable def externalPrefixBoundedMeasurableGamble
    (n : ℕ) (Y : Gamble (Fin n → Bool)) :
    BoundedMeasurableGamble (Fin n → Bool) :=
  BoundedMeasurableGamble.ofFinite Y

@[simp] theorem externalPrefixBoundedMeasurableGamble_apply
    (n : ℕ) (Y : Gamble (Fin n → Bool)) (xs : Fin n → Bool) :
    externalPrefixBoundedMeasurableGamble n Y xs = Y xs :=
  rfl

/-- Pulling a finite prefix gamble back along the external path projection gives
a bounded measurable path-space cylinder observable. -/
noncomputable def externalPathLawPrefixBoundedMeasurableGamble
    (n : ℕ) (Y : Gamble (Fin n → Bool)) :
    BoundedMeasurableGamble (ℕ → Bool) :=
  BoundedMeasurableGamble.pullback
    (Exchangeability.prefixProj (α := Bool) n)
    (Exchangeability.measurable_prefixProj (α := Bool) (n := n))
    (externalPrefixBoundedMeasurableGamble n Y)

@[simp] theorem externalPathLawPrefixBoundedMeasurableGamble_apply
    (n : ℕ) (Y : Gamble (Fin n → Bool)) (ω : ℕ → Bool) :
    externalPathLawPrefixBoundedMeasurableGamble n Y ω =
      Y (Exchangeability.prefixProj (α := Bool) n ω) :=
  rfl

/-- Pulling a finite prefix gamble back along a measurable Boolean process gives
a bounded measurable observable on the process's probability space. -/
noncomputable def externalProcessPrefixBoundedMeasurableGamble
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i))
    (n : ℕ) (Y : Gamble (Fin n → Bool)) :
    BoundedMeasurableGamble Ω :=
  BoundedMeasurableGamble.pullback
    (fun ω => fun i : Fin n => X i ω)
    (measurable_pi_lambda _ fun i => hX i)
    (externalPrefixBoundedMeasurableGamble n Y)

@[simp] theorem externalProcessPrefixBoundedMeasurableGamble_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i))
    (n : ℕ) (Y : Gamble (Fin n → Bool)) (ω : Ω) :
    externalProcessPrefixBoundedMeasurableGamble X hX n Y ω =
      Y (fun i : Fin n => X i ω) :=
  rfl

/-- Any finite prefix of an external path law over a probability space induces
a precise prevision on prefix gambles. -/
noncomputable def externalPathLawPrefixPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ) :
    PrecisePrevision (Fin n → Bool) :=
  let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
  let μprefix : Measure (Fin n → Bool) :=
    Measure.map (Exchangeability.prefixProj (α := Bool) n) path
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision μprefix

theorem externalPathLawPrefixPrevision_precise
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ) :
    (externalPathLawPrefixPrevision μ X hX n).toLowerPrevision.isPrecise := by
  let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
  let μprefix : Measure (Fin n → Bool) :=
    Measure.map (Exchangeability.prefixProj (α := Bool) n) path
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  change
    (PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision
      μprefix).toLowerPrevision.isPrecise
  exact
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_precise
      μprefix

/-- For an external path law, σ-additive expectation of a bounded measurable
finite-prefix cylinder observable agrees with the finite-prefix precise
prevision used by the projective credal adapter. -/
theorem externalPathLawPrefixBoundedMeasurablePrevision_eq_prefixPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ)
    (Y : Gamble (Fin n → Bool)) :
    let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
    haveI : IsProbabilityMeasure path := by
      dsimp [path, Exchangeability.pathLaw]
      exact Measure.isProbabilityMeasure_map
        ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
    BoundedMeasurablePrecisePrevision.ofProbabilityMeasure path
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixPrevision μ X hX n Y := by
  dsimp only
  let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
  let μprefix : Measure (Fin n → Bool) :=
    Measure.map (Exchangeability.prefixProj (α := Bool) n) path
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  unfold externalPathLawPrefixPrevision
    externalPathLawPrefixBoundedMeasurableGamble
    externalPrefixBoundedMeasurableGamble
  have hpush :=
    BoundedMeasurablePrecisePrevision.ofProbabilityMeasure_map_apply
      path (Exchangeability.prefixProj (α := Bool) n)
      (Exchangeability.measurable_prefixProj (α := Bool) (n := n))
      (BoundedMeasurableGamble.ofFinite Y)
  rw [← hpush]
  exact
    PrecisePrevision.FiniteWeights.boundedMeasurablePrevision_ofFinite_eq_finiteProbabilityMeasurePrevision
      μprefix Y

/-! ## External path-law credal sets as projective specs -/

/-- A probability space together with a measurable Boolean process.  This is
the external-exchangeability carrier for finite path-law prefix adapters:
different elements of a credal set may use different underlying probability
spaces, but they all induce precise previsions on the common finite prefix
state space `Fin n → Bool`. -/
structure ExternalBoolProcessLaw (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  prob : IsProbabilityMeasure μ
  X : ℕ → Ω → Bool
  measurable : ∀ i : ℕ, Measurable (X i)

namespace ExternalBoolProcessLaw

/-- The canonical external Boolean process law carried by a probability space
and a measurable Boolean process. -/
noncomputable def ofProcess
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i)) :
    ExternalBoolProcessLaw Ω where
  μ := μ
  prob := inferInstance
  X := X
  measurable := hX

/-- The finite-prefix precise prevision induced by an external Boolean process
law through the vendored exchangeability path-law construction. -/
noncomputable def prefixPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) (n : ℕ) :
    PrecisePrevision (Fin n → Bool) := by
  haveI : IsProbabilityMeasure A.μ := A.prob
  exact externalPathLawPrefixPrevision A.μ A.X A.measurable n

theorem prefixPrevision_precise
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) (n : ℕ) :
    (A.prefixPrevision n).toLowerPrevision.isPrecise := by
  haveI : IsProbabilityMeasure A.μ := A.prob
  exact externalPathLawPrefixPrevision_precise A.μ A.X A.measurable n

/-- Prefix-cylinder evaluation for the path law carried by an external Boolean
process law. -/
theorem prefixCylinder_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) (n : ℕ)
    (S : Set (Fin n → Bool)) (hS : MeasurableSet S) :
    Exchangeability.pathLaw (α := Bool) A.μ A.X
        (Exchangeability.prefixCylinder (α := Bool) S) =
      Measure.map (fun ω => fun i : Fin n => A.X i ω) A.μ S := by
  exact externalPathLawPrefixCylinder_apply A.μ A.X A.measurable n S hS

/-- The common infinite-path sigma-additive bounded-observable prevision
induced by an external Boolean process law. -/
noncomputable def pathBoundedMeasurablePrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) :
    BoundedMeasurablePrecisePrevision (ℕ → Bool) := by
  haveI : IsProbabilityMeasure A.μ := A.prob
  let path : Measure (ℕ → Bool) :=
    Exchangeability.pathLaw (α := Bool) A.μ A.X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => A.measurable i).aemeasurable)
  exact BoundedMeasurablePrecisePrevision.ofProbabilityMeasure path

/-- On finite-prefix cylinders, the infinite-path bounded-observable prevision
agrees with the finite-prefix precise prevision already used by the projective
credal adapter. -/
theorem pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    A.pathBoundedMeasurablePrevision
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      A.prefixPrevision n Y := by
  unfold pathBoundedMeasurablePrevision prefixPrevision
  haveI : IsProbabilityMeasure A.μ := A.prob
  exact externalPathLawPrefixBoundedMeasurablePrevision_eq_prefixPrevision
    A.μ A.X A.measurable n Y

end ExternalBoolProcessLaw

/-- A credal set of external Boolean process laws induces a finite-prefix
credal set of precise previsions on `Fin n → Bool`. -/
noncomputable def externalPathLawPrefixCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    CredalPrevisionSet (Fin n → Bool) :=
  {P | ∃ A : ExternalBoolProcessLaw Ω, A ∈ C ∧
    P = A.prefixPrevision n}

theorem externalPathLawPrefixCredalSet_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty) :
    (externalPathLawPrefixCredalSet C n).Nonempty := by
  rcases hC with ⟨A, hA⟩
  exact ⟨A.prefixPrevision n, A, hA, rfl⟩

/-- A credal set of external Boolean process laws induces a bounded-measurable
credal set on the common infinite Boolean path space. -/
noncomputable def externalPathLawBoundedMeasurableCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) :
    BoundedMeasurableCredalSet (ℕ → Bool) :=
  {P | ∃ A : ExternalBoolProcessLaw Ω, A ∈ C ∧
    P = A.pathBoundedMeasurablePrevision}

@[simp] theorem mem_externalPathLawBoundedMeasurableCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C) :
    A.pathBoundedMeasurablePrevision ∈
      externalPathLawBoundedMeasurableCredalSet C :=
  ⟨A, hA, rfl⟩

/-- Nonempty external process-law credal sets induce nonempty bounded
path-space credal sets. -/
theorem externalPathLawBoundedMeasurableCredalSet_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    (externalPathLawBoundedMeasurableCredalSet C).Nonempty := by
  rcases hC with ⟨A, hA⟩
  exact ⟨A.pathBoundedMeasurablePrevision,
    mem_externalPathLawBoundedMeasurableCredalSet C hA⟩

/-- The bounded-measurable natural extension generated by external path laws
has an exact dominating-precise-completion envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_hasExactDominatingPreciseEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    boundedMeasurableHasExactDominatingPreciseEnvelope
      (boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)) :=
  boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)

/-- The bounded-measurable external path-law natural extension is below every
actual process-law prevision on every bounded path observable. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_le_processPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X ≤
      A.pathBoundedMeasurablePrevision X :=
  boundedMeasurableNaturalExtensionPrevision_le_completion
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
    (mem_externalPathLawBoundedMeasurableCredalSet C hA) X

/-- The bounded-measurable external path-law natural extension is the greatest
bounded lower prevision dominated by every actual process-law prevision. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_greatest_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    (L : BoundedMeasurableLowerPrevision (ℕ → Bool))
    (hL : ∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        L X ≤ A.pathBoundedMeasurablePrevision X)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    L X ≤
      boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X := by
  apply boundedMeasurableNaturalExtensionPrevision_greatest_lower_bound
  intro P hP Y
  rcases hP with ⟨A, hA, rfl⟩
  exact hL A hA Y

/-- Every actual process-law prevision lies below the bounded-measurable
external path-law natural upper envelope on every bounded path observable. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_processPrevision_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    A.pathBoundedMeasurablePrevision X ≤
      boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X :=
  boundedMeasurableNaturalUpperEnvelopePrevision_completion_le
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
    (mem_externalPathLawBoundedMeasurableCredalSet C hA) X

/-- The bounded-measurable external path-law natural upper envelope is the
least bounded upper prevision dominating every actual process-law prevision. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_least_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    (U : BoundedMeasurableUpperPrevision (ℕ → Bool))
    (hU : ∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        A.pathBoundedMeasurablePrevision X ≤ U X)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X ≤
      U X := by
  apply boundedMeasurableNaturalUpperEnvelopePrevision_least_upper_bound
  intro P hP Y
  rcases hP with ⟨A, hA, rfl⟩
  exact hU A hA Y

/-- Compact evaluation-closure carrier generated by a credal set of external
Boolean process laws on the common infinite path space. -/
noncomputable def externalPathLawBoundedMeasurableCompactCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) :
    BoundedMeasurableCredalSet (ℕ → Bool) :=
  boundedMeasurableCredalSetEvaluationClosure
    (externalPathLawBoundedMeasurableCredalSet C)

/-- Every external path-law prevision belongs to the compact carrier generated
by its credal set. -/
theorem mem_externalPathLawBoundedMeasurableCompactCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C) :
    A.pathBoundedMeasurablePrevision ∈
      externalPathLawBoundedMeasurableCompactCredalSet C :=
  boundedMeasurableCredalSet_subset_evaluationClosure
    (externalPathLawBoundedMeasurableCredalSet C)
    (mem_externalPathLawBoundedMeasurableCredalSet C hA)

/-- The compact external path-law bounded-measurable credal carrier is closed in
the evaluation topology. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_isClosed
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) :
    @IsClosed (BoundedMeasurablePrecisePrevision (ℕ → Bool))
      (BoundedMeasurablePrecisePrevision.evaluationTopology
        (Ω := ℕ → Bool))
      (externalPathLawBoundedMeasurableCompactCredalSet C) :=
  boundedMeasurableCredalSetEvaluationClosure_isClosed
    (externalPathLawBoundedMeasurableCredalSet C)

/-- The compact external path-law bounded-measurable credal carrier is compact
in the evaluation topology. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_isCompact
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) :
    @IsCompact (BoundedMeasurablePrecisePrevision (ℕ → Bool))
      (BoundedMeasurablePrecisePrevision.evaluationTopology
        (Ω := ℕ → Bool))
      (externalPathLawBoundedMeasurableCompactCredalSet C) :=
  boundedMeasurableCredalSetEvaluationClosure_isCompact
    (externalPathLawBoundedMeasurableCredalSet C)

/-- Nonempty external process-law credal sets induce nonempty compact
path-space credal carriers. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    (externalPathLawBoundedMeasurableCompactCredalSet C).Nonempty :=
  boundedMeasurableCredalSetEvaluationClosure_nonempty
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)

/-- Compactifying the external path-law bounded-measurable credal carrier
preserves the dominating precise completions of the generated natural
extension. -/
theorem boundedMeasurableDominatingPreciseCompletions_externalPathLawCompactCredalSet_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (externalPathLawBoundedMeasurableCompactCredalSet C)
          (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)) =
      boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (externalPathLawBoundedMeasurableCredalSet C)
          (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)) := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  exact
    boundedMeasurableDominatingPreciseCompletions_naturalExtension_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)

/-- The compact external path-law natural extension has an exact
dominating-precise-completion envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_hasExactDominatingPreciseEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) :
    boundedMeasurableHasExactDominatingPreciseEnvelope
      (boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)) :=
  boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (externalPathLawBoundedMeasurableCompactCredalSet C)
    (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)

/-- The compact external path-law natural extension is below every actual
process-law prevision on every bounded path observable. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_le_processPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC) X ≤
      A.pathBoundedMeasurablePrevision X :=
  boundedMeasurableNaturalExtensionPrevision_le_completion
    (externalPathLawBoundedMeasurableCompactCredalSet C)
    (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
    (mem_externalPathLawBoundedMeasurableCompactCredalSet C hA) X

/-- Every actual process-law prevision lies below the compact external path-law
natural upper envelope on every bounded path observable. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_processPrevision_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : BoundedMeasurableGamble (ℕ → Bool)) :
    A.pathBoundedMeasurablePrevision X ≤
      boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC) X :=
  boundedMeasurableNaturalUpperEnvelopePrevision_completion_le
    (externalPathLawBoundedMeasurableCompactCredalSet C)
    (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
    (mem_externalPathLawBoundedMeasurableCompactCredalSet C hA) X

/-- Evaluating finite-prefix cylinder observables over the infinite-path
bounded-measurable credal set gives exactly the same value set as evaluating
the existing finite-prefix credal set. -/
theorem externalPathLawBoundedMeasurableCredalSet_prefix_value_image_eq_finitePrefix
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    ((fun P : BoundedMeasurablePrecisePrevision (ℕ → Bool) =>
      P (externalPathLawPrefixBoundedMeasurableGamble n Y)) ''
        externalPathLawBoundedMeasurableCredalSet C) =
      ((fun P : PrecisePrevision (Fin n → Bool) => P Y) ''
        externalPathLawPrefixCredalSet C n) := by
  ext z
  constructor
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨A, hA, rfl⟩
    exact ⟨A.prefixPrevision n, ⟨A, hA, rfl⟩,
      (ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision
        A n Y).symm⟩
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨A, hA, rfl⟩
    exact ⟨A.pathBoundedMeasurablePrevision,
      mem_externalPathLawBoundedMeasurableCredalSet C hA,
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision
        A n Y⟩

/-- The lower envelope over a credal set of external path-law prefix
previsions. -/
noncomputable def externalPathLawPrefixLowerEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  lowerEnvelope (externalPathLawPrefixCredalSet C n)

/-- The external path-law prefix lower envelope is below every admissible
process-law prefix prevision. -/
theorem externalPathLawPrefixLowerEnvelope_le_processPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    externalPathLawPrefixLowerEnvelope C n X ≤ A.prefixPrevision n X := by
  simpa [externalPathLawPrefixLowerEnvelope] using
    finiteLowerEnvelopePrevision_le_completion
      (externalPathLawPrefixCredalSet C n)
      (externalPathLawPrefixCredalSet_nonempty C n ⟨A, hA⟩)
      (P := A.prefixPrevision n)
      (by exact ⟨A, hA, rfl⟩) X

/-- The external path-law prefix lower envelope is the greatest lower prevision
dominated by every admissible process-law prefix prevision. -/
theorem externalPathLawPrefixLowerEnvelope_greatest_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty)
    (L : LowerPrevision (Fin n → Bool))
    (hL : ∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool), L X ≤ A.prefixPrevision n X)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    L X ≤ externalPathLawPrefixLowerEnvelope C n X := by
  simpa [externalPathLawPrefixLowerEnvelope] using
    finiteLowerEnvelopePrevision_greatest_lower_bound
      (externalPathLawPrefixCredalSet C n)
      (externalPathLawPrefixCredalSet_nonempty C n hC) L
      (by
        intro P hP Y
        rcases hP with ⟨A, hA, rfl⟩
        exact hL A hA Y)
      X

/-- The upper envelope over a credal set of external path-law prefix
previsions. -/
noncomputable def externalPathLawPrefixUpperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  upperEnvelope (externalPathLawPrefixCredalSet C n)

/-- The finite-prefix credal width induced by external path laws. -/
noncomputable def externalPathLawPrefixEnvelopeWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeWidth (externalPathLawPrefixCredalSet C n)

/-- The finite-prefix width-complement induced by external path laws, used as
the PLN-style confidence coordinate of the prefix credal projection. -/
noncomputable def externalPathLawPrefixEnvelopeWidthComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeWidthComplement (externalPathLawPrefixCredalSet C n)

/-- The finite-prefix midpoint induced by external path laws, used as the
PLN-style strength coordinate of the prefix credal projection. -/
noncomputable def externalPathLawPrefixEnvelopeMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeMidpoint (externalPathLawPrefixCredalSet C n)

/-- The infinite-path bounded-measurable lower envelope, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix lower
envelope. -/
theorem boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableLowerEnvelope
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixLowerEnvelope C n Y := by
  unfold boundedMeasurableLowerEnvelope externalPathLawPrefixLowerEnvelope
    lowerEnvelope
  rw [externalPathLawBoundedMeasurableCredalSet_prefix_value_image_eq_finitePrefix]

/-- The bounded-measurable natural extension generated by external path laws,
restricted to a finite-prefix cylinder observable, is the existing finite-prefix
lower envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_prefix_eq_finitePrefixLower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCredalSet C) hC
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixLowerEnvelope C n Y := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower]

/-- The infinite-path bounded-measurable upper envelope, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix upper
envelope. -/
theorem boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableUpperEnvelope
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixUpperEnvelope C n Y := by
  unfold boundedMeasurableUpperEnvelope externalPathLawPrefixUpperEnvelope
    upperEnvelope
  rw [externalPathLawBoundedMeasurableCredalSet_prefix_value_image_eq_finitePrefix]

/-- The bounded-measurable natural upper envelope generated by external path
laws, restricted to a finite-prefix cylinder observable, is the existing
finite-prefix upper envelope. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_prefix_eq_finitePrefixUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCredalSet C) hC
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixUpperEnvelope C n Y := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply,
    boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper]

/-- The infinite-path bounded-measurable envelope width, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix width. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCredalSet_prefix_eq_finitePrefixWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeWidth C n Y := by
  unfold boundedMeasurableEnvelopeWidth externalPathLawPrefixEnvelopeWidth
    credalEnvelopeWidth
  rw [
    boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower,
    boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper]
  rfl

/-- The infinite-path bounded-measurable width-complement, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix confidence-like
coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCredalSet_prefix_eq_finitePrefixComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeWidthComplement C n Y := by
  unfold boundedMeasurableEnvelopeWidthComplement
    externalPathLawPrefixEnvelopeWidthComplement
    credalEnvelopeWidthComplement
  rw [
    boundedMeasurableEnvelopeWidth_externalPathLawCredalSet_prefix_eq_finitePrefixWidth]
  rfl

/-- The infinite-path bounded-measurable midpoint, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix strength-like
coordinate. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCredalSet_prefix_eq_finitePrefixMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeMidpoint C n Y := by
  unfold boundedMeasurableEnvelopeMidpoint externalPathLawPrefixEnvelopeMidpoint
    credalEnvelopeMidpoint
  rw [
    boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower,
    boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper]
  rfl

/-- Compactifying the external path-law bounded-measurable credal carrier does
not change finite-prefix lower envelopes. -/
theorem boundedMeasurableLowerEnvelope_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableLowerEnvelope
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixLowerEnvelope C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableLowerEnvelope_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower]

/-- Compactifying the external path-law bounded-measurable credal carrier does
not change finite-prefix upper envelopes. -/
theorem boundedMeasurableUpperEnvelope_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableUpperEnvelope
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixUpperEnvelope C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableUpperEnvelope_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper]

/-- The compact external path-law carrier has the same finite-prefix envelope
width as the raw external path-law carrier. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeWidth C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeWidth_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableEnvelopeWidth_externalPathLawCredalSet_prefix_eq_finitePrefixWidth]

/-- The compact external path-law carrier has the same finite-prefix
width-complement confidence coordinate as the raw external path-law carrier. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeWidthComplement C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeWidthComplement_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCredalSet_prefix_eq_finitePrefixComplement]

/-- The compact external path-law carrier has the same finite-prefix midpoint
strength coordinate as the raw external path-law carrier. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_finitePrefixMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixEnvelopeMidpoint C n Y := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeMidpoint_evaluationClosure_eq
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
      (externalPathLawPrefixBoundedMeasurableGamble n Y),
    boundedMeasurableEnvelopeMidpoint_externalPathLawCredalSet_prefix_eq_finitePrefixMidpoint]

/-- The compact external path-law natural extension, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix lower
envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixLowerEnvelope C n Y := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableLowerEnvelope_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
      C hC n Y]

/-- The compact external path-law natural upper envelope, restricted to a
finite-prefix cylinder observable, is the existing finite-prefix upper
envelope. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      externalPathLawPrefixUpperEnvelope C n Y := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply,
    boundedMeasurableUpperEnvelope_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
      C hC n Y]

/-- If an external path-law finite-prefix gamble spans the full unit interval,
then the compact bounded-measurable path-law carrier reads midpoint strength
one half on the corresponding prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_half_of_prefixUnitInterval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hL : externalPathLawPrefixLowerEnvelope C n Y = 0)
    (hU : externalPathLawPrefixUpperEnvelope C n Y = 1) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = (1 / 2 : ℝ) := by
  apply boundedMeasurableEnvelopeMidpoint_eq_half_of_natural_interval
    (C := externalPathLawBoundedMeasurableCompactCredalSet C)
    (hC := externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
  · rw [
      boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
        C hC n Y]
    exact hL
  · rw [
      boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
        C hC n Y]
    exact hU

/-- If an external path-law finite-prefix gamble spans the full unit interval,
then the compact bounded-measurable path-law carrier has maximal prefix-cylinder
width. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_one_of_prefixUnitInterval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hL : externalPathLawPrefixLowerEnvelope C n Y = 0)
    (hU : externalPathLawPrefixUpperEnvelope C n Y = 1) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = 1 := by
  apply boundedMeasurableEnvelopeWidth_eq_one_of_natural_interval
    (C := externalPathLawBoundedMeasurableCompactCredalSet C)
    (hC := externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
  · rw [
      boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
        C hC n Y]
    exact hL
  · rw [
      boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
        C hC n Y]
    exact hU

/-- If an external path-law finite-prefix gamble spans the full unit interval,
then the compact bounded-measurable path-law carrier has zero width-complement
confidence on the corresponding prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_zero_of_prefixUnitInterval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hL : externalPathLawPrefixLowerEnvelope C n Y = 0)
    (hU : externalPathLawPrefixUpperEnvelope C n Y = 1) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = 0 := by
  apply boundedMeasurableEnvelopeWidthComplement_eq_zero_of_natural_interval
    (C := externalPathLawBoundedMeasurableCompactCredalSet C)
    (hC := externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
  · rw [
      boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
        C hC n Y]
    exact hL
  · rw [
      boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
        C hC n Y]
    exact hU

/-- Unit-valued finite-prefix observables have bounded path-space envelope
width in `[0,1]`. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCredalSet_prefix_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hY : ∀ xs, Y xs ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ∈
      Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeWidth_in_unit_of_unit
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawPrefixBoundedMeasurableGamble n Y) hC
    (by intro ω; exact hY (fun i : Fin n => ω i))

/-- Unit-valued finite-prefix observables have bounded path-space
width-complement confidence coordinate in `[0,1]`. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCredalSet_prefix_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hY : ∀ xs, Y xs ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ∈
      Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeWidthComplement_in_unit_of_unit
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawPrefixBoundedMeasurableGamble n Y) hC
    (by intro ω; exact hY (fun i : Fin n => ω i))

/-- Unit-valued finite-prefix observables have bounded path-space midpoint
strength coordinate in `[0,1]`. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCredalSet_prefix_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω))
    (hC : (externalPathLawBoundedMeasurableCredalSet C).Nonempty)
    (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hY : ∀ xs, Y xs ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ∈
      Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeMidpoint_in_unit_of_unit
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawPrefixBoundedMeasurableGamble n Y) hC
    (by intro ω; exact hY (fun i : Fin n => ω i))

/-- Every admissible external process-law prefix prevision is below the prefix
upper envelope. -/
theorem externalPathLawPrefixPrevision_le_upperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    {A : ExternalBoolProcessLaw Ω} (hA : A ∈ C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    A.prefixPrevision n X ≤ externalPathLawPrefixUpperEnvelope C n X := by
  simpa [externalPathLawPrefixUpperEnvelope] using
    finiteCompletion_le_upperEnvelopePrevision
      (externalPathLawPrefixCredalSet C n)
      (externalPathLawPrefixCredalSet_nonempty C n ⟨A, hA⟩)
      (P := A.prefixPrevision n)
      (by exact ⟨A, hA, rfl⟩) X

/-- The external path-law prefix upper envelope is the least upper prevision
dominating every admissible process-law prefix prevision. -/
theorem externalPathLawPrefixUpperEnvelope_least_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty)
    (U : UpperPrevision (Fin n → Bool))
    (hU : ∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool), A.prefixPrevision n X ≤ U X)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    externalPathLawPrefixUpperEnvelope C n X ≤ U X := by
  simpa [externalPathLawPrefixUpperEnvelope] using
    finiteUpperEnvelopePrevision_least_upper_bound
      (externalPathLawPrefixCredalSet C n)
      (externalPathLawPrefixCredalSet_nonempty C n hC) U
      (by
        intro P hP Y
        rcases hP with ⟨A, hA, rfl⟩
        exact hU A hA Y)
      X

/-- The finite-prefix credal set induced by external Boolean process laws as a
one-window projective local-credal specification. -/
noncomputable def externalPathLawPrefixProjectiveSpec
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    ProjectiveLocalCredalSpec PUnit.{1} (Fin n → Bool) :=
  identityCredalProjectiveSpec (externalPathLawPrefixCredalSet C n)

@[simp] theorem externalPathLawPrefixProjectiveSpec_projectiveLimitCredalSet
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ) :
    (externalPathLawPrefixProjectiveSpec C n).projectiveLimitCredalSet =
      externalPathLawPrefixCredalSet C n := by
  simp [externalPathLawPrefixProjectiveSpec]

theorem externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty) :
    (externalPathLawPrefixProjectiveSpec C n).hasCompatibleCompletion := by
  rw [externalPathLawPrefixProjectiveSpec,
    identityCredalProjectiveSpec_hasCompatibleCompletion_iff]
  exact externalPathLawPrefixCredalSet_nonempty C n hC

/-- A finite external path-law prefix natural extension is Walley-coherent as a
finite lower envelope of precise process-prefix previsions. -/
theorem externalPathLawPrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_isCoherent
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty) :
    ((externalPathLawPrefixProjectiveSpec C n).finiteGlobalNaturalExtensionPrevision
      (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)).isCoherent :=
  ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_isCoherent
    (S := externalPathLawPrefixProjectiveSpec C n)
    (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)

/-- A finite external path-law prefix natural extension is exactly the lower
envelope of the precise previsions dominating it. -/
theorem externalPathLawPrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty) :
    hasExactDominatingPreciseEnvelope
      ((externalPathLawPrefixProjectiveSpec C n).finiteGlobalNaturalExtensionPrevision
        (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)) :=
  ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S := externalPathLawPrefixProjectiveSpec C n)
    (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)

/-- The projective natural extension of an external path-law prefix credal set
is exactly its lower envelope. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_globalNaturalExtension
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (externalPathLawPrefixProjectiveSpec C n).globalNaturalExtension X =
      externalPathLawPrefixLowerEnvelope C n X := by
  simp [externalPathLawPrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalNaturalExtension,
    externalPathLawPrefixLowerEnvelope]

/-- The projective upper envelope of an external path-law prefix credal set is
exactly its upper envelope. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_upperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    upperEnvelope
        (externalPathLawPrefixProjectiveSpec C n).projectiveLimitCredalSet X =
      externalPathLawPrefixUpperEnvelope C n X := by
  simp [externalPathLawPrefixProjectiveSpec, externalPathLawPrefixUpperEnvelope]

/-- The projective global width of an external path-law prefix credal set is
exactly its prefix envelope width. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_globalEnvelopeWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidth X =
      externalPathLawPrefixEnvelopeWidth C n X := by
  simp [externalPathLawPrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    externalPathLawPrefixEnvelopeWidth]

/-- The projective global width-complement of an external path-law prefix
credal set is exactly its prefix width-complement. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_globalEnvelopeWidthComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidthComplement X =
      externalPathLawPrefixEnvelopeWidthComplement C n X := by
  simp [externalPathLawPrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    externalPathLawPrefixEnvelopeWidthComplement]

/-- The projective global midpoint of an external path-law prefix credal set is
exactly its prefix midpoint. -/
@[simp] theorem externalPathLawPrefixProjectiveSpec_globalEnvelopeMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeMidpoint X =
      externalPathLawPrefixEnvelopeMidpoint C n X := by
  simp [externalPathLawPrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    externalPathLawPrefixEnvelopeMidpoint]

/-- The compact external path-law natural extension agrees on finite-prefix
cylinder observables with the finite projective Walley natural extension of
the corresponding prefix credal set. -/
theorem boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_projectiveNaturalExtensionPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      ((externalPathLawPrefixProjectiveSpec C n).finiteGlobalNaturalExtensionPrevision
        (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)) Y := by
  rw [
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
      C hC n Y]
  rw [ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_apply]
  rw [externalPathLawPrefixProjectiveSpec_globalNaturalExtension]

/-- The compact external path-law natural upper envelope agrees on
finite-prefix cylinder observables with the finite projective Walley upper
envelope of the corresponding prefix credal set. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_projectiveUpperEnvelopePrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      ((externalPathLawPrefixProjectiveSpec C n).finiteGlobalUpperEnvelopePrevision
        (externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion C n hC)) Y := by
  rw [
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
      C hC n Y]
  rw [ProjectiveLocalCredalSpec.finiteGlobalUpperEnvelopePrevision_apply]
  rw [externalPathLawPrefixProjectiveSpec_upperEnvelope]

/-- The compact external path-law carrier and the finite projective prefix
Walley interface compute the same PLN-facing interval width. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_projectiveEnvelopeWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidth Y := by
  rw [
    boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
      C hC n Y,
    externalPathLawPrefixProjectiveSpec_globalEnvelopeWidth]

/-- The compact external path-law carrier and the finite projective prefix
Walley interface compute the same PLN-facing width-complement confidence
coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_projectiveEnvelopeWidthComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidthComplement Y := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
      C hC n Y,
    externalPathLawPrefixProjectiveSpec_globalEnvelopeWidthComplement]

/-- The compact external path-law carrier and the finite projective prefix
Walley interface compute the same PLN-facing midpoint strength coordinate. -/
theorem boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_projectiveEnvelopeMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) =
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeMidpoint Y := by
  rw [
    boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_finitePrefixMidpoint
      C hC n Y,
    externalPathLawPrefixProjectiveSpec_globalEnvelopeMidpoint]

/-- Agreement of all admissible external process laws on a finite-prefix gamble
makes that gamble determined by the projective credal set. -/
theorem externalPathLawPrefixProjectiveSpec_determinesGlobalGamble_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n X = B.prefixPrevision n X) :
    (externalPathLawPrefixProjectiveSpec C n).determinesGlobalGamble X := by
  rw [externalPathLawPrefixProjectiveSpec,
    identityCredalProjectiveSpec_determinesGlobalGamble_iff]
  intro P hP Q hQ
  rcases hP with ⟨A, hA, rfl⟩
  rcases hQ with ⟨B, hB, rfl⟩
  exact hAgree A hA B hB

/-- Disagreement between two admissible external process laws on a finite-prefix
gamble gives strict projective credal width. -/
theorem externalPathLawPrefixProjectiveSpec_hasStrictGlobalWidth_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n X < B.prefixPrevision n X) :
    (externalPathLawPrefixProjectiveSpec C n).hasStrictGlobalWidth X := by
  rw [externalPathLawPrefixProjectiveSpec,
    identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
  refine ⟨A.prefixPrevision n, ?_, B.prefixPrevision n, ?_, hlt⟩
  · exact ⟨A, hA, rfl⟩
  · exact ⟨B, hB, rfl⟩

/-- External process-law disagreement produces a nontrivial finite-prefix
lower/upper envelope. -/
theorem externalPathLawPrefixCredalSet_lowerUpperEnvelope_nontrivial_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n X < B.prefixPrevision n X) :
    lowerEnvelope (externalPathLawPrefixCredalSet C n) X <
      upperEnvelope (externalPathLawPrefixCredalSet C n) X := by
  exact
    lower_upperEnvelope_nontrivial_of_strictWidth
      (externalPathLawPrefixCredalSet C n) X
      (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) X)
      (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) X)
      (by
        refine ⟨A.prefixPrevision n, ?_, B.prefixPrevision n, ?_, hlt⟩
        · exact ⟨A, hA, rfl⟩
        · exact ⟨B, hB, rfl⟩)

/-- External process-law disagreement gives positive finite-prefix credal
envelope width. -/
theorem externalPathLawPrefixCredalSet_envelopeWidth_pos_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n X < B.prefixPrevision n X) :
    0 < credalEnvelopeWidth (externalPathLawPrefixCredalSet C n) X := by
  exact
    credalEnvelopeWidth_pos_of_strictWidth
      (externalPathLawPrefixCredalSet C n) X
      (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) X)
      (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) X)
      (by
        refine ⟨A.prefixPrevision n, ?_, B.prefixPrevision n, ?_, hlt⟩
        · exact ⟨A, hA, rfl⟩
        · exact ⟨B, hB, rfl⟩)

/-- If all admissible external process laws agree on a finite-prefix gamble,
then the PLN-style width-complement confidence coordinate is maximal. -/
theorem externalPathLawPrefixEnvelopeWidthComplement_eq_one_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n X = B.prefixPrevision n X) :
    externalPathLawPrefixEnvelopeWidthComplement C n X = 1 := by
  rcases hC with ⟨A, hA⟩
  unfold externalPathLawPrefixEnvelopeWidthComplement
  exact
    credalEnvelopeWidthComplement_eq_one_of_credalSetDetermines
      (externalPathLawPrefixCredalSet C n) X
      (externalPathLawPrefixCredalSet_nonempty C n ⟨A, hA⟩)
      (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) X)
      (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) X)
      (P := A.prefixPrevision n)
      (by exact ⟨A, hA, rfl⟩)
      (by
        intro P hP Q hQ
        rcases hP with ⟨B, hB, rfl⟩
        rcases hQ with ⟨D, hD, rfl⟩
        exact hAgree B hB D hD)

/-- If two admissible external process laws disagree on a finite-prefix gamble,
then the PLN-style width-complement confidence coordinate is strictly below
one. -/
theorem externalPathLawPrefixEnvelopeWidthComplement_lt_one_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n X < B.prefixPrevision n X) :
    externalPathLawPrefixEnvelopeWidthComplement C n X < 1 := by
  unfold externalPathLawPrefixEnvelopeWidthComplement
  exact
    credalEnvelopeWidthComplement_lt_one_of_strictWidth
      (externalPathLawPrefixCredalSet C n) X
      (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) X)
      (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) X)
      (by
        refine ⟨A.prefixPrevision n, ?_, B.prefixPrevision n, ?_, hlt⟩
        · exact ⟨A, hA, rfl⟩
        · exact ⟨B, hB, rfl⟩)

/-- If all admissible external process laws agree on a finite-prefix gamble,
then the compact path-space credal carrier determines the corresponding
bounded-measurable cylinder observable. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_determines_prefix_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n Y = B.prefixPrevision n Y) :
    boundedMeasurableCredalSetDetermines
      (externalPathLawBoundedMeasurableCompactCredalSet C)
      (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  exact boundedMeasurableCredalSetDetermines_evaluationClosure_of_determines
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
    (externalPathLawPrefixBoundedMeasurableGamble n Y)
    (by
      intro P hP Q hQ
      rcases hP with ⟨A, hA, rfl⟩
      rcases hQ with ⟨B, hB, rfl⟩
      rw [
        ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
        ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision]
      exact hAgree A hA B hB)

/-- If two admissible external process laws disagree on a finite-prefix gamble,
then the compact path-space credal carrier has strict width on the corresponding
bounded-measurable cylinder observable. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_hasStrictWidth_prefix_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    boundedMeasurableCredalSetHasStrictWidth
      (externalPathLawBoundedMeasurableCompactCredalSet C)
      (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
  unfold externalPathLawBoundedMeasurableCompactCredalSet
  exact boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_of_strictWidth
    (externalPathLawBoundedMeasurableCredalSet C)
    (externalPathLawPrefixBoundedMeasurableGamble n Y)
    (by
      refine ⟨A.pathBoundedMeasurablePrevision,
        mem_externalPathLawBoundedMeasurableCredalSet C hA,
        B.pathBoundedMeasurablePrevision,
        mem_externalPathLawBoundedMeasurableCredalSet C hB, ?_⟩
      rw [
        ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
        ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision]
      exact hlt)

/-- Disagreement between two admissible external process laws on a finite-prefix
gamble is realized by compact path-space endpoint completions: one attains the
lower endpoint, one attains the upper endpoint, and the gap is strict. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_exists_endpointPair_prefix_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    ∃ Plo : BoundedMeasurablePrecisePrevision (ℕ → Bool),
      Plo ∈ externalPathLawBoundedMeasurableCompactCredalSet C ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision (ℕ → Bool),
        Phi ∈ externalPathLawBoundedMeasurableCompactCredalSet C ∧
        Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) =
          externalPathLawPrefixLowerEnvelope C n Y ∧
        Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) =
          externalPathLawPrefixUpperEnvelope C n Y ∧
        Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) <
          Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
  have hRawLt :
      A.pathBoundedMeasurablePrevision
          (externalPathLawPrefixBoundedMeasurableGamble n Y) <
        B.pathBoundedMeasurablePrevision
          (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
    rw [
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision]
    exact hlt
  rcases boundedMeasurableEnvelope_exists_endpointPairReadout_evaluationClosure_of_disagreement
      (externalPathLawBoundedMeasurableCredalSet C)
      (externalPathLawPrefixBoundedMeasurableGamble n Y)
      (mem_externalPathLawBoundedMeasurableCredalSet C hA)
      (mem_externalPathLawBoundedMeasurableCredalSet C hB) hRawLt with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hltEndpoints, _hWidth, _hComplement,
      _hMidpoint⟩
  refine ⟨Plo, hPlo, Phi, hPhi, ?_, ?_, hltEndpoints⟩
  · rw [hlo]
    exact
      boundedMeasurableLowerEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixLower
        C n Y
  · rw [hhi]
    exact
      boundedMeasurableUpperEnvelope_externalPathLawCredalSet_prefix_eq_finitePrefixUpper
        C n Y

/-- Compact path-space determination on a finite-prefix cylinder is exactly
agreement of all admissible external process laws on the corresponding prefix
prevision. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_determines_prefix_iff_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableCredalSetDetermines
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ↔
      ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
        ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
          A.prefixPrevision n Y = B.prefixPrevision n Y := by
  constructor
  · intro hDet A hA B hB
    have hEq := hDet A.pathBoundedMeasurablePrevision
      (mem_externalPathLawBoundedMeasurableCompactCredalSet C hA)
      B.pathBoundedMeasurablePrevision
      (mem_externalPathLawBoundedMeasurableCompactCredalSet C hB)
    rw [
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision] at hEq
    exact hEq
  · exact externalPathLawBoundedMeasurableCompactCredalSet_determines_prefix_of_processAgreement
      C hC n Y

/-- Compact path-space strict width on a finite-prefix cylinder is exactly
strict disagreement between two admissible external process laws on the
corresponding prefix prevision.  Thus compactifying the path-law carrier does not
manufacture new PLN imprecision. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_hasStrictWidth_prefix_iff_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    boundedMeasurableCredalSetHasStrictWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) ↔
      ∃ A : ExternalBoolProcessLaw Ω, A ∈ C ∧
        ∃ B : ExternalBoolProcessLaw Ω, B ∈ C ∧
          A.prefixPrevision n Y < B.prefixPrevision n Y := by
  constructor
  · intro hWidth
    have hRaw :
        boundedMeasurableCredalSetHasStrictWidth
          (externalPathLawBoundedMeasurableCredalSet C)
          (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
      unfold externalPathLawBoundedMeasurableCompactCredalSet at hWidth
      exact
        (boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_iff
          (externalPathLawBoundedMeasurableCredalSet C)
          (externalPathLawBoundedMeasurableCredalSet_nonempty C hC)
          (externalPathLawPrefixBoundedMeasurableGamble n Y)).1 hWidth
    rcases hRaw with ⟨P, hP, Q, hQ, hlt⟩
    rcases hP with ⟨A, hA, rfl⟩
    rcases hQ with ⟨B, hB, rfl⟩
    rw [
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision,
      ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision] at hlt
    exact ⟨A, hA, B, hB, hlt⟩
  · rintro ⟨A, hA, B, hB, hlt⟩
    exact externalPathLawBoundedMeasurableCompactCredalSet_hasStrictWidth_prefix_of_processDisagreement
      C n Y hA hB hlt

/-- Disagreement between two admissible external process laws is realized by
Walley dominating completions of the compact path-law natural extension.

This is the de Finetti/path-law specialization of the generic
bounded-measurable Walley endpoint theorem: the endpoint completions dominate
the compact path-law natural extension, are strictly separated on the prefix
cylinder query, and compute the finite-prefix PLN-facing width,
width-complement, and midpoint coordinates. -/
theorem externalPathLawBoundedMeasurableCompactCredalSet_exists_dominatingStrictEndpointPairReadout_prefix_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    ∃ Plo : BoundedMeasurablePrecisePrevision (ℕ → Bool),
      Plo ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCompactCredalSet C)
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
              C ⟨A, hA⟩)) ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision (ℕ → Bool),
        Phi ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCompactCredalSet C)
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
              C ⟨A, hA⟩)) ∧
        Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) =
          externalPathLawPrefixLowerEnvelope C n Y ∧
        Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) =
          externalPathLawPrefixUpperEnvelope C n Y ∧
        Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) <
          Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) ∧
        externalPathLawPrefixEnvelopeWidth C n Y =
          Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) -
            Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) ∧
        externalPathLawPrefixEnvelopeWidthComplement C n Y =
          1 -
            (Phi (externalPathLawPrefixBoundedMeasurableGamble n Y) -
              Plo (externalPathLawPrefixBoundedMeasurableGamble n Y)) ∧
        externalPathLawPrefixEnvelopeMidpoint C n Y =
          (Plo (externalPathLawPrefixBoundedMeasurableGamble n Y) +
            Phi (externalPathLawPrefixBoundedMeasurableGamble n Y)) / 2 := by
  let Cc : BoundedMeasurableCredalSet (ℕ → Bool) :=
    externalPathLawBoundedMeasurableCompactCredalSet C
  let Z : BoundedMeasurableGamble (ℕ → Bool) :=
    externalPathLawPrefixBoundedMeasurableGamble n Y
  have hCc : Cc.Nonempty := by
    dsimp [Cc]
    exact externalPathLawBoundedMeasurableCompactCredalSet_nonempty
      C ⟨A, hA⟩
  have hStrict :
      boundedMeasurableCredalSetHasStrictWidth Cc Z := by
    dsimp [Cc, Z]
    exact
      externalPathLawBoundedMeasurableCompactCredalSet_hasStrictWidth_prefix_of_processDisagreement
        C n Y hA hB hlt
  rcases
      boundedMeasurableNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        Cc hCc Z hStrict with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hltEndpoints, hWidthEq, hCompEq, hMidEq⟩
  have hloPrefix :
      Plo Z = externalPathLawPrefixLowerEnvelope C n Y := by
    calc
      Plo Z = boundedMeasurableNaturalExtensionPrevision Cc hCc Z := hlo
      _ = externalPathLawPrefixLowerEnvelope C n Y := by
        dsimp [Cc, Z, hCc]
        exact
          boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
            C ⟨A, hA⟩ n Y
  have hhiPrefix :
      Phi Z = externalPathLawPrefixUpperEnvelope C n Y := by
    calc
      Phi Z = boundedMeasurableNaturalUpperEnvelopePrevision Cc hCc Z := hhi
      _ = externalPathLawPrefixUpperEnvelope C n Y := by
        dsimp [Cc, Z, hCc]
        exact
          boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
            C ⟨A, hA⟩ n Y
  have hWidthPrefix :
      externalPathLawPrefixEnvelopeWidth C n Y = Phi Z - Plo Z := by
    calc
      externalPathLawPrefixEnvelopeWidth C n Y =
          boundedMeasurableEnvelopeWidth Cc Z := by
        dsimp [Cc, Z]
        exact
          (boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
            C ⟨A, hA⟩ n Y).symm
      _ = Phi Z - Plo Z := hWidthEq
  have hCompPrefix :
      externalPathLawPrefixEnvelopeWidthComplement C n Y =
        1 - (Phi Z - Plo Z) := by
    calc
      externalPathLawPrefixEnvelopeWidthComplement C n Y =
          boundedMeasurableEnvelopeWidthComplement Cc Z := by
        dsimp [Cc, Z]
        exact
          (boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
            C ⟨A, hA⟩ n Y).symm
      _ = 1 - (Phi Z - Plo Z) := hCompEq
  have hMidPrefix :
      externalPathLawPrefixEnvelopeMidpoint C n Y = (Plo Z + Phi Z) / 2 := by
    calc
      externalPathLawPrefixEnvelopeMidpoint C n Y =
          boundedMeasurableEnvelopeMidpoint Cc Z := by
        dsimp [Cc, Z]
        exact
          (boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_finitePrefixMidpoint
            C ⟨A, hA⟩ n Y).symm
      _ = (Plo Z + Phi Z) / 2 := hMidEq
  refine ⟨Plo, ?_, Phi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Cc] using hPlo
  · simpa [Cc] using hPhi
  · simpa [Z] using hloPrefix
  · simpa [Z] using hhiPrefix
  · simpa [Z] using hltEndpoints
  · simpa [Z] using hWidthPrefix
  · simpa [Z] using hCompPrefix
  · simpa [Z] using hMidPrefix

/-- Agreement of all admissible external process laws forces zero compact
path-space envelope width on the finite-prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_zero_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n Y = B.prefixPrevision n Y) :
    boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = 0 := by
  rcases hC with ⟨A, hA⟩
  rw [
    boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
      C ⟨A, hA⟩ n Y]
  exact credalEnvelopeWidth_eq_zero_of_credalSetDetermines
    (externalPathLawPrefixCredalSet C n) Y
    (externalPathLawPrefixCredalSet_nonempty C n ⟨A, hA⟩)
    (finite_credalRange_bddBelow (externalPathLawPrefixCredalSet C n) Y)
    (finite_credalRange_bddAbove (externalPathLawPrefixCredalSet C n) Y)
    (P := A.prefixPrevision n)
    (by exact ⟨A, hA, rfl⟩)
    (by
      intro P hP Q hQ
      rcases hP with ⟨B, hB, rfl⟩
      rcases hQ with ⟨D, hD, rfl⟩
      exact hAgree B hB D hD)

/-- Disagreement between two admissible external process laws gives positive
compact path-space envelope width on the finite-prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_pos_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    0 < boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) := by
  rw [
    boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_finitePrefixWidth
      C hC n Y]
  exact externalPathLawPrefixCredalSet_envelopeWidth_pos_of_processDisagreement
    C n Y hA hB hlt

/-- Agreement of all admissible external process laws makes the compact
path-space width-complement confidence coordinate maximal on the finite-prefix
cylinder observable. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_one_of_processAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
      ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
        A.prefixPrevision n Y = B.prefixPrevision n Y) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) = 1 := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
      C hC n Y]
  exact externalPathLawPrefixEnvelopeWidthComplement_eq_one_of_processAgreement
    C n hC Y hAgree

/-- Disagreement between two admissible external process laws pushes the compact
path-space width-complement confidence coordinate strictly below one on the
finite-prefix cylinder observable. -/
theorem boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_lt_one_of_processDisagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) (hC : C.Nonempty) (n : ℕ)
    (Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {A B : ExternalBoolProcessLaw Ω} (hA : A ∈ C) (hB : B ∈ C)
    (hlt : A.prefixPrevision n Y < B.prefixPrevision n Y) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet C)
        (externalPathLawPrefixBoundedMeasurableGamble n Y) < 1 := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
      C hC n Y]
  exact externalPathLawPrefixEnvelopeWidthComplement_lt_one_of_processDisagreement
    C n Y hA hB hlt

/-- The finite-prefix law obligation is exactly the claim that the prefix
probabilities form a finite probability vector.  This isolates the remaining
analytic work for arbitrary Bernoulli mixtures: prove the finite weights exist
from the mixture integral, then the projective-credal adapter is automatic. -/
theorem bernoulliMixturePrefixLaw_iff_finiteWeights
    (M : BernoulliMixture) (n : ℕ) :
    BernoulliMixturePrefixLaw M n ↔
      ∃ w : PrecisePrevision.FiniteWeights (Fin n → Bool),
        ∀ xs : Fin n → Bool, w.weight xs = M.prob xs := by
  constructor
  · intro h
    exact ⟨h.toFiniteWeights, fun xs => rfl⟩
  · rintro ⟨w, hw⟩
    refine ⟨?_, ?_⟩
    · intro xs
      simpa [← hw xs] using w.nonneg xs
    · calc
        ∑ xs : (Fin n → Bool), M.prob xs =
            ∑ xs : (Fin n → Bool), w.weight xs := by
          apply Finset.sum_congr rfl
          intro xs _hxs
          exact (hw xs).symm
        _ = 1 := w.total

/-- A credal set of Bernoulli mixtures induces a finite-prefix credal set of
precise previsions once each mixture has its prefix-law obligations discharged. -/
noncomputable def bernoulliMixturePrefixCredalSet
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    CredalPrevisionSet (Fin n → Bool) :=
  {P | ∃ M : BernoulliMixture, ∃ hM : M ∈ C,
    P = (hLaw M hM).toPrecisePrevision}

theorem bernoulliMixturePrefixCredalSet_nonempty
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    (bernoulliMixturePrefixCredalSet C n hLaw).Nonempty := by
  rcases hC with ⟨M, hM⟩
  exact ⟨(hLaw M hM).toPrecisePrevision, M, hM, rfl⟩

/-- The lower envelope over an imprecise de Finetti credal set at a finite
prefix. -/
noncomputable def impreciseDeFinettiPrefixLowerEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  lowerEnvelope (bernoulliMixturePrefixCredalSet C n hLaw)

/-- The imprecise de Finetti prefix lower envelope is below every admissible
mixture-prefix precise prevision. -/
theorem impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    {M : BernoulliMixture} (hM : M ∈ C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    impreciseDeFinettiPrefixLowerEnvelope C n hLaw X ≤
      (hLaw M hM).toPrecisePrevision X := by
  simpa [impreciseDeFinettiPrefixLowerEnvelope] using
    finiteLowerEnvelopePrevision_le_completion
      (bernoulliMixturePrefixCredalSet C n hLaw)
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw ⟨M, hM⟩)
      (P := (hLaw M hM).toPrecisePrevision)
      (by exact ⟨M, hM, rfl⟩) X

/-- The imprecise de Finetti prefix lower envelope is the greatest lower
prevision dominated by every admissible mixture-prefix precise prevision. -/
theorem impreciseDeFinettiPrefixLowerEnvelope_greatest_lower_bound
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (L : LowerPrevision (Fin n → Bool))
    (hL : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool), L X ≤ (hLaw M hM).toPrecisePrevision X)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    L X ≤ impreciseDeFinettiPrefixLowerEnvelope C n hLaw X := by
  simpa [impreciseDeFinettiPrefixLowerEnvelope] using
    finiteLowerEnvelopePrevision_greatest_lower_bound
      (bernoulliMixturePrefixCredalSet C n hLaw)
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw hC) L
      (by
        intro P hP Y
        rcases hP with ⟨M, hM, rfl⟩
        exact hL M hM Y)
      X

/-- The upper envelope over an imprecise de Finetti credal set at a finite
prefix. -/
noncomputable def impreciseDeFinettiPrefixUpperEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  upperEnvelope (bernoulliMixturePrefixCredalSet C n hLaw)

/-- The finite-prefix credal width induced by an imprecise de Finetti set of
Bernoulli mixtures. -/
noncomputable def impreciseDeFinettiPrefixEnvelopeWidth
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeWidth (bernoulliMixturePrefixCredalSet C n hLaw)

/-- The finite-prefix width-complement induced by an imprecise de Finetti set
of Bernoulli mixtures, used as the PLN-style confidence coordinate. -/
noncomputable def impreciseDeFinettiPrefixEnvelopeWidthComplement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeWidthComplement (bernoulliMixturePrefixCredalSet C n hLaw)

/-- The finite-prefix midpoint induced by an imprecise de Finetti set of
Bernoulli mixtures, used as the PLN-style strength coordinate. -/
noncomputable def impreciseDeFinettiPrefixEnvelopeMidpoint
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool) → ℝ :=
  credalEnvelopeMidpoint (bernoulliMixturePrefixCredalSet C n hLaw)

/-- Every admissible Bernoulli-mixture prefix prevision is below the imprecise
de Finetti prefix upper envelope. -/
theorem impreciseDeFinettiPrefixPrevision_le_upperEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    {M : BernoulliMixture} (hM : M ∈ C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (hLaw M hM).toPrecisePrevision X ≤
      impreciseDeFinettiPrefixUpperEnvelope C n hLaw X := by
  simpa [impreciseDeFinettiPrefixUpperEnvelope] using
    finiteCompletion_le_upperEnvelopePrevision
      (bernoulliMixturePrefixCredalSet C n hLaw)
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw ⟨M, hM⟩)
      (P := (hLaw M hM).toPrecisePrevision)
      (by exact ⟨M, hM, rfl⟩) X

/-- The imprecise de Finetti prefix upper envelope is the least upper
prevision dominating every admissible mixture-prefix precise prevision. -/
theorem impreciseDeFinettiPrefixUpperEnvelope_least_upper_bound
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (U : UpperPrevision (Fin n → Bool))
    (hU : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool), (hLaw M hM).toPrecisePrevision X ≤ U X)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    impreciseDeFinettiPrefixUpperEnvelope C n hLaw X ≤ U X := by
  simpa [impreciseDeFinettiPrefixUpperEnvelope] using
    finiteUpperEnvelopePrevision_least_upper_bound
      (bernoulliMixturePrefixCredalSet C n hLaw)
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw hC) U
      (by
        intro P hP Y
        rcases hP with ⟨M, hM, rfl⟩
        exact hU M hM Y)
      X

/-! ## Finite-prefix de Finetti credal sets as projective specs -/

/-- The finite-prefix credal set of Bernoulli mixtures as a one-window
projective local credal specification.  This reuses the generic identity-window
adapter: no new projective machinery is duplicated. -/
noncomputable def bernoulliMixturePrefixProjectiveSpec
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    ProjectiveLocalCredalSpec PUnit.{1} (Fin n → Bool) :=
  identityCredalProjectiveSpec (bernoulliMixturePrefixCredalSet C n hLaw)

@[simp] theorem bernoulliMixturePrefixProjectiveSpec_projectiveLimitCredalSet
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).projectiveLimitCredalSet =
      bernoulliMixturePrefixCredalSet C n hLaw := by
  simp [bernoulliMixturePrefixProjectiveSpec]

theorem bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasCompatibleCompletion := by
  rw [bernoulliMixturePrefixProjectiveSpec,
    identityCredalProjectiveSpec_hasCompatibleCompletion_iff]
  exact bernoulliMixturePrefixCredalSet_nonempty C n hLaw hC

/-- A finite Bernoulli-mixture prefix natural extension is Walley-coherent as a
finite lower envelope of precise mixture-prefix previsions. -/
theorem bernoulliMixturePrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_isCoherent
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
      (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)).isCoherent :=
  ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_isCoherent
    (S := bernoulliMixturePrefixProjectiveSpec C n hLaw)
    (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)

/-- A finite Bernoulli-mixture prefix natural extension is exactly the lower
envelope of the precise previsions dominating it. -/
theorem bernoulliMixturePrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    hasExactDominatingPreciseEnvelope
      ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)) :=
  ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S := bernoulliMixturePrefixProjectiveSpec C n hLaw)
    (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)

/-- The projective natural extension of a finite-prefix de Finetti credal set
is exactly its Walley lower envelope. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalNaturalExtension X =
      impreciseDeFinettiPrefixLowerEnvelope C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalNaturalExtension,
    impreciseDeFinettiPrefixLowerEnvelope]

/-- The projective upper envelope of a finite-prefix de Finetti credal set is
exactly its upper envelope. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_upperEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    upperEnvelope
        (bernoulliMixturePrefixProjectiveSpec C n hLaw).projectiveLimitCredalSet X =
      impreciseDeFinettiPrefixUpperEnvelope C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    impreciseDeFinettiPrefixUpperEnvelope]

/-- The packaged finite projective Walley natural extension of an imprecise
Bernoulli-mixture prefix credal set is exactly its lower envelope. -/
theorem bernoulliMixturePrefixProjectiveSpec_finiteGlobalNaturalExtensionPrevision_eq_lowerEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)) X =
      impreciseDeFinettiPrefixLowerEnvelope C n hLaw X := by
  rw [ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_apply]
  rw [bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension]

/-- The packaged finite projective Walley upper envelope of an imprecise
Bernoulli-mixture prefix credal set is exactly its upper envelope. -/
theorem bernoulliMixturePrefixProjectiveSpec_finiteGlobalUpperEnvelopePrevision_eq_upperEnvelope
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalUpperEnvelopePrevision
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion C n hLaw hC)) X =
      impreciseDeFinettiPrefixUpperEnvelope C n hLaw X := by
  rw [ProjectiveLocalCredalSpec.finiteGlobalUpperEnvelopePrevision_apply]
  rw [bernoulliMixturePrefixProjectiveSpec_upperEnvelope]

/-- The projective global width of a finite-prefix de Finetti credal set is
exactly its prefix envelope width. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeWidth X =
      impreciseDeFinettiPrefixEnvelopeWidth C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    impreciseDeFinettiPrefixEnvelopeWidth]

/-- The projective global width-complement of a finite-prefix de Finetti
credal set is exactly its prefix width-complement. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeWidthComplement X =
      impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    impreciseDeFinettiPrefixEnvelopeWidthComplement]

/-- The projective global midpoint of a finite-prefix de Finetti credal set is
exactly its prefix midpoint. -/
@[simp] theorem bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeMidpoint X =
      impreciseDeFinettiPrefixEnvelopeMidpoint C n hLaw X := by
  simp [bernoulliMixturePrefixProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    impreciseDeFinettiPrefixEnvelopeMidpoint]

/-- If all admissible Bernoulli mixtures agree on a finite-prefix gamble, then
the projective de Finetti prefix credal set determines that gamble. -/
theorem bernoulliMixturePrefixProjectiveSpec_determinesGlobalGamble_of_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        (hLaw M hM).toPrecisePrevision X =
          (hLaw N hN).toPrecisePrevision X) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).determinesGlobalGamble X := by
  rw [bernoulliMixturePrefixProjectiveSpec,
    identityCredalProjectiveSpec_determinesGlobalGamble_iff]
  intro P hP Q hQ
  rcases hP with ⟨M, hM, rfl⟩
  rcases hQ with ⟨N, hN, rfl⟩
  exact hAgree M hM N hN

/-- If two admissible Bernoulli mixtures disagree on a finite-prefix gamble, the
projective de Finetti prefix credal set has strict global width on that gamble. -/
theorem bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth X := by
  rw [bernoulliMixturePrefixProjectiveSpec,
    identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
  refine ⟨(hLaw M hM).toPrecisePrevision, ?_,
    (hLaw N hN).toPrecisePrevision, ?_, hlt⟩
  · exact ⟨M, hM, rfl⟩
  · exact ⟨N, hN, rfl⟩

/-- Mixture disagreement produces a nontrivial finite-prefix de Finetti
lower/upper envelope.  Boundedness is automatic because the prefix state space
is finite. -/
theorem bernoulliMixturePrefixCredalSet_lowerUpperEnvelope_nontrivial_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    lowerEnvelope (bernoulliMixturePrefixCredalSet C n hLaw) X <
      upperEnvelope (bernoulliMixturePrefixCredalSet C n hLaw) X := by
  exact
    lower_upperEnvelope_nontrivial_of_strictWidth
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (by
        refine ⟨(hLaw M hM).toPrecisePrevision, ?_,
          (hLaw N hN).toPrecisePrevision, ?_, hlt⟩
        · exact ⟨M, hM, rfl⟩
        · exact ⟨N, hN, rfl⟩)

/-- The same finite-prefix de Finetti disagreement expressed as positive
prefix credal envelope width. -/
theorem bernoulliMixturePrefixCredalSet_envelopeWidth_pos_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    0 < credalEnvelopeWidth (bernoulliMixturePrefixCredalSet C n hLaw) X := by
  exact
    credalEnvelopeWidth_pos_of_strictWidth
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (by
        refine ⟨(hLaw M hM).toPrecisePrevision, ?_,
          (hLaw N hN).toPrecisePrevision, ?_, hlt⟩
        · exact ⟨M, hM, rfl⟩
        · exact ⟨N, hN, rfl⟩)

/-- If all admissible Bernoulli mixtures agree on a finite-prefix gamble, then
the imprecise de Finetti width-complement confidence coordinate is maximal. -/
theorem impreciseDeFinettiPrefixEnvelopeWidthComplement_eq_one_of_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        (hLaw M hM).toPrecisePrevision X =
          (hLaw N hN).toPrecisePrevision X) :
    impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X = 1 := by
  rcases hC with ⟨M, hM⟩
  unfold impreciseDeFinettiPrefixEnvelopeWidthComplement
  exact
    credalEnvelopeWidthComplement_eq_one_of_credalSetDetermines
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw ⟨M, hM⟩)
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (P := (hLaw M hM).toPrecisePrevision)
      (by exact ⟨M, hM, rfl⟩)
      (by
        intro P hP Q hQ
        rcases hP with ⟨N, hN, rfl⟩
        rcases hQ with ⟨O, hO, rfl⟩
        exact hAgree N hN O hO)

/-- If all admissible Bernoulli mixtures agree on a finite-prefix gamble, then
the imprecise de Finetti prefix interval has zero width. -/
theorem impreciseDeFinettiPrefixEnvelopeWidth_eq_zero_of_mixtureAgreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        (hLaw M hM).toPrecisePrevision X =
          (hLaw N hN).toPrecisePrevision X) :
    impreciseDeFinettiPrefixEnvelopeWidth C n hLaw X = 0 := by
  rcases hC with ⟨M, hM⟩
  unfold impreciseDeFinettiPrefixEnvelopeWidth
  exact
    credalEnvelopeWidth_eq_zero_of_credalSetDetermines
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (bernoulliMixturePrefixCredalSet_nonempty C n hLaw ⟨M, hM⟩)
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (P := (hLaw M hM).toPrecisePrevision)
      (by exact ⟨M, hM, rfl⟩)
      (by
        intro P hP Q hQ
        rcases hP with ⟨N, hN, rfl⟩
        rcases hQ with ⟨O, hO, rfl⟩
        exact hAgree N hN O hO)

/-- If two admissible Bernoulli mixtures disagree on a finite-prefix gamble,
then the imprecise de Finetti width-complement confidence coordinate is
strictly below one. -/
theorem impreciseDeFinettiPrefixEnvelopeWidthComplement_lt_one_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X < 1 := by
  unfold impreciseDeFinettiPrefixEnvelopeWidthComplement
  exact
    credalEnvelopeWidthComplement_lt_one_of_strictWidth
      (bernoulliMixturePrefixCredalSet C n hLaw) X
      (finite_credalRange_bddBelow
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (finite_credalRange_bddAbove
        (bernoulliMixturePrefixCredalSet C n hLaw) X)
      (by
        refine ⟨(hLaw M hM).toPrecisePrevision, ?_,
          (hLaw N hN).toPrecisePrevision, ?_, hlt⟩
        · exact ⟨M, hM, rfl⟩
        · exact ⟨N, hN, rfl⟩)

/-- Disagreement between two admissible Bernoulli mixtures is realized by
Walley dominating completions of the finite-prefix natural extension.

The endpoint completions need not be admissible mixtures themselves.  They are
precise previsions dominating the finite-prefix lower envelope, and they touch
the lower and conjugate upper endpoints that compute the imprecise de Finetti
PLN-facing width, width-complement, and midpoint coordinates. -/
theorem impreciseDeFinettiPrefix_exists_dominatingStrictEndpointPairReadout_of_mixtureDisagreement
    (C : Set BernoulliMixture) (n : ℕ)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C →
      BernoulliMixturePrefixLaw M n)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
      (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      (hLaw M hM).toPrecisePrevision X <
        (hLaw N hN).toPrecisePrevision X) :
    ∃ Plo : PrecisePrevision (Fin n → Bool),
      Plo ∈ dominatingPreciseCompletions
          ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
            (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
              C n hLaw ⟨M, hM⟩)) ∧
      ∃ Phi : PrecisePrevision (Fin n → Bool),
        Phi ∈ dominatingPreciseCompletions
          ((bernoulliMixturePrefixProjectiveSpec C n hLaw).finiteGlobalNaturalExtensionPrevision
            (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
              C n hLaw ⟨M, hM⟩)) ∧
        Plo X = impreciseDeFinettiPrefixLowerEnvelope C n hLaw X ∧
        Phi X = impreciseDeFinettiPrefixUpperEnvelope C n hLaw X ∧
        Plo X < Phi X ∧
        impreciseDeFinettiPrefixEnvelopeWidth C n hLaw X =
          Phi X - Plo X ∧
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X =
          1 - (Phi X - Plo X) ∧
        impreciseDeFinettiPrefixEnvelopeMidpoint C n hLaw X =
          (Plo X + Phi X) / 2 := by
  have hProjectiveWidth :
      (bernoulliMixturePrefixProjectiveSpec C n hLaw).hasStrictGlobalWidth X :=
    bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
      C n hLaw X hM hN hlt
  rcases
      ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        (S := bernoulliMixturePrefixProjectiveSpec C n hLaw)
        (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
          C n hLaw ⟨M, hM⟩) X hProjectiveWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hltEndpoints, hWidthEq, hCompEq, hMidEq⟩
  have hloPrefix :
      Plo X = impreciseDeFinettiPrefixLowerEnvelope C n hLaw X :=
    hlo.trans (bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension
      C n hLaw X)
  have hhiPrefix :
      Phi X = impreciseDeFinettiPrefixUpperEnvelope C n hLaw X :=
    hhi.trans (bernoulliMixturePrefixProjectiveSpec_upperEnvelope C n hLaw X)
  refine ⟨Plo, ?_, Phi, ?_, hloPrefix, hhiPrefix, hltEndpoints, ?_, ?_, ?_⟩
  · exact hPlo
  · exact hPhi
  · calc
      impreciseDeFinettiPrefixEnvelopeWidth C n hLaw X =
          (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeWidth X :=
        (bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth C n hLaw X).symm
      _ = Phi X - Plo X := hWidthEq
  · calc
      impreciseDeFinettiPrefixEnvelopeWidthComplement C n hLaw X =
          (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeWidthComplement X :=
        (bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement C n hLaw X).symm
      _ = 1 - (Phi X - Plo X) := hCompEq
  · calc
      impreciseDeFinettiPrefixEnvelopeMidpoint C n hLaw X =
          (bernoulliMixturePrefixProjectiveSpec C n hLaw).globalEnvelopeMidpoint X :=
        (bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint C n hLaw X).symm
      _ = (Plo X + Phi X) / 2 := hMidEq

/-- Adapter from a de Finetti Bernoulli-mixture factorization into a projective
credal specification.  The `mixtureCompatible` field is the honest gluing map:
it says which projective credal completion the latent mixture induces. -/
structure DeFinettiProjectiveCredalSpecialization
    (X : ℕ → Ω → Bool) (μ : Measure Ω) where
  projectiveSpec : ProjectiveLocalCredalSpec Window Global
  completionOfMixture : BernoulliMixture → PrecisePrevision Global
  mixtureCompatible :
    ∀ M : BernoulliMixture, Represents M X μ →
      completionOfMixture M ∈ projectiveSpec.projectiveLimitCredalSet

namespace DeFinettiProjectiveCredalSpecialization

variable {X : ℕ → Ω → Bool} {μ : Measure Ω}

/-- A de Finetti factorization, plus an explicit adapter from mixtures to
projective precise previsions, gives a nonempty compatible projective credal
set. -/
theorem hasCompatibleCompletion_of_factorization
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := Window) (Global := Global) X μ)
    (hfac : CategoricalDeFinettiFactorization X μ) :
    D.projectiveSpec.hasCompatibleCompletion := by
  let M := latentBernoulliMixtureOf hfac
  exact D.projectiveSpec.projectiveLimitCredalSet_nonempty_of_completion
    (P := D.completionOfMixture M)
    (by
      intro i
      exact D.mixtureCompatible M
        (latentBernoulliMixtureOf_represents hfac) i)

/-- Exchangeability supplies the de Finetti factorization; the adapter supplies
the projective credal completion. -/
theorem hasCompatibleCompletion_of_exchangeable
    (D : DeFinettiProjectiveCredalSpecialization
      (Window := Window) (Global := Global) X μ)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    D.projectiveSpec.hasCompatibleCompletion :=
  D.hasCompatibleCompletion_of_factorization
    (categoricalDeFinetti_factorization_of_exchangeable X μ hX hexch)

end DeFinettiProjectiveCredalSpecialization

/-! ## Imprecise de Finetti process-law crown -/

/-- Select the finite-prefix law at window `n` from an all-prefix family of
Bernoulli-mixture laws. -/
def bernoulliMixturePrefixLawAt
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (n : ℕ) :
    ∀ M : BernoulliMixture, M ∈ C → BernoulliMixturePrefixLaw M n :=
  fun M hM => hLaw M hM n

/-- The canonical infinite Boolean prefix cylinder system: window `n` is the
first `n` bits of an infinite Boolean path. -/
def bernoulliMixturePrefixProcessCylinderSystem :
    ProjectiveCylinderSystem ℕ (ℕ → Bool) where
  Local n := Fin n → Bool
  project n ω := fun i => ω i
  restrict := fun {i j} hij xs => fun k => xs (Fin.castLE hij k)
  project_restrict := by
    intro i j hij ω
    rfl

/-- The canonical joint prefix length for a finite family of Boolean-prefix
windows: use the largest requested prefix length, with `0` for the empty
family. -/
def prefixWindowJointLength (u : Finset ℕ) : ℕ :=
  u.sup (fun n : ℕ => n)

/-- Every requested prefix window embeds into the canonical joint prefix
window for the finite family. -/
theorem prefixWindow_le_jointLength
    (u : Finset ℕ) {i : ℕ} (hi : i ∈ u) :
    i ≤ prefixWindowJointLength u := by
  exact Finset.le_sup (f := fun n : ℕ => n) hi

/-- The process-level local lower-prevision specification generated by an
imprecise de Finetti set of Bernoulli mixtures.

At each finite prefix length `n`, the local lower prevision is exactly the lower
envelope of the admissible Bernoulli-mixture prefix previsions. -/
noncomputable def bernoulliMixturePrefixProcessLowerSpec
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    ProjectiveLocalLowerPrevisionSpec ℕ (ℕ → Bool) where
  cylinders := bernoulliMixturePrefixProcessCylinderSystem
  localLower n := by
    change LowerPrevision (Fin n → Bool)
    exact finiteLowerEnvelopePrevision
      (bernoulliMixturePrefixCredalSet C n
        (bernoulliMixturePrefixLawAt C hLaw n))
      (bernoulliMixturePrefixCredalSet_nonempty C n
        (bernoulliMixturePrefixLawAt C hLaw n) hC)

@[simp] theorem bernoulliMixturePrefixProcessLowerSpec_cylinders
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).cylinders =
      bernoulliMixturePrefixProcessCylinderSystem :=
  rfl

@[simp] theorem bernoulliMixturePrefixProcessLowerSpec_localLower_apply
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).localLower n X =
      impreciseDeFinettiPrefixLowerEnvelope C n
        (bernoulliMixturePrefixLawAt C hLaw n) X :=
  by
    change
      finiteLowerEnvelopePrevision
          (bernoulliMixturePrefixCredalSet C n
            (bernoulliMixturePrefixLawAt C hLaw n))
          (bernoulliMixturePrefixCredalSet_nonempty C n
          (bernoulliMixturePrefixLawAt C hLaw n) hC) X =
        impreciseDeFinettiPrefixLowerEnvelope C n
          (bernoulliMixturePrefixLawAt C hLaw n) X
    rfl

/-- Canonical finite joint-window system for the Boolean prefix process.

For a finite set of prefix lengths `u`, the joint state is the largest requested
Boolean prefix.  Each member window is obtained by truncating this largest
prefix.  This removes an arbitrary-`J` choice from downstream finite-window
realization statements; the remaining mathematical work is the joint prevision
and carrier-realization proof for this canonical system. -/
def bernoulliMixturePrefixProcessFiniteJointWindowSystem
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC) where
  Joint u := Fin (prefixWindowJointLength u) → Bool
  restrict u _i hi xs := fun k =>
    xs (Fin.castLE (prefixWindow_le_jointLength u hi) k)

@[simp] theorem bernoulliMixturePrefixProcessFiniteJointWindowSystem_restrict_apply
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (u : Finset ℕ) (i : ℕ) (hi : i ∈ u)
    (xs : Fin (prefixWindowJointLength u) → Bool) (k : Fin i) :
    (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC).restrict
        u i hi xs k =
      xs (Fin.castLE (prefixWindow_le_jointLength u hi) k) :=
  rfl

/-- Exact finite-prefix marginal consistency for an imprecise Bernoulli-mixture
family, stated on the canonical largest-prefix joint-window system.

For every admissible mixture in `C`, the law on the largest requested prefix
must marginalize to the law on each member prefix.  This is the non-circular
finite-window hypothesis that feeds the generic compact/FIP crown without
assuming an arbitrary local-coherence witness. -/
def bernoulliMixturePrefixProcessMarginalConsistent
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n) : Prop :=
  ∀ (M : BernoulliMixture) (hM : M ∈ C)
    (u : Finset ℕ) {i : ℕ} (hi : i ∈ u)
    (X : Gamble (Fin i → Bool)),
    ((bernoulliMixturePrefixLawAt C hLaw (prefixWindowJointLength u)) M hM).toPrecisePrevision
      (fun xs => X (fun t =>
        xs (Fin.castLE (prefixWindow_le_jointLength u hi) t))) =
    ((bernoulliMixturePrefixLawAt C hLaw i) M hM).toPrecisePrevision X

/-- Prefix marginal consistency supplies local coherence for the canonical
largest-prefix finite joint-window system of an imprecise Bernoulli-mixture
family. -/
theorem bernoulliMixturePrefixProcessFiniteJointWindowSystem_localCoherent_of_marginalConsistent
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (hMarginal :
      bernoulliMixturePrefixProcessMarginalConsistent C hLaw) :
    (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).finiteWindowLocalCoherent
      (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC) := by
  have hCw : C.Nonempty := hC
  rcases hC with ⟨M₀, hM₀⟩
  intro u
  let R : PrecisePrevision
      ((bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hCw).Joint u) :=
    ((bernoulliMixturePrefixLawAt C hLaw (prefixWindowJointLength u)) M₀ hM₀).toPrecisePrevision
  refine ⟨R, ?_⟩
  intro i hi
  rw [mem_dominatingPreciseCompletions]
  intro X
  have hLower :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hCw).localLower i X ≤
        ((bernoulliMixturePrefixLawAt C hLaw i) M₀ hM₀).toPrecisePrevision X := by
    rw [bernoulliMixturePrefixProcessLowerSpec_localLower_apply]
    exact
      impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
        C i (bernoulliMixturePrefixLawAt C hLaw i) hM₀ X
  have hMarginalEq :
      (bernoulliMixturePrefixProcessFiniteJointWindowSystem
          C hLaw hCw).jointMarginalPrevision u i hi R X =
        ((bernoulliMixturePrefixLawAt C hLaw i) M₀ hM₀).toPrecisePrevision X := by
    rw [ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem.jointMarginalPrevision_apply]
    simpa [R, ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem.jointCylinderGamble,
      bernoulliMixturePrefixProcessFiniteJointWindowSystem] using
      (hMarginal M₀ hM₀ u (i := i) hi X)
  exact hLower.trans_eq hMarginalEq.symm

/-- The canonical analytic Bernoulli-mixture prefix laws are automatically
marginal-consistent on the largest-prefix finite-window system. -/
theorem bernoulliMixturePrefixProcessMarginalConsistent_analytic
    (C : Set BernoulliMixture) :
    bernoulliMixturePrefixProcessMarginalConsistent C
      (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) := by
  intro M _hM u i hi X
  exact bernoulliMixturePrefixPrevision_takePrefix_eq
    (M := M) (hmn := prefixWindow_le_jointLength u hi) X

/-- Finite-window realization/FIP completion for the imprecise de Finetti
prefix-process specification.

The two finite-window hypotheses are intentionally explicit: `hLocal` supplies a
finite joint model for every finite set of prefix windows, while `hRealize`
asserts that such finite joint previsions are realized inside the chosen compact
global carrier. -/
theorem impreciseDeFinetti_processLawCompatibleCompletion_of_finiteWindowRealization
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).localLower n)})
    (J : ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC))
    (hLocal :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).finiteWindowLocalCoherent J)
    (hRealize :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).jointPrevisionsRealizedInCarrier
        J carrier) :
    ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).toCredalSpec).hasCompatibleCompletion := by
  let S := bernoulliMixturePrefixProcessLowerSpec C hLaw hC
  have hFIP : S.finiteWindowCompatibleInCarrier carrier :=
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      S J carrier hLocal hRealize
  exact
    S.hasCompatibleCompletion_of_finiteWindowCompatibleInCarrier carrier
      hCompact hCarrierConvex hClosed hFIP

/-- Compact/FIP completion for the imprecise de Finetti prefix-process
specification, stated at the minimal finite-window compatibility boundary.

The more structured finite-joint-window realization theorem above is one way to
prove `hFIP`; this theorem exposes the smaller assumption consumed by the
compact projective completion theorem. -/
theorem impreciseDeFinetti_processLawCompatibleCompletion_of_finiteWindowCompatibleInCarrier
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).localLower n)})
    (hFIP :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).finiteWindowCompatibleInCarrier
        carrier) :
    ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).toCredalSpec).hasCompatibleCompletion := by
  exact
    ProjectiveLocalLowerPrevisionSpec.hasCompatibleCompletion_of_finiteWindowCompatibleInCarrier
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC)
      carrier hCompact hCarrierConvex hClosed hFIP

/-- Paper-facing package for the imprecise de Finetti process-law crown.  It
combines the process-level compact/FIP completion with finite-prefix PLN
lower/upper-envelope and confidence-width readouts. -/
structure ImpreciseDeFinettiProcessLawCrown
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) where
  processCompatibleCompletion :
    ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).toCredalSpec).hasCompatibleCompletion
  prefixCompatibleCompletion :
    ∀ n : ℕ,
      (bernoulliMixturePrefixProjectiveSpec C n
        (bernoulliMixturePrefixLawAt C hLaw n)).hasCompatibleCompletion
  prefixLowerEnvelopeReadout :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n
        (bernoulliMixturePrefixLawAt C hLaw n)).globalNaturalExtension X =
        impreciseDeFinettiPrefixLowerEnvelope C n
          (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixUpperEnvelopeReadout :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      upperEnvelope
          (bernoulliMixturePrefixProjectiveSpec C n
            (bernoulliMixturePrefixLawAt C hLaw n)).projectiveLimitCredalSet X =
        impreciseDeFinettiPrefixUpperEnvelope C n
          (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixWidthComplementReadout :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n
        (bernoulliMixturePrefixLawAt C hLaw n)).globalEnvelopeWidthComplement X =
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n
          (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixMidpointReadout :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n
        (bernoulliMixturePrefixLawAt C hLaw n)).globalEnvelopeMidpoint X =
        impreciseDeFinettiPrefixEnvelopeMidpoint C n
          (bernoulliMixturePrefixLawAt C hLaw n) X
  agreementDetermines :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X =
            ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) →
        (bernoulliMixturePrefixProjectiveSpec C n
          (bernoulliMixturePrefixLawAt C hLaw n)).determinesGlobalGamble X
  agreementWidthComplement_eq_one :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X =
            ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) →
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n
          (bernoulliMixturePrefixLawAt C hLaw n) X = 1
  disagreementStrictWidth :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool))
      {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C),
      ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X <
        ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X →
        (bernoulliMixturePrefixProjectiveSpec C n
          (bernoulliMixturePrefixLawAt C hLaw n)).hasStrictGlobalWidth X
  disagreementEnvelopeWidth_pos :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool))
      {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C),
      ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X <
        ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X →
        0 < impreciseDeFinettiPrefixEnvelopeWidth C n
          (bernoulliMixturePrefixLawAt C hLaw n) X
  disagreementWidthComplement_lt_one :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool))
      {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C),
      ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X <
        ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X →
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n
          (bernoulliMixturePrefixLawAt C hLaw n) X < 1

/-- Agreement of all admissible mixtures on a prefix query gives a determined
projective query. -/
theorem impreciseDeFinetti_prefixAgreement_projectiveDetermines
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (n : ℕ) (X : Gamble (Fin n → Bool))
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X =
          ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) :
    (bernoulliMixturePrefixProjectiveSpec C n
      (bernoulliMixturePrefixLawAt C hLaw n)).determinesGlobalGamble X :=
  bernoulliMixturePrefixProjectiveSpec_determinesGlobalGamble_of_mixtureAgreement
    C n (bernoulliMixturePrefixLawAt C hLaw n) X hAgree

/-- Agreement of all admissible mixtures on a prefix query gives maximal
PLN-style confidence. -/
theorem impreciseDeFinetti_prefixAgreement_confidence_eq_one
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) (n : ℕ) (X : Gamble (Fin n → Bool))
    (hAgree : ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X =
          ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) :
    impreciseDeFinettiPrefixEnvelopeWidthComplement C n
      (bernoulliMixturePrefixLawAt C hLaw n) X = 1 :=
  impreciseDeFinettiPrefixEnvelopeWidthComplement_eq_one_of_mixtureAgreement
    C n (bernoulliMixturePrefixLawAt C hLaw n) hC X hAgree

/-- Disagreement of two admissible mixtures on a prefix query gives strict
projective credal width. -/
theorem impreciseDeFinetti_prefixDisagreement_strictWidth
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (n : ℕ) (X : Gamble (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X <
        ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) :
    (bernoulliMixturePrefixProjectiveSpec C n
      (bernoulliMixturePrefixLawAt C hLaw n)).hasStrictGlobalWidth X :=
  bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
    C n (bernoulliMixturePrefixLawAt C hLaw n) X hM hN hlt

/-- Disagreement of two admissible mixtures on a prefix query gives positive
credal envelope width. -/
theorem impreciseDeFinetti_prefixDisagreement_envelopeWidth_pos
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (n : ℕ) (X : Gamble (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X <
        ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) :
    0 < impreciseDeFinettiPrefixEnvelopeWidth C n
      (bernoulliMixturePrefixLawAt C hLaw n) X := by
  simpa [impreciseDeFinettiPrefixEnvelopeWidth] using
    bernoulliMixturePrefixCredalSet_envelopeWidth_pos_of_mixtureDisagreement
      C n (bernoulliMixturePrefixLawAt C hLaw n) X hM hN hlt

/-- Disagreement of two admissible mixtures on a prefix query gives confidence
strictly below one. -/
theorem impreciseDeFinetti_prefixDisagreement_confidence_lt_one
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (n : ℕ) (X : Gamble (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X <
        ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) :
    impreciseDeFinettiPrefixEnvelopeWidthComplement C n
      (bernoulliMixturePrefixLawAt C hLaw n) X < 1 :=
  impreciseDeFinettiPrefixEnvelopeWidthComplement_lt_one_of_mixtureDisagreement
    C n (bernoulliMixturePrefixLawAt C hLaw n) X hM hN hlt

/-! ### Posterior mixtures as singleton projective prefix systems -/

/-- The singleton de Finetti-mixture set generated by a normalized posterior
after `k` successes and `l` failures. -/
noncomputable def posteriorBernoulliMixtureSet
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) : Set BernoulliMixture :=
  {M.posteriorBernoulliMixture k l hZ}

theorem posteriorBernoulliMixtureSet_nonempty
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (posteriorBernoulliMixtureSet M k l hZ).Nonempty := by
  exact ⟨M.posteriorBernoulliMixture k l hZ, rfl⟩

theorem posteriorBernoulliMixture_mem_posteriorSet
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    M.posteriorBernoulliMixture k l hZ ∈
      posteriorBernoulliMixtureSet M k l hZ :=
  rfl

/-- Every member of the posterior singleton set has analytic Bernoulli prefix
laws. -/
def posteriorBernoulliMixtureSetPrefixLaw
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    ∀ P : BernoulliMixture, P ∈ posteriorBernoulliMixtureSet M k l hZ →
      ∀ n : ℕ, BernoulliMixturePrefixLaw P n := by
  intro P hP n
  have hEq : P = M.posteriorBernoulliMixture k l hZ := by
    simpa [posteriorBernoulliMixtureSet] using hP
  subst P
  exact bernoulliMixturePrefixLaw_analytic
    (M.posteriorBernoulliMixture k l hZ) n

/-- The finite-window prefix-law selector for the posterior singleton set. -/
abbrev posteriorBernoulliMixturePrefixLawAt
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) (n : ℕ) :
    ∀ P : BernoulliMixture, P ∈ posteriorBernoulliMixtureSet M k l hZ →
      BernoulliMixturePrefixLaw P n :=
  bernoulliMixturePrefixLawAt (posteriorBernoulliMixtureSet M k l hZ)
    (posteriorBernoulliMixtureSetPrefixLaw M k l hZ) n

/-! ### Posterior mixture families as imprecise revision envelopes -/

/-- Updating every prior mixture in a credal family by the same observed counts
gives the posterior credal family.  The nonzero-normalizer hypothesis is kept
memberwise; it is the honest Bayes gate for count revision. -/
noncomputable def posteriorBernoulliMixtureFamilySet
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0) : Set BernoulliMixture :=
  {P | ∃ M : BernoulliMixture, ∃ hM : M ∈ C,
    P = M.posteriorBernoulliMixture k l (hZ M hM)}

theorem posteriorBernoulliMixtureFamilySet_nonempty
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty) :
    (posteriorBernoulliMixtureFamilySet C k l hZ).Nonempty := by
  rcases hC with ⟨M, hM⟩
  exact ⟨M.posteriorBernoulliMixture k l (hZ M hM), M, hM, rfl⟩

theorem posteriorBernoulliMixture_mem_posteriorFamilySet
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    {M : BernoulliMixture} (hM : M ∈ C) :
    M.posteriorBernoulliMixture k l (hZ M hM) ∈
      posteriorBernoulliMixtureFamilySet C k l hZ :=
  ⟨M, hM, rfl⟩

/-- Every member of the posterior family has analytic Bernoulli prefix laws. -/
def posteriorBernoulliMixtureFamilyPrefixLaw
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0) :
    ∀ P : BernoulliMixture,
      P ∈ posteriorBernoulliMixtureFamilySet C k l hZ →
      ∀ n : ℕ, BernoulliMixturePrefixLaw P n := by
  intro P _hP n
  exact bernoulliMixturePrefixLaw_analytic P n

/-- The finite-window prefix-law selector for an updated posterior family. -/
abbrev posteriorBernoulliMixtureFamilyPrefixLawAt
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0) (n : ℕ) :
    ∀ P : BernoulliMixture,
      P ∈ posteriorBernoulliMixtureFamilySet C k l hZ →
      BernoulliMixturePrefixLaw P n :=
  bernoulliMixturePrefixLawAt (posteriorBernoulliMixtureFamilySet C k l hZ)
    (posteriorBernoulliMixtureFamilyPrefixLaw C k l hZ) n

/-- In the posterior family envelope, every admissible prior mixture's
next-success Bayes ratio lies between the lower and upper one-bit envelopes.

This is a semantic Walley-family statement: it says the updated family contains
the memberwise Bayes update, not that the endpoints are proof-theoretically
tight. -/
theorem posteriorBernoulliMixtureFamily_trueRatio_mem_prefixEnvelope
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    {M : BernoulliMixture} (hM : M ∈ C) :
    impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        oneBitTrueGamble ≤
      M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l ∧
    M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l ≤
      impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        oneBitTrueGamble := by
  let P := M.posteriorBernoulliMixture k l (hZ M hM)
  have hP :
      P ∈ posteriorBernoulliMixtureFamilySet C k l hZ :=
    posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM
  have hValue :
      ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
          P hP).toPrecisePrevision oneBitTrueGamble =
        M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l := by
    simpa [P, posteriorBernoulliMixtureFamilyPrefixLawAt,
      posteriorBernoulliMixtureFamilyPrefixLaw, bernoulliMixturePrefixLawAt] using
      (posteriorBernoulliMixturePrefixPrevision_oneBitTrue_eq_countEvidenceMass_ratio
        M k l (hZ M hM))
  constructor
  · exact
      (impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        hP oneBitTrueGamble).trans_eq hValue
  · calc
      M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l =
          ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
            P hP).toPrecisePrevision oneBitTrueGamble := hValue.symm
      _ ≤ impreciseDeFinettiPrefixUpperEnvelope
          (posteriorBernoulliMixtureFamilySet C k l hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
          oneBitTrueGamble :=
        impreciseDeFinettiPrefixPrevision_le_upperEnvelope
          (posteriorBernoulliMixtureFamilySet C k l hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
          hP oneBitTrueGamble

/-- The same posterior-family envelope fact for the next-failure Bayes ratio. -/
theorem posteriorBernoulliMixtureFamily_falseRatio_mem_prefixEnvelope
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    {M : BernoulliMixture} (hM : M ∈ C) :
    impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        oneBitFalseGamble ≤
      M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l ∧
    M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l ≤
      impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        oneBitFalseGamble := by
  let P := M.posteriorBernoulliMixture k l (hZ M hM)
  have hP :
      P ∈ posteriorBernoulliMixtureFamilySet C k l hZ :=
    posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM
  have hValue :
      ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
          P hP).toPrecisePrevision oneBitFalseGamble =
        M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l := by
    simpa [P, posteriorBernoulliMixtureFamilyPrefixLawAt,
      posteriorBernoulliMixtureFamilyPrefixLaw, bernoulliMixturePrefixLawAt] using
      (posteriorBernoulliMixturePrefixPrevision_oneBitFalse_eq_countEvidenceMass_ratio
        M k l (hZ M hM))
  constructor
  · exact
      (impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        hP oneBitFalseGamble).trans_eq hValue
  · calc
      M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l =
          ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
            P hP).toPrecisePrevision oneBitFalseGamble := hValue.symm
      _ ≤ impreciseDeFinettiPrefixUpperEnvelope
          (posteriorBernoulliMixtureFamilySet C k l hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
          oneBitFalseGamble :=
        impreciseDeFinettiPrefixPrevision_le_upperEnvelope
          (posteriorBernoulliMixtureFamilySet C k l hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
          hP oneBitFalseGamble

/-- The posterior-family lower envelope for the next-success event is the
greatest scalar lower bound of all memberwise Bayes count ratios.

This remains a semantic Walley-envelope statement.  It does not assert that a
proof system derives the endpoint; it says the endpoint is forced by the full
updated credal family. -/
theorem posteriorBernoulliMixtureFamily_trueRatio_lowerEnvelope_greatestLowerBound
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty) {a : ℝ}
    (ha : ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
      a ≤ M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l) :
    a ≤
      impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        oneBitTrueGamble := by
  unfold impreciseDeFinettiPrefixLowerEnvelope
  apply le_lowerEnvelope_of_forall_le
  · exact bernoulliMixturePrefixCredalSet_nonempty
      (posteriorBernoulliMixtureFamilySet C k l hZ) 1
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
      (posteriorBernoulliMixtureFamilySet_nonempty C k l hZ hC)
  · intro P hP
    rcases hP with ⟨N, hN, rfl⟩
    rcases hN with ⟨M, hM, rfl⟩
    have hValue :
        (BernoulliMixturePrefixLaw.toPrecisePrevision
          ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
            (M.posteriorBernoulliMixture k l (hZ M hM))
            (posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM)))
            oneBitTrueGamble =
          M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l := by
      simpa [posteriorBernoulliMixtureFamilyPrefixLawAt,
        posteriorBernoulliMixtureFamilyPrefixLaw, bernoulliMixturePrefixLawAt] using
        (posteriorBernoulliMixturePrefixPrevision_oneBitTrue_eq_countEvidenceMass_ratio
          M k l (hZ M hM))
    calc
      a ≤ M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l := ha M hM
      _ = (BernoulliMixturePrefixLaw.toPrecisePrevision
            ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
            (M.posteriorBernoulliMixture k l (hZ M hM))
            (posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM)))
            oneBitTrueGamble := hValue.symm

/-- The posterior-family upper envelope for the next-success event is the least
scalar upper bound of all memberwise Bayes count ratios. -/
theorem posteriorBernoulliMixtureFamily_trueRatio_upperEnvelope_leastUpperBound
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty) {a : ℝ}
    (ha : ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
      M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l ≤ a) :
    impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        oneBitTrueGamble ≤
      a := by
  unfold impreciseDeFinettiPrefixUpperEnvelope
  apply upperEnvelope_le_of_forall_le
  · exact bernoulliMixturePrefixCredalSet_nonempty
      (posteriorBernoulliMixtureFamilySet C k l hZ) 1
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
      (posteriorBernoulliMixtureFamilySet_nonempty C k l hZ hC)
  · intro P hP
    rcases hP with ⟨N, hN, rfl⟩
    rcases hN with ⟨M, hM, rfl⟩
    have hValue :
        (BernoulliMixturePrefixLaw.toPrecisePrevision
          ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
            (M.posteriorBernoulliMixture k l (hZ M hM))
            (posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM)))
            oneBitTrueGamble =
          M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l := by
      simpa [posteriorBernoulliMixtureFamilyPrefixLawAt,
        posteriorBernoulliMixtureFamilyPrefixLaw, bernoulliMixturePrefixLawAt] using
        (posteriorBernoulliMixturePrefixPrevision_oneBitTrue_eq_countEvidenceMass_ratio
          M k l (hZ M hM))
    calc
      (BernoulliMixturePrefixLaw.toPrecisePrevision
        ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
          (M.posteriorBernoulliMixture k l (hZ M hM))
          (posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM)))
          oneBitTrueGamble =
        M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l := hValue
      _ ≤ a := ha M hM

/-- The posterior-family lower envelope for the next-failure event is the
greatest scalar lower bound of all memberwise Bayes count ratios. -/
theorem posteriorBernoulliMixtureFamily_falseRatio_lowerEnvelope_greatestLowerBound
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty) {a : ℝ}
    (ha : ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
      a ≤ M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l) :
    a ≤
      impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        oneBitFalseGamble := by
  unfold impreciseDeFinettiPrefixLowerEnvelope
  apply le_lowerEnvelope_of_forall_le
  · exact bernoulliMixturePrefixCredalSet_nonempty
      (posteriorBernoulliMixtureFamilySet C k l hZ) 1
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
      (posteriorBernoulliMixtureFamilySet_nonempty C k l hZ hC)
  · intro P hP
    rcases hP with ⟨N, hN, rfl⟩
    rcases hN with ⟨M, hM, rfl⟩
    have hValue :
        (BernoulliMixturePrefixLaw.toPrecisePrevision
          ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
            (M.posteriorBernoulliMixture k l (hZ M hM))
            (posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM)))
            oneBitFalseGamble =
          M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l := by
      simpa [posteriorBernoulliMixtureFamilyPrefixLawAt,
        posteriorBernoulliMixtureFamilyPrefixLaw, bernoulliMixturePrefixLawAt] using
        (posteriorBernoulliMixturePrefixPrevision_oneBitFalse_eq_countEvidenceMass_ratio
          M k l (hZ M hM))
    calc
      a ≤ M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l := ha M hM
      _ = (BernoulliMixturePrefixLaw.toPrecisePrevision
            ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
            (M.posteriorBernoulliMixture k l (hZ M hM))
            (posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM)))
            oneBitFalseGamble := hValue.symm

/-- The posterior-family upper envelope for the next-failure event is the
least scalar upper bound of all memberwise Bayes count ratios. -/
theorem posteriorBernoulliMixtureFamily_falseRatio_upperEnvelope_leastUpperBound
    (C : Set BernoulliMixture) (k l : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty) {a : ℝ}
    (ha : ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
      M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l ≤ a) :
    impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) 1
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
        oneBitFalseGamble ≤
      a := by
  unfold impreciseDeFinettiPrefixUpperEnvelope
  apply upperEnvelope_le_of_forall_le
  · exact bernoulliMixturePrefixCredalSet_nonempty
      (posteriorBernoulliMixtureFamilySet C k l hZ) 1
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
      (posteriorBernoulliMixtureFamilySet_nonempty C k l hZ hC)
  · intro P hP
    rcases hP with ⟨N, hN, rfl⟩
    rcases hN with ⟨M, hM, rfl⟩
    have hValue :
        (BernoulliMixturePrefixLaw.toPrecisePrevision
          ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
            (M.posteriorBernoulliMixture k l (hZ M hM))
            (posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM)))
            oneBitFalseGamble =
          M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l := by
      simpa [posteriorBernoulliMixtureFamilyPrefixLawAt,
        posteriorBernoulliMixtureFamilyPrefixLaw, bernoulliMixturePrefixLawAt] using
        (posteriorBernoulliMixturePrefixPrevision_oneBitFalse_eq_countEvidenceMass_ratio
          M k l (hZ M hM))
    calc
      (BernoulliMixturePrefixLaw.toPrecisePrevision
        ((posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ 1)
          (M.posteriorBernoulliMixture k l (hZ M hM))
          (posteriorBernoulliMixture_mem_posteriorFamilySet C k l hZ hM)))
          oneBitFalseGamble =
        M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l := hValue
      _ ≤ a := ha M hM

theorem posteriorBernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) (n : ℕ) :
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).hasCompatibleCompletion := by
  exact bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
    (posteriorBernoulliMixtureSet M k l hZ) n
    (posteriorBernoulliMixturePrefixLawAt M k l hZ n)
    (posteriorBernoulliMixtureSet_nonempty M k l hZ)

theorem posteriorBernoulliMixturePrefixProjectiveSpec_determines
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).determinesGlobalGamble X := by
  exact impreciseDeFinetti_prefixAgreement_projectiveDetermines
    (posteriorBernoulliMixtureSet M k l hZ)
    (posteriorBernoulliMixtureSetPrefixLaw M k l hZ) n X
    (by
      intro P hP Q hQ
      have hPEq : P = M.posteriorBernoulliMixture k l hZ := by
        simpa [posteriorBernoulliMixtureSet] using hP
      have hQEq : Q = M.posteriorBernoulliMixture k l hZ := by
        simpa [posteriorBernoulliMixtureSet] using hQ
      subst P
      subst Q
      rfl)

theorem posteriorBernoulliMixturePrefixEnvelopeWidth_eq_zero
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    impreciseDeFinettiPrefixEnvelopeWidth
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X = 0 := by
  exact impreciseDeFinettiPrefixEnvelopeWidth_eq_zero_of_mixtureAgreement
    (posteriorBernoulliMixtureSet M k l hZ) n
    (posteriorBernoulliMixturePrefixLawAt M k l hZ n)
    (posteriorBernoulliMixtureSet_nonempty M k l hZ) X
    (by
      intro P hP Q hQ
      have hPEq : P = M.posteriorBernoulliMixture k l hZ := by
        simpa [posteriorBernoulliMixtureSet] using hP
      have hQEq : Q = M.posteriorBernoulliMixture k l hZ := by
        simpa [posteriorBernoulliMixtureSet] using hQ
      subst P
      subst Q
      rfl)

theorem posteriorBernoulliMixturePrefixEnvelopeWidthComplement_eq_one
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    impreciseDeFinettiPrefixEnvelopeWidthComplement
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X = 1 := by
  exact impreciseDeFinetti_prefixAgreement_confidence_eq_one
    (posteriorBernoulliMixtureSet M k l hZ)
    (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
    (posteriorBernoulliMixtureSet_nonempty M k l hZ) n X
    (by
      intro P hP Q hQ
      have hPEq : P = M.posteriorBernoulliMixture k l hZ := by
        simpa [posteriorBernoulliMixtureSet] using hP
      have hQEq : Q = M.posteriorBernoulliMixture k l hZ := by
        simpa [posteriorBernoulliMixtureSet] using hQ
      subst P
      subst Q
      rfl)

/-- Posterior/update transport into the existing de Finetti projective
finite-prefix surface.  This does not claim a new process carrier; it records
that the normalized posterior mixture is already a singleton projective prefix
system with compatible completions and determined finite-prefix intervals. -/
structure PosteriorBernoulliMixturePrefixProjectiveCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) : Prop where
  posterior_mem : M.posteriorBernoulliMixture k l hZ ∈
    posteriorBernoulliMixtureSet M k l hZ
  posterior_prefix_law : ∀ n : ℕ,
    BernoulliMixturePrefixLaw (M.posteriorBernoulliMixture k l hZ) n
  posterior_set_nonempty : (posteriorBernoulliMixtureSet M k l hZ).Nonempty
  prefixCompatibleCompletion : ∀ n : ℕ,
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).hasCompatibleCompletion
  prefixDetermines : ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).determinesGlobalGamble X
  prefixEnvelopeWidth_eq_zero : ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    impreciseDeFinettiPrefixEnvelopeWidth
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X = 0
  prefixWidthComplement_eq_one : ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    impreciseDeFinettiPrefixEnvelopeWidthComplement
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X = 1

theorem posteriorBernoulliMixturePrefixProjectiveCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixturePrefixProjectiveCrown M k l hZ where
  posterior_mem := posteriorBernoulliMixture_mem_posteriorSet M k l hZ
  posterior_prefix_law := by
    intro n
    exact bernoulliMixturePrefixLaw_analytic
      (M.posteriorBernoulliMixture k l hZ) n
  posterior_set_nonempty := posteriorBernoulliMixtureSet_nonempty M k l hZ
  prefixCompatibleCompletion := by
    intro n
    exact posteriorBernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
      M k l hZ n
  prefixDetermines := by
    intro n X
    exact posteriorBernoulliMixturePrefixProjectiveSpec_determines M k l hZ n X
  prefixEnvelopeWidth_eq_zero := by
    intro n X
    exact posteriorBernoulliMixturePrefixEnvelopeWidth_eq_zero M k l hZ n X
  prefixWidthComplement_eq_one := by
    intro n X
    exact posteriorBernoulliMixturePrefixEnvelopeWidthComplement_eq_one M k l hZ n X

/-! ### Posterior mixtures as process-law systems -/

/-- The process-level local lower-prevision specification generated by the
singleton posterior Bernoulli mixture after `k` successes and `l` failures. -/
noncomputable abbrev posteriorBernoulliMixturePrefixProcessLowerSpec
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    ProjectiveLocalLowerPrevisionSpec ℕ (ℕ → Bool) :=
  bernoulliMixturePrefixProcessLowerSpec
    (posteriorBernoulliMixtureSet M k l hZ)
    (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
    (posteriorBernoulliMixtureSet_nonempty M k l hZ)

@[simp] theorem posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_apply
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n X =
      impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureSet M k l hZ) n
        (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X := by
  exact bernoulliMixturePrefixProcessLowerSpec_localLower_apply
    (posteriorBernoulliMixtureSet M k l hZ)
    (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
    (posteriorBernoulliMixtureSet_nonempty M k l hZ) n X

/-- The posterior singleton prefix credal set is exactly the analytic prefix
law at each finite window. -/
theorem posteriorBernoulliMixturePrefixCredalSet_eq_singleton
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) (n : ℕ) :
    bernoulliMixturePrefixCredalSet
        (posteriorBernoulliMixtureSet M k l hZ) n
        (posteriorBernoulliMixturePrefixLawAt M k l hZ n) =
      ({(bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision} :
        CredalPrevisionSet (Fin n → Bool)) := by
  ext P
  constructor
  · rintro ⟨N, hN, rfl⟩
    have hEq : N = M.posteriorBernoulliMixture k l hZ := by
      simpa [posteriorBernoulliMixtureSet] using hN
    subst hEq
    simp
  · intro hP
    refine ⟨M.posteriorBernoulliMixture k l hZ,
      posteriorBernoulliMixture_mem_posteriorSet M k l hZ, ?_⟩
    simpa [posteriorBernoulliMixtureSetPrefixLaw] using hP

/-- The posterior prefix-process local lower prevision is already exact at each
finite window. -/
theorem posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_eq_analytic
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  rw [posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_apply]
  unfold impreciseDeFinettiPrefixLowerEnvelope
  rw [posteriorBernoulliMixturePrefixCredalSet_eq_singleton]
  exact lowerEnvelope_singleton _ _

/-- Canonical finite joint-window system for the posterior singleton Boolean
prefix process.  This specializes the arbitrary finite-window system `J` in the
generic realization theorem to the largest-prefix construction. -/
noncomputable abbrev posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ) :=
  bernoulliMixturePrefixProcessFiniteJointWindowSystem
    (posteriorBernoulliMixtureSet M k l hZ)
    (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
    (posteriorBernoulliMixtureSet_nonempty M k l hZ)

/-- Exact finite-prefix marginal consistency needed by the canonical
largest-prefix joint-window system.

For every finite family of requested prefix lengths `u`, the analytic posterior
law on the largest requested prefix must marginalize to the analytic law on
each member prefix.  This is the remaining finite product-sum theorem, stated
without hiding it behind an arbitrary local-coherence witness. -/
noncomputable def posteriorBernoulliMixturePrefixProcessMarginalConsistent
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) : Prop :=
  ∀ (u : Finset ℕ) {i : ℕ} (hi : i ∈ u)
    (X : Gamble (Fin i → Bool)),
    (bernoulliMixturePrefixLaw_analytic
      (M.posteriorBernoulliMixture k l hZ)
      (prefixWindowJointLength u)).toPrecisePrevision
      (fun xs => X (fun t =>
        xs (Fin.castLE (prefixWindow_le_jointLength u hi) t))) =
    (bernoulliMixturePrefixLaw_analytic
      (M.posteriorBernoulliMixture k l hZ) i).toPrecisePrevision X

/-- The canonical largest-prefix posterior finite-window system is exactly
marginal-consistent: truncating the analytic law on the largest requested prefix
recovers the analytic law on each requested member prefix. -/
theorem posteriorBernoulliMixturePrefixProcessMarginalConsistent_analytic
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    posteriorBernoulliMixturePrefixProcessMarginalConsistent M k l hZ := by
  intro u i hi X
  exact bernoulliMixturePrefixPrevision_takePrefix_eq
    (M := M.posteriorBernoulliMixture k l hZ)
    (hmn := prefixWindow_le_jointLength u hi) X

/-- Any precise completion dominating the lower-prevision view of a precise
prevision agrees with it exactly. -/
theorem precisePrevision_eq_of_mem_dominatingPreciseCompletions_toLowerPrevision
    {Ω : Type*} {P Q : PrecisePrevision Ω}
    (hQ : Q ∈ dominatingPreciseCompletions P.toLowerPrevision) :
    Q = P := by
  ext X
  have hle : P X ≤ Q X := by
    simpa [PrecisePrevision.toLowerPrevision_apply] using hQ X
  have hneg : P (-X) ≤ Q (-X) := by
    simpa [PrecisePrevision.toLowerPrevision_apply] using hQ (-X)
  have hge : Q X ≤ P X := by
    have hneg' : -P X ≤ -Q X := by
      simpa [PrecisePrevision.map_neg] using hneg
    linarith
  exact le_antisymm hge hle

/-- The analytic posterior prefix laws form a compatible cylinder-domain
completion of the posterior process specification.

Positive example: each finite prefix window is evaluated by the exact analytic
posterior prefix prevision. Negative example: this is only a
`CylinderPrevision`, not a raw `PrecisePrevision (ℕ → Bool)` on all gambles. -/
noncomputable def posteriorBernoulliMixturePrefixProcessCylinderPrevision
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.CylinderPrevision where
  toFun n X :=
    (bernoulliMixturePrefixLaw_analytic
      (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  lower_bound := by
    intro n X c hc
    exact
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision.lower_bound
          X c hc
  pos_homog := by
    intro n r X hr
    exact
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision.pos_homog
          r X hr
  add := by
    intro n X Y
    exact
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision.add X Y
  restrict_compat := by
    intro i j hij X
    exact bernoulliMixturePrefixPrevision_takePrefix_eq
      (M := M.posteriorBernoulliMixture k l hZ) (hmn := hij) X

@[simp] theorem posteriorBernoulliMixturePrefixProcessCylinderPrevision_localPrevision
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) (n : ℕ) :
    (posteriorBernoulliMixturePrefixProcessCylinderPrevision M k l hZ).localPrevision n =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision := by
  ext X
  rfl

/-- The analytic posterior prefix cylinder completion belongs to the generated
projective cylinder credal set. -/
theorem posteriorBernoulliMixturePrefixProcessCylinderPrevision_mem_projectiveCylinderCredalSet
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    posteriorBernoulliMixturePrefixProcessCylinderPrevision M k l hZ ∈
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec.projectiveCylinderCredalSet := by
  intro n X
  exact le_of_eq
    (posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_eq_analytic M k l hZ n X)

/-- The posterior process lower-prevision specification already has a compatible
cylinder-domain completion, without any raw all-gambles process witness. -/
theorem posteriorBernoulliMixturePrefixProcess_hasCompatibleCylinderCompletion
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec.hasCompatibleCylinderCompletion :=
  ⟨posteriorBernoulliMixturePrefixProcessCylinderPrevision M k l hZ,
    posteriorBernoulliMixturePrefixProcessCylinderPrevision_mem_projectiveCylinderCredalSet
      M k l hZ⟩

/-- At each finite prefix window, the local credal set generated by the
posterior process lower spec is already the singleton analytic posterior prefix
prevision. -/
theorem posteriorBernoulliMixturePrefixProcessLocalCredal_eq_singleton
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) (n : ℕ) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec.localCredal n =
      ({(bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision} :
        CredalPrevisionSet (Fin n → Bool)) := by
  ext R
  constructor
  · intro hR
    have hR' :
        R ∈ dominatingPreciseCompletions
          ((bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision.toLowerPrevision) := by
      intro X
      have hRX := hR X
      rw [posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_eq_analytic
        M k l hZ n X] at hRX
      simpa [PrecisePrevision.toLowerPrevision_apply] using hRX
    have hEq :
        R =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision :=
      precisePrevision_eq_of_mem_dominatingPreciseCompletions_toLowerPrevision hR'
    exact hEq ▸ rfl
  · intro hR
    rcases Set.mem_singleton_iff.mp hR with rfl
    intro X
    rw [posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_eq_analytic
      M k l hZ n X]

/-- Every admissible local precise completion at a finite prefix window lifts to
the analytic compatible cylinder completion, so the posterior process is exact
at the cylinder-domain level. -/
theorem posteriorBernoulliMixturePrefixProcess_localCylinderCredalExactAt
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) (n : ℕ) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec.localCylinderCredalExactAt n := by
  intro R hR
  refine ⟨posteriorBernoulliMixturePrefixProcessCylinderPrevision M k l hZ, ?_, ?_⟩
  · exact
      posteriorBernoulliMixturePrefixProcessCylinderPrevision_mem_projectiveCylinderCredalSet
        M k l hZ
  · have hEq :
        R =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision := by
      have hR' :
          R ∈ dominatingPreciseCompletions
            ((bernoulliMixturePrefixLaw_analytic
              (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision.toLowerPrevision) := by
        intro X
        have hRX := hR X
        rw [posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_eq_analytic
          M k l hZ n X] at hRX
        simpa [PrecisePrevision.toLowerPrevision_apply] using hRX
      exact
        precisePrevision_eq_of_mem_dominatingPreciseCompletions_toLowerPrevision
          hR'
    subst R
    exact
      posteriorBernoulliMixturePrefixProcessCylinderPrevision_localPrevision
        M k l hZ n

/-- Cylinder-domain posterior interval width already collapses to zero at every
finite prefix window.  This is the honest process-level replacement for the
raw witness route when only cylinder observables are needed. -/
theorem posteriorBernoulliMixturePrefixProcess_cylinderEnvelopeWidth_eq_zero
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).cylinderEnvelopeWidth
      n X = 0 := by
  let S := (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec
  haveI : Fintype (S.cylinders.Local n) := by
    dsimp [S, posteriorBernoulliMixturePrefixProcessLowerSpec,
      bernoulliMixturePrefixProcessLowerSpec, bernoulliMixturePrefixProcessCylinderSystem]
    infer_instance
  haveI : Nonempty (S.cylinders.Local n) := by
    dsimp [S, posteriorBernoulliMixturePrefixProcessLowerSpec,
      bernoulliMixturePrefixProcessLowerSpec, bernoulliMixturePrefixProcessCylinderSystem]
    infer_instance
  have hDet : credalSetDetermines (S.localCredal n) X := by
    rw [posteriorBernoulliMixturePrefixProcessLocalCredal_eq_singleton M k l hZ n]
    exact credalSetDetermines_singleton
      ((bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision) X
  exact
    ProjectiveLocalCredalSpec.finiteCylinderEnvelopeWidth_eq_zero_of_localCredal_determines_of_exact
      S
      (posteriorBernoulliMixturePrefixProcess_hasCompatibleCylinderCompletion
        M k l hZ)
      n X
      (posteriorBernoulliMixturePrefixProcess_localCylinderCredalExactAt
        M k l hZ n)
      hDet

/-- Cylinder-domain posterior width-complement is already maximal at every
finite prefix window. -/
theorem posteriorBernoulliMixturePrefixProcess_cylinderEnvelopeWidthComplement_eq_one
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).cylinderEnvelopeWidthComplement
      n X = 1 := by
  let S := (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec
  haveI : Fintype (S.cylinders.Local n) := by
    dsimp [S, posteriorBernoulliMixturePrefixProcessLowerSpec,
      bernoulliMixturePrefixProcessLowerSpec, bernoulliMixturePrefixProcessCylinderSystem]
    infer_instance
  haveI : Nonempty (S.cylinders.Local n) := by
    dsimp [S, posteriorBernoulliMixturePrefixProcessLowerSpec,
      bernoulliMixturePrefixProcessLowerSpec, bernoulliMixturePrefixProcessCylinderSystem]
    infer_instance
  have hDet : credalSetDetermines (S.localCredal n) X := by
    rw [posteriorBernoulliMixturePrefixProcessLocalCredal_eq_singleton M k l hZ n]
    exact credalSetDetermines_singleton
      ((bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision) X
  exact
    ProjectiveLocalCredalSpec.finiteCylinderEnvelopeWidthComplement_eq_one_of_localCredal_determines_of_exact
      S
      (posteriorBernoulliMixturePrefixProcess_hasCompatibleCylinderCompletion
        M k l hZ)
      n X
      (posteriorBernoulliMixturePrefixProcess_localCylinderCredalExactAt
        M k l hZ n)
      hDet

/-! ### Raw-witness obstruction on infinite first-true cylinders -/

/-- The all-`true` length-`n` Boolean prefix. -/
def allTruePrefix (n : ℕ) : Fin n → Bool := fun _ => true

/-- The all-`false` length-`n` Boolean prefix. -/
def allFalsePrefix (n : ℕ) : Fin n → Bool := fun _ => false

/-- The constant infinite Boolean path that is identically `true`. -/
def allTruePath : ℕ → Bool := fun _ => true

/-- The constant infinite Boolean path that is identically `false`. -/
def allFalsePath : ℕ → Bool := fun _ => false

/-- The `(n+1)`-bit prefix whose first `n` bits are `false` and whose final
bit is `true`.  This is the finite prefix encoding “the first `true` occurs at
time `n`”. -/
def firstTruePrefix (n : ℕ) : Fin (n + 1) → Bool :=
  Fin.snoc (allFalsePrefix n) true

/-- Atomic prefix gamble selecting the first-`true` prefix at horizon `n+1`. -/
def firstTruePrefixGamble (n : ℕ) : Gamble (Fin (n + 1) → Bool) :=
  PrecisePrevision.FiniteWeights.atomGamble (firstTruePrefix n)

/-- Global cylinder gamble selecting infinite Boolean paths whose first `true`
appears exactly at coordinate `n`. -/
def firstTrueCylinderGamble (n : ℕ) : Gamble (ℕ → Bool) :=
  fun ω => if ω n = true ∧ ∀ m < n, ω m = false then 1 else 0

theorem firstTrueCylinderGamble_eq_cylinderGamble
    (n : ℕ) :
    firstTrueCylinderGamble n =
      bernoulliMixturePrefixProcessCylinderSystem.cylinderGamble
        (n + 1) (firstTruePrefixGamble n) := by
  funext ω
  unfold firstTrueCylinderGamble
  unfold ProjectiveCylinderSystem.cylinderGamble
  unfold firstTruePrefixGamble
  unfold PrecisePrevision.FiniteWeights.atomGamble
  change
    (if ω n = true ∧ ∀ m < n, ω m = false then (1 : ℝ) else 0) =
      if (fun i : Fin (n + 1) => ω i) = firstTruePrefix n then 1 else 0
  by_cases h :
      ω n = true ∧ ∀ m < n, ω m = false
  · have hEq : (fun i : Fin (n + 1) => ω i) = firstTruePrefix n := by
      funext i
      cases i using Fin.lastCases with
      | last =>
          simpa [firstTruePrefix] using h.1
      | cast j =>
          have hfalse : ω j = false := h.2 j j.2
          simpa [firstTruePrefix, allFalsePrefix] using hfalse
    rw [if_pos h, if_pos hEq]
  · have hNe : (fun i : Fin (n + 1) => ω i) ≠ firstTruePrefix n := by
      intro hEq
      have htrue : ω n = true := by
        have hlast := congrArg (fun f : Fin (n + 1) → Bool => f (Fin.last n)) hEq
        simpa [firstTruePrefix] using hlast
      have hfalse : ∀ m < n, ω m = false := by
        intro m hm
        have hcast :=
          congrArg (fun f : Fin (n + 1) → Bool => f (Fin.castSucc ⟨m, hm⟩)) hEq
        have hprefix :
            firstTruePrefix n (Fin.castSucc ⟨m, hm⟩) = false := by
          unfold firstTruePrefix
          rw [Fin.snoc_castSucc]
          simp [allFalsePrefix]
        exact hcast.trans hprefix
      exact h ⟨htrue, hfalse⟩
    rw [if_neg h, if_neg hNe]

@[simp] theorem firstTrueCylinderGamble_apply
    (n : ℕ) (ω : ℕ → Bool) :
    firstTrueCylinderGamble n ω =
      (if ω n = true ∧ ∀ m < n, ω m = false then 1 else 0) :=
  rfl

theorem firstTrueCylinderGamble_find
    {ω : ℕ → Bool}
    (hω : ∃ n, ω n = true) :
    firstTrueCylinderGamble (Nat.find hω) ω = 1 := by
  have htrue : ω (Nat.find hω) = true := Nat.find_spec hω
  have hbefore : ∀ m < Nat.find hω, ω m = false := by
    intro m hm
    cases hval : ω m with
    | false =>
        rfl
    | true =>
        exfalso
        exact (not_lt_of_ge (Nat.find_min' hω hval) hm).elim
  have hcond :
      ω (Nat.find hω) = true ∧ ∀ m < Nat.find hω, ω m = false :=
    ⟨htrue, hbefore⟩
  unfold firstTrueCylinderGamble
  rw [if_pos hcond]

theorem firstTrueCylinderGamble_eq_zero_of_ne_find
    {ω : ℕ → Bool}
    (hω : ∃ n, ω n = true) {n : ℕ}
    (hne : n ≠ Nat.find hω) :
    firstTrueCylinderGamble n ω = 0 := by
  by_cases hfirst : ω n = true ∧ ∀ m < n, ω m = false
  · have hfind_eq : Nat.find hω = n := by
      apply le_antisymm
      · exact Nat.find_min' hω hfirst.1
      · by_contra hlt
        have hlt' : Nat.find hω < n := lt_of_not_ge hlt
        have hfalse : ω (Nat.find hω) = false := hfirst.2 (Nat.find hω) hlt'
        rw [Nat.find_spec hω] at hfalse
        cases hfalse
    exact (hne hfind_eq.symm).elim
  · simp [firstTrueCylinderGamble, hfirst]

/-- The exploding gamble that assigns the reciprocal weight of the first `true`
index and vanishes on the all-`false` path. -/
noncomputable def firstTrueExplodingGamble
    (w : ℕ → ℝ) : Gamble (ℕ → Bool) := by
  classical
  exact fun ω =>
    if hω : ∃ n, ω n = true then (w (Nat.find hω))⁻¹ else 0

/-- Finite partial sum of the weighted first-`true` cylinder indicators. -/
noncomputable def firstTruePartialGamble
    (N : ℕ) (w : ℕ → ℝ) : Gamble (ℕ → Bool) :=
  ∑ n ∈ Finset.range N, (w n)⁻¹ • firstTrueCylinderGamble n

theorem firstTruePartialGamble_le_exploding
    (N : ℕ) (w : ℕ → ℝ)
    (hPos : ∀ n : ℕ, 0 < w n) :
    ∀ ω : ℕ → Bool,
      firstTruePartialGamble N w ω ≤ firstTrueExplodingGamble w ω := by
  classical
  intro ω
  by_cases hω : ∃ n, ω n = true
  · by_cases hmem : Nat.find hω ∈ Finset.range N
    · have hsum :
        firstTruePartialGamble N w ω = (w (Nat.find hω))⁻¹ := by
        unfold firstTruePartialGamble
        rw [PrecisePrevision.sum_gamble_apply]
        rw [Finset.sum_eq_single (Nat.find hω)]
        · have hfirst :
              firstTrueCylinderGamble (Nat.find hω) ω = 1 :=
            firstTrueCylinderGamble_find hω
          show (w (Nat.find hω))⁻¹ * firstTrueCylinderGamble (Nat.find hω) ω
            = (w (Nat.find hω))⁻¹
          rw [hfirst, mul_one]
        · intro n hn hne
          have hz :
              firstTrueCylinderGamble n ω = 0 :=
            firstTrueCylinderGamble_eq_zero_of_ne_find hω hne
          show (w n)⁻¹ * firstTrueCylinderGamble n ω = 0
          rw [hz, mul_zero]
        · intro hnot
          exact (hnot hmem).elim
      simp [firstTrueExplodingGamble, hω, hsum]
    · have hsum :
        firstTruePartialGamble N w ω = 0 := by
          unfold firstTruePartialGamble
          rw [PrecisePrevision.sum_gamble_apply]
          apply Finset.sum_eq_zero
          intro n hn
          have hne : n ≠ Nat.find hω := by
            intro hEq
            apply hmem
            simpa [hEq] using hn
          have hz :
              firstTrueCylinderGamble n ω = 0 :=
            firstTrueCylinderGamble_eq_zero_of_ne_find hω hne
          show (w n)⁻¹ * firstTrueCylinderGamble n ω = 0
          rw [hz, mul_zero]
      have hnonneg : 0 ≤ (w (Nat.find hω))⁻¹ := by
        exact inv_nonneg.mpr (le_of_lt (hPos (Nat.find hω)))
      rw [hsum]
      simp [firstTrueExplodingGamble, hω, hnonneg]
  · have hsum :
      firstTruePartialGamble N w ω = 0 := by
      unfold firstTruePartialGamble
      rw [PrecisePrevision.sum_gamble_apply]
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hfirst : ω n = true ∧ ∀ m < n, ω m = false
      · exact (hω ⟨n, hfirst.1⟩).elim
      · show (w n)⁻¹ * firstTrueCylinderGamble n ω = 0
        simp only [firstTrueCylinderGamble, if_neg hfirst, mul_zero]
    rw [hsum]
    simp [firstTrueExplodingGamble, hω]

theorem countTrue_allFalsePrefix (n : ℕ) :
    Mettapedia.Logic.Exchangeability.countTrue (allFalsePrefix n) = 0 := by
  simp [allFalsePrefix, Mettapedia.Logic.Exchangeability.countTrue]

theorem countFalse_allFalsePrefix (n : ℕ) :
    Mettapedia.Logic.Exchangeability.countFalse (allFalsePrefix n) = n := by
  simp [allFalsePrefix, Mettapedia.Logic.Exchangeability.countFalse]

theorem countTrue_allTruePrefix (n : ℕ) :
    Mettapedia.Logic.Exchangeability.countTrue (allTruePrefix n) = n := by
  simp [allTruePrefix, Mettapedia.Logic.Exchangeability.countTrue]

theorem countFalse_allTruePrefix (n : ℕ) :
    Mettapedia.Logic.Exchangeability.countFalse (allTruePrefix n) = 0 := by
  simp [allTruePrefix, Mettapedia.Logic.Exchangeability.countFalse]

theorem eq_allFalsePrefix_of_countTrue_eq_zero
    {n : ℕ} {xs : Fin n → Bool}
    (hTrue : Mettapedia.Logic.Exchangeability.countTrue xs = 0) :
    xs = allFalsePrefix n := by
  funext i
  by_cases hi : xs i = true
  · have hCardPos :
        0 < Mettapedia.Logic.Exchangeability.countTrue xs := by
      unfold Mettapedia.Logic.Exchangeability.countTrue
      exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    omega
  · cases hxi : xs i <;> simp [allFalsePrefix, hxi] at hi ⊢

theorem eq_allTruePrefix_of_countFalse_eq_zero
    {n : ℕ} {xs : Fin n → Bool}
    (hFalse : Mettapedia.Logic.Exchangeability.countFalse xs = 0) :
    xs = allTruePrefix n := by
  funext i
  by_cases hi : xs i = false
  · have hCardPos :
        0 < Mettapedia.Logic.Exchangeability.countFalse xs := by
      unfold Mettapedia.Logic.Exchangeability.countFalse
      exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    omega
  · cases hxi : xs i <;> simp [allTruePrefix, hxi] at hi ⊢

theorem allTruePrefix_ne_allFalsePrefix {n : ℕ} (hn : 0 < n) :
    allTruePrefix n ≠ allFalsePrefix n := by
  intro hEq
  have h0 := congrArg (fun f : Fin n → Bool => f ⟨0, hn⟩) hEq
  simp [allTruePrefix, allFalsePrefix] at h0

theorem firstTruePrefix_eq_append (n : ℕ) :
    firstTruePrefix n = Fin.append (allFalsePrefix n) oneBitTruePrefix := by
  have hone : oneBitTruePrefix = Fin.cons true Fin.elim0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [oneBitTruePrefix]
  rw [hone]
  simpa [firstTruePrefix] using
    (Fin.snoc_eq_append (allFalsePrefix n) true)

theorem countTrue_firstTruePrefix (n : ℕ) :
    Mettapedia.Logic.Exchangeability.countTrue (firstTruePrefix n) = 1 := by
  rw [firstTruePrefix_eq_append]
  rw [countTrue_append_fin, countTrue_allFalsePrefix]
  simp [oneBitTruePrefix, Mettapedia.Logic.Exchangeability.countTrue]

theorem countFalse_firstTruePrefix (n : ℕ) :
    Mettapedia.Logic.Exchangeability.countFalse (firstTruePrefix n) = n := by
  rw [firstTruePrefix_eq_append]
  rw [countFalse_append_fin, countFalse_allFalsePrefix]
  simp [oneBitTruePrefix, Mettapedia.Logic.Exchangeability.countFalse]

theorem precisePrevision_firstTruePartialGamble
    (P : PrecisePrevision (ℕ → Bool))
    (w : ℕ → ℝ)
    (hWeights : ∀ n : ℕ, P (firstTrueCylinderGamble n) = w n)
    (hPos : ∀ n : ℕ, 0 < w n)
    (N : ℕ) :
    P (firstTruePartialGamble N w) = (N : ℝ) := by
  unfold firstTruePartialGamble
  rw [P.map_sum]
  calc
    ∑ n ∈ Finset.range N, P ((w n)⁻¹ • firstTrueCylinderGamble n)
        = ∑ n ∈ Finset.range N, ((w n)⁻¹) * w n := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [P.map_smul, hWeights n]
    _ = ∑ _n ∈ Finset.range N, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n _hn
          field_simp [ne_of_gt (hPos n)]
    _ = (N : ℝ) := by
          simp

/-- A raw precise prevision on the full infinite-path gamble space cannot assign
strictly positive values to every “first `true` at time `n`” cylinder event.
Otherwise the corresponding exploding gamble would dominate partial sums of
arbitrarily large expectation. -/
theorem no_rawPrecisePrevision_extends_positiveFirstTrueWeights
    (P : PrecisePrevision (ℕ → Bool))
    (hPos : ∀ n : ℕ, 0 < P (firstTrueCylinderGamble n)) :
    False := by
  let w : ℕ → ℝ := fun n => P (firstTrueCylinderGamble n)
  let X : Gamble (ℕ → Bool) := firstTrueExplodingGamble w
  have hLower : ∀ N : ℕ, (N : ℝ) ≤ P X := by
    intro N
    have hpartial :
        P (firstTruePartialGamble N w) = (N : ℝ) :=
      precisePrevision_firstTruePartialGamble P w (fun n => rfl) hPos N
    have hmono :
        P (firstTruePartialGamble N w) ≤ P X :=
      P.mono (firstTruePartialGamble_le_exploding N w hPos)
    rwa [hpartial] at hmono
  obtain ⟨N, hN⟩ := exists_nat_gt (P X)
  exact not_le_of_gt hN (hLower N)

theorem posteriorBernoulliMixture_firstTruePrefixPrevision_eq_countEvidenceMass_ratio
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) (n + 1)).toPrecisePrevision
        (firstTruePrefixGamble n) =
      M.countEvidenceMass (k + 1) (l + n) / M.countEvidenceMass k l := by
  rw [firstTruePrefixGamble, BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  rw [BernoulliMixture.posteriorBernoulliMixture_prob_eq_countEvidenceMass_ratio]
  rw [countTrue_firstTruePrefix, countFalse_firstTruePrefix]

/-- A single global carrier member with the analytic posterior prefix marginals
already suffices for the canonical largest-prefix finite-window bridge. -/
def posteriorBernoulliMixturePrefixProcessCarrierWitness
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool)) : Prop :=
  ∃ P : PrecisePrevision (ℕ → Bool), P ∈ carrier ∧
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) X =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X

/-- The raw global posterior-process witness at the right mathematical layer:
a single all-gambles precise prevision on `(ℕ → Bool)` with exactly the
analytic posterior finite prefix marginals.

This is the actual object sought by the original Crown 2 carrier question. The
carrier-based witness above is equivalent, but bundles extra membership data
used by the compact/FIP route. -/
def posteriorBernoulliMixturePrefixProcessWitness
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) : Prop :=
  ∃ P : PrecisePrevision (ℕ → Bool),
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) X =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X

theorem posteriorBernoulliMixturePrefixProcessWitness_iff_existsCarrierWitness
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    posteriorBernoulliMixturePrefixProcessWitness M k l hZ ↔
      ∃ carrier : CredalPrevisionSet (ℕ → Bool),
        posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier := by
  constructor
  · rintro ⟨P, hPmarg⟩
    refine ⟨({P} : CredalPrevisionSet (ℕ → Bool)), ?_⟩
    exact ⟨P, by simp, hPmarg⟩
  · rintro ⟨carrier, hWitness⟩
    rcases hWitness with ⟨P, _hPcarrier, hPmarg⟩
    exact ⟨P, hPmarg⟩

/-- The single-global raw witness boundary is impossible whenever every
posterior first-`true` cylinder already has strictly positive analytic mass.
This is the formal obstruction showing that the remaining raw witness is not
merely unproved: under these explicit positivity hypotheses, it cannot exist. -/
theorem not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_positiveFirstTrueMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hPos : ∀ n : ℕ,
      0 <
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) (n + 1)).toPrecisePrevision
          (firstTruePrefixGamble n)) :
    ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness
        M k l hZ carrier := by
  intro hWitness
  rcases hWitness with ⟨P, _hPcarrier, hPmarg⟩
  apply no_rawPrecisePrevision_extends_positiveFirstTrueWeights P
  intro n
  have hEq :
      P (firstTrueCylinderGamble n) =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) (n + 1)).toPrecisePrevision
          (firstTruePrefixGamble n) := by
    calc
      P (firstTrueCylinderGamble n)
          = P
              (bernoulliMixturePrefixProcessCylinderSystem.cylinderGamble
                (n + 1) (firstTruePrefixGamble n)) := by
                  rw [firstTrueCylinderGamble_eq_cylinderGamble]
      _ =
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
              (n + 1) P) (firstTruePrefixGamble n) := by
                rfl
      _ =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) (n + 1)).toPrecisePrevision
            (firstTruePrefixGamble n) := hPmarg (n + 1) (firstTruePrefixGamble n)
  rw [hEq]
  exact hPos n

theorem not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_positiveFirstTrueEvidenceMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hPos : ∀ n : ℕ, 0 < M.countEvidenceMass (k + 1) (l + n)) :
    ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness
        M k l hZ carrier := by
  have hDen : 0 < M.countEvidenceMass k l := by
    exact lt_of_le_of_ne (BernoulliMixture.countEvidenceMass_nonneg M k l) hZ.symm
  apply
    not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_positiveFirstTrueMass
      M k l hZ carrier
  intro n
  rw [posteriorBernoulliMixture_firstTruePrefixPrevision_eq_countEvidenceMass_ratio
    M k l n hZ]
  exact div_pos (hPos n) hDen

theorem not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness
        M k l hZ carrier := by
  apply
    not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_positiveFirstTrueEvidenceMass
      M k l hZ carrier
  intro n
  exact BernoulliMixture.countEvidenceMass_pos_of_interiorMass
    M (k + 1) (l + n) hInterior

theorem not_posteriorBernoulliMixturePrefixProcessWitness_of_positiveFirstTrueMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hPos : ∀ n : ℕ,
      0 <
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) (n + 1)).toPrecisePrevision
          (firstTruePrefixGamble n)) :
    ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  intro hWitness
  rcases
      (posteriorBernoulliMixturePrefixProcessWitness_iff_existsCarrierWitness
        M k l hZ).mp hWitness with
    ⟨carrier, hCarrierWitness⟩
  exact
    (not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_positiveFirstTrueMass
      M k l hZ carrier hPos)
      hCarrierWitness

theorem not_posteriorBernoulliMixturePrefixProcessWitness_of_positiveFirstTrueEvidenceMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hPos : ∀ n : ℕ, 0 < M.countEvidenceMass (k + 1) (l + n)) :
    ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  intro hWitness
  rcases
      (posteriorBernoulliMixturePrefixProcessWitness_iff_existsCarrierWitness
        M k l hZ).mp hWitness with
    ⟨carrier, hCarrierWitness⟩
  exact
    (not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_positiveFirstTrueEvidenceMass
      M k l hZ carrier hPos)
      hCarrierWitness

theorem not_posteriorBernoulliMixturePrefixProcessWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  intro hWitness
  rcases
      (posteriorBernoulliMixturePrefixProcessWitness_iff_existsCarrierWitness
        M k l hZ).mp hWitness with
    ⟨carrier, hCarrierWitness⟩
  exact
    (not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_interiorMixingMass
      M k l hZ carrier hInterior)
      hCarrierWitness

theorem posteriorBernoulliMixturePrefixProcessWitness_exists_zeroFirstTrueEvidenceMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hWitness : posteriorBernoulliMixturePrefixProcessWitness M k l hZ) :
    ∃ n : ℕ, M.countEvidenceMass (k + 1) (l + n) = 0 := by
  by_contra hNoZero
  push_neg at hNoZero
  have hPos : ∀ n : ℕ, 0 < M.countEvidenceMass (k + 1) (l + n) := by
    intro n
    exact
      lt_of_le_of_ne
        (BernoulliMixture.countEvidenceMass_nonneg M (k + 1) (l + n))
        (hNoZero n).symm
  exact
    (not_posteriorBernoulliMixturePrefixProcessWitness_of_positiveFirstTrueEvidenceMass
      M k l hZ hPos)
      hWitness

theorem posteriorBernoulliMixturePrefixProcessWitness_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hWitness : posteriorBernoulliMixturePrefixProcessWitness M k l hZ) :
    M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  have hNotPos : ¬ 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1) := by
    intro hInterior
    exact
      (not_posteriorBernoulliMixturePrefixProcessWitness_of_interiorMixingMass
        M k l hZ hInterior)
        hWitness
  exact le_antisymm (le_of_not_gt hNotPos) bot_le

theorem not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_mixedEvidence
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hk : 0 < k) (hl : 0 < l) :
    ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness
        M k l hZ carrier := by
  intro hCarrierWitness
  have hWitness : posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
    exact
      (posteriorBernoulliMixturePrefixProcessWitness_iff_existsCarrierWitness
        M k l hZ).2 ⟨carrier, hCarrierWitness⟩
  have hInteriorZero :
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 :=
    posteriorBernoulliMixturePrefixProcessWitness_zeroInteriorMixingMass
      M k l hZ hWitness
  have hCountZero :
      M.countEvidenceMass k l = 0 :=
    BernoulliMixture.countEvidenceMass_eq_zero_of_zeroInteriorMass_of_pos_of_pos
      M k l hk hl hInteriorZero
  exact hZ hCountZero

theorem not_posteriorBernoulliMixturePrefixProcessWitness_of_mixedEvidence
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hk : 0 < k) (hl : 0 < l) :
    ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  intro hWitness
  have hInteriorZero :
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 :=
    posteriorBernoulliMixturePrefixProcessWitness_zeroInteriorMixingMass
      M k l hZ hWitness
  have hCountZero :
      M.countEvidenceMass k l = 0 :=
    BernoulliMixture.countEvidenceMass_eq_zero_of_zeroInteriorMass_of_pos_of_pos
      M k l hk hl hInteriorZero
  exact hZ hCountZero

theorem bernoulliMixture_oneBitPrefixPrevision_true_add_false
    (M : BernoulliMixture) :
    (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
        oneBitTrueGamble +
      (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
        oneBitFalseGamble = 1 := by
  calc
    (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
        oneBitTrueGamble +
      (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
        oneBitFalseGamble =
        (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
          (oneBitTrueGamble + oneBitFalseGamble) := by
        symm
        exact
          (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision.add
            oneBitTrueGamble oneBitFalseGamble
    _ =
        (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
          (Gamble.const (1 : ℝ)) := by
        rw [oneBitTrueGamble_add_oneBitFalseGamble]
    _ = 1 := by
        simpa using
          (PrecisePrevision.map_const_one
            ((bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision))

theorem bernoulliMixture_allTruePrefixPrevision_eq_oneBitTrue_of_zeroInteriorMixingMass
    (M : BernoulliMixture)
    (n : ℕ) (hn : 0 < n)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision
        (PrecisePrevision.FiniteWeights.atomGamble (allTruePrefix n)) =
      (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
        oneBitTrueGamble := by
  rw [BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble,
    oneBitTrueGamble, BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  have hLeft :
      M.prob (allTruePrefix n) = M.countEvidenceMass 1 0 := by
    rw [← BernoulliMixture.countEvidenceMass_eq_prob_of_counts M (allTruePrefix n)]
    simpa [countTrue_allTruePrefix, countFalse_allTruePrefix] using
      (BernoulliMixture.countEvidenceMass_eq_countEvidenceMass_one_zero_of_zeroInteriorMass_of_pos
        M n hn hInterior)
  have hRight :
      M.prob oneBitTruePrefix = M.countEvidenceMass 1 0 := by
    rw [← BernoulliMixture.countEvidenceMass_eq_prob_of_counts M oneBitTruePrefix]
    simp [oneBitTruePrefix, Mettapedia.Logic.Exchangeability.countTrue,
      Mettapedia.Logic.Exchangeability.countFalse]
  rw [hLeft, hRight]

theorem bernoulliMixture_allFalsePrefixPrevision_eq_oneBitFalse_of_zeroInteriorMixingMass
    (M : BernoulliMixture)
    (n : ℕ) (hn : 0 < n)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision
        (PrecisePrevision.FiniteWeights.atomGamble (allFalsePrefix n)) =
      (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
        oneBitFalseGamble := by
  rw [BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble,
    oneBitFalseGamble, BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  have hLeft :
      M.prob (allFalsePrefix n) = M.countEvidenceMass 0 1 := by
    rw [← BernoulliMixture.countEvidenceMass_eq_prob_of_counts M (allFalsePrefix n)]
    simpa [countTrue_allFalsePrefix, countFalse_allFalsePrefix] using
      (BernoulliMixture.countEvidenceMass_eq_countEvidenceMass_zero_one_of_zeroInteriorMass_of_pos
        M n hn hInterior)
  have hRight :
      M.prob oneBitFalsePrefix = M.countEvidenceMass 0 1 := by
    rw [← BernoulliMixture.countEvidenceMass_eq_prob_of_counts M oneBitFalsePrefix]
    simp [oneBitFalsePrefix, Mettapedia.Logic.Exchangeability.countTrue,
      Mettapedia.Logic.Exchangeability.countFalse]
  rw [hLeft, hRight]

theorem bernoulliMixture_prefixAtom_eq_zero_of_zeroInteriorMixingMass_of_countTrue_pos_of_countFalse_pos
    (M : BernoulliMixture)
    {n : ℕ} (xs : Fin n → Bool)
    (hTrue : 0 < Mettapedia.Logic.Exchangeability.countTrue xs)
    (hFalse : 0 < Mettapedia.Logic.Exchangeability.countFalse xs)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision
        (PrecisePrevision.FiniteWeights.atomGamble xs) = 0 := by
  rw [BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  rw [← BernoulliMixture.countEvidenceMass_eq_prob_of_counts M xs]
  exact
    BernoulliMixture.countEvidenceMass_eq_zero_of_zeroInteriorMass_of_pos_of_pos
      M
      (Mettapedia.Logic.Exchangeability.countTrue xs)
      (Mettapedia.Logic.Exchangeability.countFalse xs)
      hTrue hFalse hInterior

theorem posteriorBernoulliMixture_oneBitPrefixPrevision_true_add_false
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitTrueGamble +
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitFalseGamble = 1 := by
  calc
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitTrueGamble +
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitFalseGamble =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
          (oneBitTrueGamble + oneBitFalseGamble) := by
        symm
        exact
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision.add
            oneBitTrueGamble oneBitFalseGamble
    _ =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
          (Gamble.const (1 : ℝ)) := by
        rw [oneBitTrueGamble_add_oneBitFalseGamble]
    _ = 1 := by
        simpa using
          (PrecisePrevision.map_const_one
            ((bernoulliMixturePrefixLaw_analytic
              (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision))

theorem posteriorBernoulliMixture_allTruePrefixPrevision_eq_oneBitTrue_of_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (hn : 0 < n)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision
        (PrecisePrevision.FiniteWeights.atomGamble (allTruePrefix n)) =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitTrueGamble := by
  rw [BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble,
    oneBitTrueGamble, BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  rw [BernoulliMixture.posteriorBernoulliMixture_prob_eq_countEvidenceMass_ratio,
    BernoulliMixture.posteriorBernoulliMixture_prob_eq_countEvidenceMass_ratio]
  simp [countTrue_allTruePrefix, countFalse_allTruePrefix]
  by_cases hl0 : l = 0
  · subst hl0
    have hkLeft : 0 < k + n := Nat.add_pos_right k hn
    have hkRight : 0 < k + 1 := Nat.succ_pos k
    have hLeft :
        M.countEvidenceMass (k + n) 0 = M.countEvidenceMass 1 0 :=
      BernoulliMixture.countEvidenceMass_eq_countEvidenceMass_one_zero_of_zeroInteriorMass_of_pos
        M (k + n) hkLeft hInterior
    have hRight :
        M.countEvidenceMass
            (k + Mettapedia.Logic.Exchangeability.countTrue oneBitTruePrefix)
            (0 + Mettapedia.Logic.Exchangeability.countFalse oneBitTruePrefix) =
          M.countEvidenceMass 1 0 := by
      simpa [oneBitTruePrefix, Mettapedia.Logic.Exchangeability.countTrue,
        Mettapedia.Logic.Exchangeability.countFalse] using
        (BernoulliMixture.countEvidenceMass_eq_countEvidenceMass_one_zero_of_zeroInteriorMass_of_pos
          M (k + 1) hkRight hInterior)
    rw [hLeft, hRight]
  · have hl : 0 < l := Nat.pos_of_ne_zero hl0
    have hLeftZero :
        M.countEvidenceMass (k + n) l = 0 :=
      BernoulliMixture.countEvidenceMass_eq_zero_of_zeroInteriorMass_of_pos_of_pos
        M (k + n) l (Nat.add_pos_right k hn) hl hInterior
    have hRightZero :
        M.countEvidenceMass (k + 1) l = 0 :=
      BernoulliMixture.countEvidenceMass_eq_zero_of_zeroInteriorMass_of_pos_of_pos
        M (k + 1) l (Nat.succ_pos k) hl hInterior
    rw [hLeftZero]
    simpa [oneBitTruePrefix, Mettapedia.Logic.Exchangeability.countTrue,
      Mettapedia.Logic.Exchangeability.countFalse] using
      congrArg (fun x => x / M.countEvidenceMass k l) hRightZero.symm

theorem posteriorBernoulliMixture_allFalsePrefixPrevision_eq_oneBitFalse_of_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (n : ℕ) (hn : 0 < n)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision
        (PrecisePrevision.FiniteWeights.atomGamble (allFalsePrefix n)) =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
        oneBitFalseGamble := by
  rw [BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble,
    oneBitFalseGamble, BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  rw [BernoulliMixture.posteriorBernoulliMixture_prob_eq_countEvidenceMass_ratio,
    BernoulliMixture.posteriorBernoulliMixture_prob_eq_countEvidenceMass_ratio]
  simp [countTrue_allFalsePrefix, countFalse_allFalsePrefix]
  by_cases hk0 : k = 0
  · subst hk0
    have hlLeft : 0 < l + n := Nat.add_pos_right l hn
    have hlRight : 0 < l + 1 := Nat.succ_pos l
    have hLeft :
        M.countEvidenceMass 0 (l + n) = M.countEvidenceMass 0 1 :=
      BernoulliMixture.countEvidenceMass_eq_countEvidenceMass_zero_one_of_zeroInteriorMass_of_pos
        M (l + n) hlLeft hInterior
    have hRight :
        M.countEvidenceMass
            (0 + Mettapedia.Logic.Exchangeability.countTrue oneBitFalsePrefix)
            (l + Mettapedia.Logic.Exchangeability.countFalse oneBitFalsePrefix) =
          M.countEvidenceMass 0 1 := by
      simpa [oneBitFalsePrefix, Mettapedia.Logic.Exchangeability.countTrue,
        Mettapedia.Logic.Exchangeability.countFalse] using
        (BernoulliMixture.countEvidenceMass_eq_countEvidenceMass_zero_one_of_zeroInteriorMass_of_pos
          M (l + 1) hlRight hInterior)
    rw [hLeft, hRight]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hLeftZero :
        M.countEvidenceMass k (l + n) = 0 :=
      BernoulliMixture.countEvidenceMass_eq_zero_of_zeroInteriorMass_of_pos_of_pos
        M k (l + n) hk (Nat.add_pos_right l hn) hInterior
    have hRightZero :
        M.countEvidenceMass k (l + 1) = 0 :=
      BernoulliMixture.countEvidenceMass_eq_zero_of_zeroInteriorMass_of_pos_of_pos
        M k (l + 1) hk (Nat.succ_pos l) hInterior
    rw [hLeftZero]
    simpa [oneBitFalsePrefix, Mettapedia.Logic.Exchangeability.countTrue,
      Mettapedia.Logic.Exchangeability.countFalse] using
      congrArg (fun x => x / M.countEvidenceMass k l) hRightZero.symm

theorem posteriorBernoulliMixture_prefixAtom_eq_zero_of_zeroInteriorMixingMass_of_countTrue_pos_of_countFalse_pos
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    {n : ℕ} (xs : Fin n → Bool)
    (hTrue : 0 < Mettapedia.Logic.Exchangeability.countTrue xs)
    (hFalse : 0 < Mettapedia.Logic.Exchangeability.countFalse xs)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision
        (PrecisePrevision.FiniteWeights.atomGamble xs) = 0 := by
  rw [BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
  rw [BernoulliMixture.posteriorBernoulliMixture_prob_eq_countEvidenceMass_ratio]
  have hNumZero :
      M.countEvidenceMass
        (k + Mettapedia.Logic.Exchangeability.countTrue xs)
        (l + Mettapedia.Logic.Exchangeability.countFalse xs) = 0 :=
    BernoulliMixture.countEvidenceMass_eq_zero_of_zeroInteriorMass_of_pos_of_pos
      M
      (k + Mettapedia.Logic.Exchangeability.countTrue xs)
      (l + Mettapedia.Logic.Exchangeability.countFalse xs)
      (Nat.add_pos_right k hTrue)
      (Nat.add_pos_right l hFalse)
      hInterior
  rw [hNumZero, zero_div]

theorem posteriorBernoulliMixturePrefixProcessWitness_of_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  classical
  let t : ℝ :=
    (bernoulliMixturePrefixLaw_analytic
      (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
      oneBitTrueGamble
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact
      ((bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision).lower_bound
        oneBitTrueGamble 0 (by
          intro xs
          simpa [oneBitTrueGamble] using
            (PrecisePrevision.FiniteWeights.atomGamble_nonneg oneBitTruePrefix xs))
  have hFalseNonneg :
      0 ≤
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
          oneBitFalseGamble := by
    exact
      ((bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision).lower_bound
        oneBitFalseGamble 0 (by
          intro xs
          simpa [oneBitFalseGamble] using
            (PrecisePrevision.FiniteWeights.atomGamble_nonneg oneBitFalsePrefix xs))
  have hSum :
      t +
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
          oneBitFalseGamble = 1 := by
    simpa [t] using
      posteriorBernoulliMixture_oneBitPrefixPrevision_true_add_false M k l hZ
  have ht1 : t ≤ 1 := by
    linarith
  let P : PrecisePrevision (ℕ → Bool) :=
    PrecisePrevision.mix t
      (PrecisePrevision.dirac allTruePath)
      (PrecisePrevision.dirac allFalsePath)
      ht0 ht1
  refine ⟨P, ?_⟩
  intro n X
  have hMarginalTrue :
      bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n
        (PrecisePrevision.dirac allTruePath) =
        PrecisePrevision.dirac (allTruePrefix n) := by
    ext Y
    rfl
  have hMarginalFalse :
      bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n
        (PrecisePrevision.dirac allFalsePath) =
        PrecisePrevision.dirac (allFalsePrefix n) := by
    ext Y
    rfl
  have hMarginalMix :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision n P =
        PrecisePrevision.mix t
          (PrecisePrevision.dirac (allTruePrefix n))
          (PrecisePrevision.dirac (allFalsePrefix n))
          ht0 ht1 := by
    change
      bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n P =
        PrecisePrevision.mix t
          (PrecisePrevision.dirac (allTruePrefix n))
          (PrecisePrevision.dirac (allFalsePrefix n))
          ht0 ht1
    rw [ProjectiveCylinderSystem.marginalPrevision_mix]
    rw [hMarginalTrue, hMarginalFalse]
    rfl
  have hLocalEq :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision n P =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision := by
    cases n with
    | zero =>
        have hWeights :
            PrecisePrevision.FiniteWeights.ofPrecisePrevision
              (Ω := Fin 0 → Bool)
              ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision 0 P) =
              PrecisePrevision.FiniteWeights.ofPrecisePrevision
                (Ω := Fin 0 → Bool)
                ((bernoulliMixturePrefixLaw_analytic
                  (M.posteriorBernoulliMixture k l hZ) 0).toPrecisePrevision) := by
          ext xs
          have hxs : xs = default := by
            ext i
            exact Fin.elim0 i
          subst hxs
          rw [PrecisePrevision.FiniteWeights.ofPrecisePrevision_weight,
            PrecisePrevision.FiniteWeights.ofPrecisePrevision_weight]
          rw [hMarginalMix]
          have hTrue0 : allTruePrefix 0 = (default : Fin 0 → Bool) := by
            ext i
            exact Fin.elim0 i
          have hFalse0 : allFalsePrefix 0 = (default : Fin 0 → Bool) := by
            ext i
            exact Fin.elim0 i
          have hLeft :
              (PrecisePrevision.mix t
                  (PrecisePrevision.dirac (allTruePrefix 0))
                  (PrecisePrevision.dirac (allFalsePrefix 0)) ht0 ht1)
                (PrecisePrevision.FiniteWeights.atomGamble (default : Fin 0 → Bool)) = 1 := by
            simp [PrecisePrevision.mix, PrecisePrevision.FiniteWeights.atomGamble, t,
              hTrue0, hFalse0]
          have hTotal :=
            (bernoulliMixturePrefixLaw_analytic
              (M.posteriorBernoulliMixture k l hZ) 0).total
          have hRight :
              (bernoulliMixturePrefixLaw_analytic
                  (M.posteriorBernoulliMixture k l hZ) 0).toPrecisePrevision
                (PrecisePrevision.FiniteWeights.atomGamble (default : Fin 0 → Bool)) = 1 := by
            simp only [BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
            rw [Fintype.sum_unique] at hTotal
            exact hTotal
          exact hLeft.trans hRight.symm
        have hPrec := congrArg PrecisePrevision.FiniteWeights.toPrecisePrevision hWeights
        rw [PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision,
          PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision] at hPrec
        exact hPrec
    | succ m =>
        have hWeights :
            PrecisePrevision.FiniteWeights.ofPrecisePrevision
              (Ω := Fin (Nat.succ m) → Bool)
              ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision (Nat.succ m) P) =
              PrecisePrevision.FiniteWeights.ofPrecisePrevision
                (Ω := Fin (Nat.succ m) → Bool)
                ((bernoulliMixturePrefixLaw_analytic
                  (M.posteriorBernoulliMixture k l hZ) (Nat.succ m)).toPrecisePrevision) := by
          ext xs
          rw [PrecisePrevision.FiniteWeights.ofPrecisePrevision_weight,
            PrecisePrevision.FiniteWeights.ofPrecisePrevision_weight]
          rw [hMarginalMix]
          by_cases hEqTrue : xs = allTruePrefix (Nat.succ m)
          · have hEqFalse : xs ≠ allFalsePrefix (Nat.succ m) := by
              intro hEqFalse'
              exact
                allTruePrefix_ne_allFalsePrefix (Nat.succ_pos m)
                  (hEqTrue.symm.trans hEqFalse')
            subst hEqTrue
            have hEqFalse' : allFalsePrefix (Nat.succ m) ≠ allTruePrefix (Nat.succ m) := by
              intro h
              exact hEqFalse h.symm
            have hLeft :
                (PrecisePrevision.mix t
                    (PrecisePrevision.dirac (allTruePrefix (Nat.succ m)))
                    (PrecisePrevision.dirac (allFalsePrefix (Nat.succ m))) ht0 ht1)
                  (PrecisePrevision.FiniteWeights.atomGamble (allTruePrefix (Nat.succ m))) = t := by
              simp [PrecisePrevision.mix, PrecisePrevision.FiniteWeights.atomGamble,
                hEqFalse', t]
            have hRight :
                (bernoulliMixturePrefixLaw_analytic
                    (M.posteriorBernoulliMixture k l hZ) (Nat.succ m)).toPrecisePrevision
                  (PrecisePrevision.FiniteWeights.atomGamble (allTruePrefix (Nat.succ m))) = t := by
              simpa [t] using
                posteriorBernoulliMixture_allTruePrefixPrevision_eq_oneBitTrue_of_zeroInteriorMixingMass
                  M k l hZ (Nat.succ m) (Nat.succ_pos m) hInterior
            exact hLeft.trans hRight.symm
          · by_cases hEqFalse : xs = allFalsePrefix (Nat.succ m)
            · subst hEqFalse
              have hEqTrue' : allTruePrefix (Nat.succ m) ≠ allFalsePrefix (Nat.succ m) := by
                intro h
                exact hEqTrue h.symm
              have hLeft :
                  (PrecisePrevision.mix t
                      (PrecisePrevision.dirac (allTruePrefix (Nat.succ m)))
                      (PrecisePrevision.dirac (allFalsePrefix (Nat.succ m))) ht0 ht1)
                    (PrecisePrevision.FiniteWeights.atomGamble (allFalsePrefix (Nat.succ m))) =
                    1 - t := by
                simp [PrecisePrevision.mix, PrecisePrevision.FiniteWeights.atomGamble,
                  hEqTrue', t]
              have hOneBitFalse :
                  (bernoulliMixturePrefixLaw_analytic
                      (M.posteriorBernoulliMixture k l hZ) (Nat.succ m)).toPrecisePrevision
                      (PrecisePrevision.FiniteWeights.atomGamble (allFalsePrefix (Nat.succ m))) =
                    (bernoulliMixturePrefixLaw_analytic
                      (M.posteriorBernoulliMixture k l hZ) 1).toPrecisePrevision
                      oneBitFalseGamble :=
                posteriorBernoulliMixture_allFalsePrefixPrevision_eq_oneBitFalse_of_zeroInteriorMixingMass
                  M k l hZ (Nat.succ m) (Nat.succ_pos m) hInterior
              have hRight :
                  (bernoulliMixturePrefixLaw_analytic
                      (M.posteriorBernoulliMixture k l hZ) (Nat.succ m)).toPrecisePrevision
                    (PrecisePrevision.FiniteWeights.atomGamble (allFalsePrefix (Nat.succ m))) =
                    1 - t := by
                linarith [hSum, hOneBitFalse]
              exact hLeft.trans hRight.symm
            · have hCountTruePos :
                  0 < Mettapedia.Logic.Exchangeability.countTrue xs := by
                by_contra hNotPos
                have hZero : Mettapedia.Logic.Exchangeability.countTrue xs = 0 :=
                  Nat.eq_zero_of_not_pos hNotPos
                exact hEqFalse (eq_allFalsePrefix_of_countTrue_eq_zero hZero)
              have hCountFalsePos :
                  0 < Mettapedia.Logic.Exchangeability.countFalse xs := by
                by_contra hNotPos
                have hZero : Mettapedia.Logic.Exchangeability.countFalse xs = 0 :=
                  Nat.eq_zero_of_not_pos hNotPos
                exact hEqTrue (eq_allTruePrefix_of_countFalse_eq_zero hZero)
              have hEqTrue' : allTruePrefix (Nat.succ m) ≠ xs := by
                intro h
                exact hEqTrue h.symm
              have hEqFalse' : allFalsePrefix (Nat.succ m) ≠ xs := by
                intro h
                exact hEqFalse h.symm
              have hLeft :
                  (PrecisePrevision.mix t
                      (PrecisePrevision.dirac (allTruePrefix (Nat.succ m)))
                      (PrecisePrevision.dirac (allFalsePrefix (Nat.succ m))) ht0 ht1)
                    (PrecisePrevision.FiniteWeights.atomGamble xs) = 0 := by
                simp [PrecisePrevision.mix, PrecisePrevision.FiniteWeights.atomGamble,
                  hEqTrue', hEqFalse', t]
              have hRight :
                  (bernoulliMixturePrefixLaw_analytic
                      (M.posteriorBernoulliMixture k l hZ) (Nat.succ m)).toPrecisePrevision
                    (PrecisePrevision.FiniteWeights.atomGamble xs) = 0 := by
                exact
                  posteriorBernoulliMixture_prefixAtom_eq_zero_of_zeroInteriorMixingMass_of_countTrue_pos_of_countFalse_pos
                  M k l hZ xs hCountTruePos hCountFalsePos hInterior
              exact hLeft.trans hRight.symm
        have hPrec := congrArg PrecisePrevision.FiniteWeights.toPrecisePrevision hWeights
        rw [PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision,
          PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision] at hPrec
        exact hPrec
  exact congrArg (fun Q => Q X) hLocalEq

theorem posteriorBernoulliMixturePrefixProcessWitness_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    posteriorBernoulliMixturePrefixProcessWitness M k l hZ ↔
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  constructor
  · exact posteriorBernoulliMixturePrefixProcessWitness_zeroInteriorMixingMass M k l hZ
  · exact posteriorBernoulliMixturePrefixProcessWitness_of_zeroInteriorMixingMass M k l hZ

theorem posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (∃ carrier : CredalPrevisionSet (ℕ → Bool),
        posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier) ↔
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  simpa [posteriorBernoulliMixturePrefixProcessWitness_iff_existsCarrierWitness M k l hZ] using
    (posteriorBernoulliMixturePrefixProcessWitness_iff_zeroInteriorMixingMass M k l hZ)

/-- Prefix marginal consistency supplies local coherence for the canonical
largest-prefix finite joint-window system. -/
theorem posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem_localCoherent_of_marginalConsistent
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hMarginal :
      posteriorBernoulliMixturePrefixProcessMarginalConsistent M k l hZ) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowLocalCoherent
      (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ) := by
  intro u
  let R : PrecisePrevision
      ((posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
        M k l hZ).Joint u) :=
    (bernoulliMixturePrefixLaw_analytic
      (M.posteriorBernoulliMixture k l hZ)
      (prefixWindowJointLength u)).toPrecisePrevision
  refine ⟨R, ?_⟩
  intro i hi
  rw [mem_dominatingPreciseCompletions]
  intro X
  have hLower :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower i X ≤
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) i).toPrecisePrevision X := by
    rw [posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_apply]
    simpa [posteriorBernoulliMixturePrefixLawAt,
      posteriorBernoulliMixtureSetPrefixLaw, bernoulliMixturePrefixLawAt,
      posteriorBernoulliMixtureSet] using
      (impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
        (posteriorBernoulliMixtureSet M k l hZ) i
        (posteriorBernoulliMixturePrefixLawAt M k l hZ i)
        (posteriorBernoulliMixture_mem_posteriorSet M k l hZ) X)
  have hMarginalEq :
      (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
          M k l hZ).jointMarginalPrevision u i hi R X =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) i).toPrecisePrevision X := by
    rw [ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem.jointMarginalPrevision_apply]
    simpa [R, ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem.jointCylinderGamble,
      posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem,
      bernoulliMixturePrefixProcessFiniteJointWindowSystem] using
      (hMarginal u (i := i) hi X)
  exact hLower.trans_eq hMarginalEq.symm

/-- Extend a finite Boolean prefix to an infinite path by padding the tail with
`false`.  This is the explicit window-by-window raw carrier used to realize a
finite prefix law without pretending that one global all-prefix raw witness
exists. -/
def prefixTailFalseExtension {n : ℕ} (xs : Fin n → Bool) : ℕ → Bool :=
  fun j => if hj : j < n then xs ⟨j, hj⟩ else false

theorem prefixTailFalseExtension_apply_castLE
    {n i : ℕ} (hi : i ≤ n) (xs : Fin n → Bool) (k : Fin i) :
    prefixTailFalseExtension xs k = xs (Fin.castLE hi k) := by
  have hk : (k : ℕ) < n := lt_of_lt_of_le k.is_lt hi
  have hcast : (⟨(k : ℕ), hk⟩ : Fin n) = Fin.castLE hi k := by
    ext
    rfl
  simpa [prefixTailFalseExtension, hk] using congrArg xs hcast

/-- Finite joint-window precise previsions can be pushed forward to raw global
previsions by extending each prefix state with a `false` tail. -/
noncomputable def prefixTailFalseExtensionPrevision
    {n : ℕ} (R : PrecisePrevision (Fin n → Bool)) :
    PrecisePrevision (ℕ → Bool) := by
  classical
  exact
    (PrecisePrevision.FiniteWeights.ofPrecisePrevision R).pushForwardPrevision
      prefixTailFalseExtension

theorem prefixTailFalseExtensionPrevision_marginal_eq
    {n i : ℕ} (hi : i ≤ n)
    (R : PrecisePrevision (Fin n → Bool))
    (X : Gamble (Fin i → Bool)) :
    bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision i
        (prefixTailFalseExtensionPrevision R) X =
      R (fun xs => X (fun k => xs (Fin.castLE hi k))) := by
  classical
  rw [ProjectiveCylinderSystem.marginalPrevision_apply]
  unfold prefixTailFalseExtensionPrevision
  change
    (PrecisePrevision.FiniteWeights.ofPrecisePrevision R).toPrecisePrevision
      (fun xs =>
        (bernoulliMixturePrefixProcessCylinderSystem.cylinderGamble i X)
          (prefixTailFalseExtension xs)) =
      _
  rw [PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision]
  congr 1
  funext xs
  unfold ProjectiveCylinderSystem.cylinderGamble
  congr 1
  funext k
  exact prefixTailFalseExtension_apply_castLE hi xs k

/-- Explicit raw carrier generated by finite prefix laws extended with `false`
tails.  This is the honest family of per-window realizers for the canonical
largest-prefix joint system. -/
def prefixTailFalseExtensionCarrier : CredalPrevisionSet (ℕ → Bool) :=
  Set.range (fun s : Σ n : ℕ, PrecisePrevision (Fin n → Bool) =>
    prefixTailFalseExtensionPrevision s.2)

/-- The canonical largest-prefix finite-window system is realized inside the
explicit tail-false raw carrier, one finite window at a time. -/
theorem bernoulliMixturePrefixProcess_jointPrevisionsRealizedIn_prefixTailFalseExtensionCarrier
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).jointPrevisionsRealizedInCarrier
      (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC)
      prefixTailFalseExtensionCarrier := by
  intro u R _hR
  refine ⟨prefixTailFalseExtensionPrevision R, ?_, ?_⟩
  · exact ⟨⟨prefixWindowJointLength u, R⟩, rfl⟩
  · intro i hi
    ext X
    exact prefixTailFalseExtensionPrevision_marginal_eq
      (n := prefixWindowJointLength u) (i := i)
      (prefixWindow_le_jointLength u hi) R X

/-- Any raw carrier containing the explicit tail-false finite-window realizers
inherits canonical carrier realization for the imprecise Bernoulli-mixture
prefix process. -/
theorem bernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_prefixTailFalseExtensionCarrierSubset
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).jointPrevisionsRealizedInCarrier
      (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC)
      carrier := by
  intro u R _hR
  refine ⟨prefixTailFalseExtensionPrevision R, ?_, ?_⟩
  · exact hSubset ⟨⟨prefixWindowJointLength u, R⟩, rfl⟩
  · intro i hi
    ext X
    exact prefixTailFalseExtensionPrevision_marginal_eq
      (n := prefixWindowJointLength u) (i := i)
      (prefixWindow_le_jointLength u hi) R X

/-- The canonical largest-prefix finite-window system is realized inside the
explicit tail-false raw carrier, one finite window at a time. -/
theorem posteriorBernoulliMixturePrefixProcess_jointPrevisionsRealizedIn_prefixTailFalseExtensionCarrier
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
      (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ)
      prefixTailFalseExtensionCarrier := by
  intro u R _hR
  refine ⟨prefixTailFalseExtensionPrevision R, ?_, ?_⟩
  · exact ⟨⟨prefixWindowJointLength u, R⟩, rfl⟩
  · intro i hi
    ext X
    exact prefixTailFalseExtensionPrevision_marginal_eq
      (n := prefixWindowJointLength u) (i := i)
      (prefixWindow_le_jointLength u hi) R X

/-- Any raw carrier containing the explicit tail-false finite-window realizers
inherits canonical carrier realization for the posterior prefix process. -/
theorem posteriorBernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_prefixTailFalseExtensionCarrierSubset
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
      (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ)
      carrier := by
  intro u R _hR
  refine ⟨prefixTailFalseExtensionPrevision R, ?_, ?_⟩
  · exact hSubset ⟨⟨prefixWindowJointLength u, R⟩, rfl⟩
  · intro i hi
    ext X
    exact prefixTailFalseExtensionPrevision_marginal_eq
      (n := prefixWindowJointLength u) (i := i)
      (prefixWindow_le_jointLength u hi) R X

/-- Any raw carrier containing the explicit tail-false finite-window realizers
already satisfies the canonical finite-window compatibility/FIP hypothesis for
the posterior prefix process.  This isolates the remaining raw-side boundary to
carrier packaging assumptions such as compactness, convexity, and closed local
constraints. -/
theorem posteriorBernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_prefixTailFalseExtensionCarrierSubset
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowCompatibleInCarrier
      carrier := by
  refine
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ)
      (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ)
      carrier
      ?_
      ?_
  · exact
      posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem_localCoherent_of_marginalConsistent
        M k l hZ
        (posteriorBernoulliMixturePrefixProcessMarginalConsistent_analytic M k l hZ)
  · exact
      posteriorBernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_prefixTailFalseExtensionCarrierSubset
        M k l hZ carrier hSubset

/-- Main imprecise de Finetti process-law synthesis crown, stated at the
minimal compact finite-window compatibility boundary. -/
theorem impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).localLower n)})
    (hFIP :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).finiteWindowCompatibleInCarrier
        carrier) :
    ImpreciseDeFinettiProcessLawCrown C hLaw hC where
  processCompatibleCompletion :=
    impreciseDeFinetti_processLawCompatibleCompletion_of_finiteWindowCompatibleInCarrier
      C hLaw hC carrier hCompact hCarrierConvex hClosed hFIP
  prefixCompatibleCompletion := by
    intro n
    exact bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
      C n (bernoulliMixturePrefixLawAt C hLaw n) hC
  prefixLowerEnvelopeReadout := by
    intro n X
    exact bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension
      C n (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixUpperEnvelopeReadout := by
    intro n X
    exact bernoulliMixturePrefixProjectiveSpec_upperEnvelope
      C n (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixWidthComplementReadout := by
    intro n X
    exact bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement
      C n (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixMidpointReadout := by
    intro n X
    exact bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint
      C n (bernoulliMixturePrefixLawAt C hLaw n) X
  agreementDetermines := by
    intro n X hAgree
    exact impreciseDeFinetti_prefixAgreement_projectiveDetermines
      C hLaw n X hAgree
  agreementWidthComplement_eq_one := by
    intro n X hAgree
    exact impreciseDeFinetti_prefixAgreement_confidence_eq_one
      C hLaw hC n X hAgree
  disagreementStrictWidth := by
    intro n X M N hM hN hlt
    exact impreciseDeFinetti_prefixDisagreement_strictWidth
      C hLaw n X hM hN hlt
  disagreementEnvelopeWidth_pos := by
    intro n X M N hM hN hlt
    exact impreciseDeFinetti_prefixDisagreement_envelopeWidth_pos
      C hLaw n X hM hN hlt
  disagreementWidthComplement_lt_one := by
    intro n X M N hM hN hlt
    exact impreciseDeFinetti_prefixDisagreement_confidence_lt_one
      C hLaw n X hM hN hlt

/-- The exact raw all-gambles compatibility predicate for an imprecise de
Finetti prefix-process lower envelope.

Positive example: any instance of `ImpreciseDeFinettiProcessLawCrown` supplies
this predicate by projection.  Negative example: in the posterior singleton
case with positive interior mixing mass, the already-proved dichotomy refutes
this predicate through the corresponding posterior process-law crown. -/
def ImpreciseDeFinettiRawProcessCompatible
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) : Prop :=
  ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).toCredalSpec).hasCompatibleCompletion

/-- The process-law crown follows from the exact raw compatibility predicate;
the remaining prefix envelope, width, and agreement/disagreement readouts are
the finite-prefix de Finetti machinery already proved above. -/
theorem impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_rawProcessCompatible
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (hCompat : ImpreciseDeFinettiRawProcessCompatible C hLaw hC) :
    ImpreciseDeFinettiProcessLawCrown C hLaw hC where
  processCompatibleCompletion := hCompat
  prefixCompatibleCompletion := by
    intro n
    exact bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
      C n (bernoulliMixturePrefixLawAt C hLaw n) hC
  prefixLowerEnvelopeReadout := by
    intro n X
    exact bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension
      C n (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixUpperEnvelopeReadout := by
    intro n X
    exact bernoulliMixturePrefixProjectiveSpec_upperEnvelope
      C n (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixWidthComplementReadout := by
    intro n X
    exact bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement
      C n (bernoulliMixturePrefixLawAt C hLaw n) X
  prefixMidpointReadout := by
    intro n X
    exact bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint
      C n (bernoulliMixturePrefixLawAt C hLaw n) X
  agreementDetermines := by
    intro n X hAgree
    exact impreciseDeFinetti_prefixAgreement_projectiveDetermines
      C hLaw n X hAgree
  agreementWidthComplement_eq_one := by
    intro n X hAgree
    exact impreciseDeFinetti_prefixAgreement_confidence_eq_one
      C hLaw hC n X hAgree
  disagreementStrictWidth := by
    intro n X M N hM hN hlt
    exact impreciseDeFinetti_prefixDisagreement_strictWidth
      C hLaw n X hM hN hlt
  disagreementEnvelopeWidth_pos := by
    intro n X M N hM hN hlt
    exact impreciseDeFinetti_prefixDisagreement_envelopeWidth_pos
      C hLaw n X hM hN hlt
  disagreementWidthComplement_lt_one := by
    intro n X M N hM hN hlt
    exact impreciseDeFinetti_prefixDisagreement_confidence_lt_one
      C hLaw n X hM hN hlt

/-- Exact boundary form of the generic process-law crown: after all finite-prefix
readouts are factored out, its raw process-side content is precisely compatible
completion of the projective lower-envelope specification. -/
theorem impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_iff_rawProcessCompatible
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    ImpreciseDeFinettiProcessLawCrown C hLaw hC ↔
      ImpreciseDeFinettiRawProcessCompatible C hLaw hC := by
  constructor
  · intro hCrown
    exact hCrown.processCompatibleCompletion
  · intro hCompat
    exact
      impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_rawProcessCompatible
        C hLaw hC hCompat

/-- A respecting global lower prevision is the direct constructive route to the
raw compatibility predicate. -/
theorem ImpreciseDeFinettiRawProcessCompatible_of_respectsLocalLower
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (L : LowerPrevision (ℕ → Bool))
    (hL :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).respectsLocalLower L) :
    ImpreciseDeFinettiRawProcessCompatible C hLaw hC := by
  exact
    ProjectiveLocalLowerPrevisionSpec.hasCompatibleCompletion_of_respectsLocalLower
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC) L hL

/-- Exact lower-prevision form of raw compatibility: the projective lower
envelope has a compatible precise completion iff some global lower prevision
respects all local lower assessments. -/
theorem ImpreciseDeFinettiRawProcessCompatible_iff_exists_respectsLocalLower
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty) :
    ImpreciseDeFinettiRawProcessCompatible C hLaw hC ↔
      ∃ L : LowerPrevision (ℕ → Bool),
        (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).respectsLocalLower L := by
  let S := bernoulliMixturePrefixProcessLowerSpec C hLaw hC
  change S.toCredalSpec.hasCompatibleCompletion ↔
    ∃ L : LowerPrevision (ℕ → Bool), S.respectsLocalLower L
  constructor
  · intro hCompat
    rcases hCompat with ⟨P, hP⟩
    refine ⟨P.toLowerPrevision, ?_⟩
    intro i X
    have hPi :
        S.cylinders.marginalPrevision i P ∈
          dominatingPreciseCompletions (S.localLower i) := by
      exact hP i
    exact hPi X
  · rintro ⟨L, hL⟩
    exact
      ImpreciseDeFinettiRawProcessCompatible_of_respectsLocalLower
        C hLaw hC L hL

/-- Main imprecise de Finetti process-law synthesis crown. -/
theorem impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).localLower n)})
    (J : ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC))
    (hLocal :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).finiteWindowLocalCoherent J)
    (hRealize :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).jointPrevisionsRealizedInCarrier
        J carrier) :
    ImpreciseDeFinettiProcessLawCrown C hLaw hC := by
  have hFIP :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).finiteWindowCompatibleInCarrier
        carrier :=
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC) J carrier hLocal hRealize
  exact
    impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
      C hLaw hC carrier hCompact hCarrierConvex hClosed hFIP

/-- Canonical prefix marginal consistency plus carrier realization imply the
finite-window compatibility boundary consumed by the generic compact/FIP
completion theorem. -/
theorem bernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_prefixMarginalConsistentCarrierRealization
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hMarginal :
      bernoulliMixturePrefixProcessMarginalConsistent C hLaw)
    (hRealize :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).jointPrevisionsRealizedInCarrier
        (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC)
        carrier) :
    (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).finiteWindowCompatibleInCarrier
      carrier := by
  exact
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC)
      (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC)
      carrier
      (bernoulliMixturePrefixProcessFiniteJointWindowSystem_localCoherent_of_marginalConsistent
        C hLaw hC hMarginal)
      hRealize

/-- Canonical prefix marginal consistency plus any carrier containing the
explicit tail-false finite-window realizers imply the finite-window
compatibility boundary consumed by the generic compact/FIP completion theorem. -/
theorem bernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_marginalConsistent_prefixTailFalseExtensionCarrierSubset
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hMarginal :
      bernoulliMixturePrefixProcessMarginalConsistent C hLaw)
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).finiteWindowCompatibleInCarrier
      carrier := by
  exact
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC)
      (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC)
      carrier
      (bernoulliMixturePrefixProcessFiniteJointWindowSystem_localCoherent_of_marginalConsistent
        C hLaw hC hMarginal)
      (bernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_prefixTailFalseExtensionCarrierSubset
        C hLaw hC carrier hSubset)

/-- Canonical prefix marginal consistency plus carrier realization imply the
generic process-law compatible completion, without an arbitrary local-coherence
or finite-window-system witness. -/
theorem impreciseDeFinetti_processLawCompatibleCompletion_of_prefixMarginalConsistentCarrierRealization
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).localLower n)})
    (hMarginal :
      bernoulliMixturePrefixProcessMarginalConsistent C hLaw)
    (hRealize :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).jointPrevisionsRealizedInCarrier
        (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC)
        carrier) :
    ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).toCredalSpec).hasCompatibleCompletion := by
  exact
    impreciseDeFinetti_processLawCompatibleCompletion_of_finiteWindowCompatibleInCarrier
      C hLaw hC carrier hCompact hCarrierConvex hClosed
      (bernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_prefixMarginalConsistentCarrierRealization
        C hLaw hC carrier hMarginal hRealize)

/-- Main imprecise de Finetti process-law synthesis crown from the canonical
largest-prefix marginal-consistency condition plus carrier realization. -/
theorem impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_prefixMarginalConsistentCarrierRealization
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec C hLaw hC).localLower n)})
    (hMarginal :
      bernoulliMixturePrefixProcessMarginalConsistent C hLaw)
    (hRealize :
      (bernoulliMixturePrefixProcessLowerSpec C hLaw hC).jointPrevisionsRealizedInCarrier
        (bernoulliMixturePrefixProcessFiniteJointWindowSystem C hLaw hC)
        carrier) :
    ImpreciseDeFinettiProcessLawCrown C hLaw hC := by
  exact
    impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
      C hLaw hC carrier hCompact hCarrierConvex hClosed
      (bernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_prefixMarginalConsistentCarrierRealization
        C hLaw hC carrier hMarginal hRealize)

/-- For the canonical analytic prefix laws, any compact carrier containing the
explicit tail-false finite-window realizers already yields the full imprecise
de Finetti process-law crown.  This removes a separate local-coherence witness,
an explicit finite-window realization witness, and a separate marginal-
consistency assumption from the public synthesis boundary. -/
theorem impreciseDeFinetti_analyticProcessLaw_projectiveNaturalExtension_crown_of_prefixTailFalseExtensionCarrierSubset
    (C : Set BernoulliMixture)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec
          C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec
              C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).localLower n)})
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    ImpreciseDeFinettiProcessLawCrown
      C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC := by
  exact
    impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
      C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC
      carrier hCompact hCarrierConvex hClosed
      (bernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_marginalConsistent_prefixTailFalseExtensionCarrierSubset
        C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC
        carrier
        (bernoulliMixturePrefixProcessMarginalConsistent_analytic C)
        hSubset)

/-! ### Posterior process-law crown under finite-window compatibility/realization -/

/-- Finite-window/FIP completion for the posterior singleton process
specification, stated at the minimal compact carrier compatibility boundary. -/
theorem posteriorBernoulliMixture_processLawCompatibleCompletion_of_finiteWindowCompatibleInCarrier
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hFIP :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowCompatibleInCarrier
        carrier) :
    ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).hasCompatibleCompletion := by
  exact
    impreciseDeFinetti_processLawCompatibleCompletion_of_finiteWindowCompatibleInCarrier
      (posteriorBernoulliMixtureSet M k l hZ)
      (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
      (posteriorBernoulliMixtureSet_nonempty M k l hZ)
      carrier hCompact hCarrierConvex hClosed hFIP

/-- The explicit tail-false finite-window realizers already supply the
compatible-completion hypothesis for any compact/convex/closed raw carrier that
contains them. -/
theorem posteriorBernoulliMixture_processLawCompatibleCompletion_of_prefixTailFalseExtensionCarrierSubset
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).hasCompatibleCompletion :=
  posteriorBernoulliMixture_processLawCompatibleCompletion_of_finiteWindowCompatibleInCarrier
    M k l hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_prefixTailFalseExtensionCarrierSubset
      M k l hZ carrier hSubset)

/-- Finite-window realization/FIP completion for the posterior singleton
process specification.

This is the posterior-specific adapter into the existing compact/FIP process
bridge.  The remaining carrier hypotheses are explicit: compactness/convexity
and closed local constraints for the chosen carrier, plus a finite joint-window
system whose locally coherent joint previsions are realized in that carrier. -/
theorem posteriorBernoulliMixture_processLawCompatibleCompletion_of_finiteWindowRealization
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (J : ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ))
    (hLocal :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowLocalCoherent J)
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
        J carrier) :
    ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).hasCompatibleCompletion := by
  have hFIP :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowCompatibleInCarrier
        carrier :=
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ)
      J carrier hLocal hRealize
  exact
    posteriorBernoulliMixture_processLawCompatibleCompletion_of_finiteWindowCompatibleInCarrier
      M k l hZ carrier hCompact hCarrierConvex hClosed hFIP

/-- Posterior/update transport into the process-law crown, stated at the
minimal compact finite-window compatibility boundary.  The generic credal-set
and all-prefix-law obligations are generated by the normalized posterior
Bernoulli mixture itself. -/
theorem posteriorBernoulliMixture_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hFIP :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowCompatibleInCarrier
        carrier) :
    ImpreciseDeFinettiProcessLawCrown
      (posteriorBernoulliMixtureSet M k l hZ)
      (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
      (posteriorBernoulliMixtureSet_nonempty M k l hZ) := by
  exact
    impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
      (posteriorBernoulliMixtureSet M k l hZ)
      (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
      (posteriorBernoulliMixtureSet_nonempty M k l hZ)
      carrier hCompact hCarrierConvex hClosed hFIP

/-- The explicit tail-false finite-window realizers already supply the
projective natural-extension crown for any compact/convex/closed raw carrier
that contains them. -/
theorem posteriorBernoulliMixture_processLaw_projectiveNaturalExtension_crown_of_prefixTailFalseExtensionCarrierSubset
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    ImpreciseDeFinettiProcessLawCrown
      (posteriorBernoulliMixtureSet M k l hZ)
      (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
      (posteriorBernoulliMixtureSet_nonempty M k l hZ) :=
  posteriorBernoulliMixture_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
    M k l hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_prefixTailFalseExtensionCarrierSubset
      M k l hZ carrier hSubset)

theorem posteriorBernoulliMixture_processLaw_projectiveNaturalExtension_crown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (J : ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ))
    (hLocal :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowLocalCoherent J)
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
        J carrier) :
    ImpreciseDeFinettiProcessLawCrown
      (posteriorBernoulliMixtureSet M k l hZ)
      (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
      (posteriorBernoulliMixtureSet_nonempty M k l hZ) := by
  have hFIP :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowCompatibleInCarrier
        carrier :=
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ)
      J carrier hLocal hRealize
  exact
    posteriorBernoulliMixture_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
      M k l hZ carrier hCompact hCarrierConvex hClosed hFIP

/-- Paper-facing posterior process-law package.  It records both the unconditional
finite-prefix posterior singleton result and the conditional process-law result
obtained once compact finite-window carrier compatibility is supplied. -/
structure PosteriorBernoulliMixtureProcessLawCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) : Prop where
  prefixProjectiveCrown :
    PosteriorBernoulliMixturePrefixProjectiveCrown M k l hZ
  processLawCrown :
    ImpreciseDeFinettiProcessLawCrown
      (posteriorBernoulliMixtureSet M k l hZ)
      (posteriorBernoulliMixtureSetPrefixLaw M k l hZ)
      (posteriorBernoulliMixtureSet_nonempty M k l hZ)
  processCompatibleCompletion :
    ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).hasCompatibleCompletion
  prefixEnvelopeWidth_eq_zero : ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    impreciseDeFinettiPrefixEnvelopeWidth
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X = 0
  prefixWidthComplement_eq_one : ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    impreciseDeFinettiPrefixEnvelopeWidthComplement
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X = 1

/-- Paper-facing posterior process-law package from the minimal compact
finite-window compatibility boundary. -/
theorem posteriorBernoulliMixture_processLawCrown_of_finiteWindowCompatibleInCarrier
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hFIP :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowCompatibleInCarrier
        carrier) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ where
  prefixProjectiveCrown :=
    posteriorBernoulliMixturePrefixProjectiveCrown M k l hZ
  processLawCrown :=
    posteriorBernoulliMixture_processLaw_projectiveNaturalExtension_crown_of_finiteWindowCompatibleInCarrier
      M k l hZ carrier hCompact hCarrierConvex hClosed hFIP
  processCompatibleCompletion :=
    posteriorBernoulliMixture_processLawCompatibleCompletion_of_finiteWindowCompatibleInCarrier
      M k l hZ carrier hCompact hCarrierConvex hClosed hFIP
  prefixEnvelopeWidth_eq_zero := by
    intro n X
    exact posteriorBernoulliMixturePrefixEnvelopeWidth_eq_zero M k l hZ n X
  prefixWidthComplement_eq_one := by
    intro n X
    exact posteriorBernoulliMixturePrefixEnvelopeWidthComplement_eq_one M k l hZ n X

/-- Paper-facing posterior process-law package from structured finite joint
window realization data. -/
theorem posteriorBernoulliMixture_processLawCrown_of_finiteWindowRealization
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (J : ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ))
    (hLocal :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowLocalCoherent J)
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
        J carrier) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ := by
  have hFIP :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowCompatibleInCarrier
        carrier :=
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ)
      J carrier hLocal hRealize
  exact
    posteriorBernoulliMixture_processLawCrown_of_finiteWindowCompatibleInCarrier
      M k l hZ carrier hCompact hCarrierConvex hClosed hFIP

/-- Paper-facing posterior process-law package from the canonical largest-prefix
finite joint-window system.

Compared with `posteriorBernoulliMixture_processLawCrown_of_finiteWindowRealization`,
this fixes the finite-window system `J` to the Boolean-prefix construction
`posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem`.  The remaining
local-coherence and carrier-realization hypotheses are therefore stated for a
canonical joint state space, not for an arbitrary witness. -/
theorem posteriorBernoulliMixture_processLawCrown_of_prefixFiniteWindowRealization
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hLocal :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).finiteWindowLocalCoherent
        (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ))
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
        (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ)
        carrier) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ :=
  posteriorBernoulliMixture_processLawCrown_of_finiteWindowRealization
    M k l hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ)
    hLocal hRealize

/-- Paper-facing posterior process-law package from canonical prefix marginal
consistency plus carrier realization.

This removes the standalone local-coherence assumption from the canonical
largest-prefix endpoint.  The remaining finite-window work is the concrete
prefix marginalization theorem and carrier realization for the same canonical
joint state spaces. -/
theorem posteriorBernoulliMixture_processLawCrown_of_prefixMarginalConsistentCarrierRealization
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hMarginal :
      posteriorBernoulliMixturePrefixProcessMarginalConsistent M k l hZ)
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
        (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ)
        carrier) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ :=
  posteriorBernoulliMixture_processLawCrown_of_prefixFiniteWindowRealization
    M k l hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem_localCoherent_of_marginalConsistent
      M k l hZ hMarginal)
    hRealize

/-- Paper-facing posterior process-law package from canonical carrier
realization alone.

The canonical finite-prefix marginal theorem is now discharged internally, so
the only remaining finite-window assumption at this endpoint is the explicit
carrier realization of those canonical joint previsions. -/
theorem posteriorBernoulliMixture_processLawCrown_of_prefixCarrierRealization
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
        (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ)
        carrier) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ :=
  posteriorBernoulliMixture_processLawCrown_of_prefixMarginalConsistentCarrierRealization
    M k l hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcessMarginalConsistent_analytic M k l hZ)
    hRealize

/-- A single global carrier witness with the analytic posterior prefix
marginals implies the stronger canonical finite-joint realization predicate. -/
theorem posteriorBernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_carrierWitness
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hWitness :
      posteriorBernoulliMixturePrefixProcessCarrierWitness
        M k l hZ carrier) :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).jointPrevisionsRealizedInCarrier
      (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem M k l hZ)
      carrier := by
  intro u R hR
  rcases hWitness with ⟨P, hPcarrier, hPmarg⟩
  refine ⟨P, hPcarrier, ?_⟩
  intro i hi
  have hJointEq :
      (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
          M k l hZ).jointMarginalPrevision u i hi R =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) i).toPrecisePrevision := by
    apply precisePrevision_eq_of_mem_dominatingPreciseCompletions_toLowerPrevision
    intro X
    have hRi :
        (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower i X ≤
          (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
            M k l hZ).jointMarginalPrevision u i hi R X :=
      hR i hi X
    rw [posteriorBernoulliMixturePrefixProcessLowerSpec_localLower_eq_analytic
      M k l hZ i X] at hRi
    simpa [PrecisePrevision.toLowerPrevision_apply] using hRi
  have hPmargEq :
      (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision i P
        = (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) i).toPrecisePrevision := by
    ext X
    exact hPmarg i X
  exact hPmargEq.trans hJointEq.symm

/-- Paper-facing posterior process-law package from a single global carrier
witness for the analytic posterior prefix laws.

The extra compact/convex/closed carrier packaging is supplied internally by the
singleton carrier generated by the witness itself, equipped with the discrete
topology.  So the honest remaining assumption here is exactly the witness, not
any auxiliary compactness scaffolding. -/
theorem posteriorBernoulliMixture_processLawCrown_of_prefixCarrierWitness
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hWitness :
      posteriorBernoulliMixturePrefixProcessCarrierWitness
        M k l hZ carrier) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ := by
  rcases hWitness with ⟨P, _hPcarrier, hPmarg⟩
  let carrier' : CredalPrevisionSet (ℕ → Bool) := ({P} : CredalPrevisionSet (ℕ → Bool))
  letI : TopologicalSpace (PrecisePrevision (ℕ → Bool)) := ⊥
  letI : DiscreteTopology (PrecisePrevision (ℕ → Bool)) :=
    discreteTopology_bot (PrecisePrevision (ℕ → Bool))
  have hCompact : IsCompact carrier' := by
    exact isCompact_singleton
  have hCarrierConvex : CredalPrevisionSet.IsConvex carrier' := by
    exact CredalPrevisionSet.isConvex_singleton P
  have hClosed : ∀ n, IsClosed {Q : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n Q) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)} := by
    intro n
    exact isClosed_discrete _
  have hWitness' :
      posteriorBernoulliMixturePrefixProcessCarrierWitness
        M k l hZ carrier' := by
    refine ⟨P, ?_, hPmarg⟩
    simp [carrier']
  exact
    posteriorBernoulliMixture_processLawCrown_of_prefixCarrierRealization
      M k l hZ carrier' hCompact hCarrierConvex hClosed
      (posteriorBernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_carrierWitness
        M k l hZ carrier' hWitness')

/-- Paper-facing posterior process-law package from the raw global
posterior-process witness itself.

This isolates the genuine remaining all-gambles object: if one global precise
prevision with the analytic posterior prefix marginals exists, the compact/FIP
process-law crown follows automatically. -/
theorem posteriorBernoulliMixture_processLawCrown_of_prefixWitness
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hWitness : posteriorBernoulliMixturePrefixProcessWitness M k l hZ) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ := by
  rcases hWitness with ⟨P, hPmarg⟩
  exact
    posteriorBernoulliMixture_processLawCrown_of_prefixCarrierWitness
      M k l hZ ({P} : CredalPrevisionSet (ℕ → Bool))
      ⟨P, by simp, hPmarg⟩

/-- In the zero-interior-mass regime, the raw posterior-process witness exists,
so the full raw process-law crown follows directly. -/
theorem posteriorBernoulliMixture_processLawCrown_of_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ := by
  exact
    posteriorBernoulliMixture_processLawCrown_of_prefixWitness M k l hZ
      (posteriorBernoulliMixturePrefixProcessWitness_of_zeroInteriorMixingMass
        M k l hZ hInterior)

/-- Any compatible completion of the posterior prefix-process credal spec is
already a raw global witness, because every local credal slice is the singleton
analytic posterior prefix prevision. -/
theorem posteriorBernoulliMixturePrefixProcessWitness_of_processLawCompatibleCompletion
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hComp :
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).hasCompatibleCompletion) :
    posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  rcases hComp with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  intro n X
  have hPn :
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec.localCredal n :=
    hP n
  rw [posteriorBernoulliMixturePrefixProcessLocalCredal_eq_singleton M k l hZ n] at hPn
  have hEq :
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision :=
    Set.mem_singleton_iff.mp hPn
  exact congrArg (fun R : PrecisePrevision (Fin n → Bool) => R X) hEq

/-- A raw posterior process-law crown already contains a compatible completion,
so it forces the existence of the raw global posterior-process witness. -/
theorem posteriorBernoulliMixturePrefixProcessWitness_of_processLawCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hCrown : PosteriorBernoulliMixtureProcessLawCrown M k l hZ) :
    posteriorBernoulliMixturePrefixProcessWitness M k l hZ :=
  posteriorBernoulliMixturePrefixProcessWitness_of_processLawCompatibleCompletion
    M k l hZ hCrown.processCompatibleCompletion

/-- Consequently, a raw posterior process-law crown also forces existence of a
carrier witness for the analytic posterior prefix marginals. -/
theorem posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_of_processLawCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hCrown : PosteriorBernoulliMixtureProcessLawCrown M k l hZ) :
    ∃ carrier : CredalPrevisionSet (ℕ → Bool),
      posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier := by
  exact
    (posteriorBernoulliMixturePrefixProcessWitness_iff_existsCarrierWitness
      M k l hZ).mp
      (posteriorBernoulliMixturePrefixProcessWitness_of_processLawCrown
        M k l hZ hCrown)

/-- The raw posterior process-law crown is equivalent to existence of some
carrier witness for the analytic posterior prefix marginals. -/
theorem posteriorBernoulliMixture_processLawCrown_iff_exists_prefixCarrierWitness
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ ↔
      ∃ carrier : CredalPrevisionSet (ℕ → Bool),
        posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier := by
  constructor
  · intro hCrown
    exact
      posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_of_processLawCrown
        M k l hZ hCrown
  · rintro ⟨carrier, hWitness⟩
    exact
      posteriorBernoulliMixture_processLawCrown_of_prefixCarrierWitness
        M k l hZ carrier hWitness

/-- Exact regime split for the raw posterior process-law crown itself: it
exists precisely in the zero-interior-mixing regime. -/
theorem posteriorBernoulliMixture_processLawCrown_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ ↔
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  constructor
  · intro hCrown
    exact
      (posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_iff_zeroInteriorMixingMass
        M k l hZ).mp
        ((posteriorBernoulliMixture_processLawCrown_iff_exists_prefixCarrierWitness
          M k l hZ).mp hCrown)
  · intro hInterior
    exact
      posteriorBernoulliMixture_processLawCrown_of_zeroInteriorMixingMass
        M k l hZ hInterior

/-- In the nondegenerate interior-mass regime, the stronger raw posterior
process-law crown is impossible. -/
theorem not_posteriorBernoulliMixture_processLawCrown_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    ¬ PosteriorBernoulliMixtureProcessLawCrown M k l hZ := by
  intro hCrown
  have hZero :
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 :=
    (posteriorBernoulliMixture_processLawCrown_iff_zeroInteriorMixingMass
      M k l hZ).mp hCrown
  have hNot :
      ¬ 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1) := by
    rw [hZero]
    exact lt_irrefl 0
  exact hNot hInterior

/-- Paper-facing posterior process-law package from any compact/convex/closed
raw carrier that contains the explicit tail-false finite-window realizers. -/
theorem posteriorBernoulliMixture_processLawCrown_of_prefixTailFalseExtensionCarrierSubset
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).localLower n)})
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ :=
  posteriorBernoulliMixture_processLawCrown_of_prefixCarrierRealization
    M k l hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_prefixTailFalseExtensionCarrierSubset
      M k l hZ carrier hSubset)

/-! ### Posterior external process-carrier boundary -/

/-- An external Boolean process law realizes a Bernoulli mixture when every
finite prefix prevision agrees with the analytic Bernoulli-mixture prefix
prevision.  This is the explicit sigma-additive process-carrier boundary left
after the posterior/update and finite-prefix projective crowns. -/
def BernoulliMixtureExternalProcessRealization
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (A : ExternalBoolProcessLaw Ω) : Prop :=
  ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    A.prefixPrevision n X =
      (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision X

/-- Canonical sigma-additive `Bool^ℕ` process measure for a Bernoulli mixture:
mix the internal iid `Theta ↦ Bool^ℕ` kernel against the mixture's pulled-back
`Theta` law.  This is the honest global process object supplied by the existing
Kleisli/IID infrastructure; the remaining raw-prevision gap is therefore an
extension question, not a missing global measure. -/
noncomputable def bernoulliMixtureCanonicalProcessMeasure
    (M : BernoulliMixture) : Measure (ℕ → Bool) :=
  Measure.bind
    (DeFinettiConnection.mixingMeasureTheta M)
    (fun θ : LatentTheta => iidSequenceKernelTheta θ)

instance bernoulliMixtureCanonicalProcessMeasure_isProbability
    (M : BernoulliMixture) :
    IsProbabilityMeasure (bernoulliMixtureCanonicalProcessMeasure M) := by
  unfold bernoulliMixtureCanonicalProcessMeasure
  infer_instance

private theorem bernoulliMixtureCanonical_coordProcess_measurable :
    ∀ i : ℕ, Measurable (coordProcess i) := by
  intro i
  exact measurable_pi_apply (a := i)

/-- The canonical mixed `Bool^ℕ` process measure represents the original
Bernoulli mixture on every finite prefix.  This packages the internal
`Theta → Bool^ℕ` iid kernel as a concrete global de Finetti witness on the
standard path space itself. -/
theorem bernoulliMixtureCanonicalProcessMeasure_represents
    (M : BernoulliMixture) :
    DeFinetti.Represents M coordProcess
      (bernoulliMixtureCanonicalProcessMeasure M) := by
  let ν : Measure LatentTheta := DeFinettiConnection.mixingMeasureTheta M
  let κ : ProbabilityTheory.Kernel PUnit GlobalBinarySeq :=
    ProbabilityTheory.Kernel.const PUnit (bernoulliMixtureCanonicalProcessMeasure M)
  let L : ProbabilityTheory.Kernel PUnit LatentTheta :=
    ProbabilityTheory.Kernel.const PUnit ν
  have hprefixLaw :
      ∀ (_y : PUnit) (n : ℕ) (xs : Fin n → Bool),
        κ _y (seqPrefixEvent n xs) =
          ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L _y) := by
    intro y n xs
    have hseqMeas : MeasurableSet (seqPrefixEvent n xs) := by
      simpa [seqPrefixEvent, coordProcess, cyl] using
        (DeFinetti.measurableSet_cyl coordProcess
          bernoulliMixtureCanonical_coordProcess_measurable xs)
    calc
      κ y (seqPrefixEvent n xs)
          = bernoulliMixtureCanonicalProcessMeasure M (seqPrefixEvent n xs) := by
              simp [κ, ProbabilityTheory.Kernel.const_apply]
      _ = ∫⁻ θ : LatentTheta, iidSequenceKernelTheta θ (seqPrefixEvent n xs) ∂ν := by
            exact
              Measure.bind_apply hseqMeas
                (ProbabilityTheory.Kernel.aemeasurable iidSequenceKernelTheta)
      _ = ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂ν := by
            refine lintegral_congr_ae ?_
            exact Filter.Eventually.of_forall
              (fun θ => iidSequenceKernelTheta_prefix_apply_unconditional θ n xs)
      _ = ∫⁻ θ : LatentTheta, (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y) := by
            simp [L, ν, ProbabilityTheory.Kernel.const_apply]
  have hKernelRep :
      KernelRepresentsLatentTheta
        (X := coordProcess) κ (fun y => L y) :=
    kernelRepresentsLatentTheta_of_kernelPrefixLaw_iidPrefix
      (κ := κ) (L := L) hprefixLaw
  rcases hKernelRep PUnit.unit with ⟨M', hRep', hMix'⟩
  have hMixEq :
      DeFinettiConnection.mixingMeasureTheta M' =
        DeFinettiConnection.mixingMeasureTheta M := by
    simpa [L, ν, ProbabilityTheory.Kernel.const_apply] using hMix'.symm
  have hM' : M' = M :=
    DeFinettiConnection.bernoulliMixture_ext_of_mixingMeasureTheta_eq
      M' M hMixEq
  subst hM'
  simpa [κ, bernoulliMixtureCanonicalProcessMeasure,
    ProbabilityTheory.Kernel.const_apply] using hRep'

/-- A standard de Finetti representation by singleton finite-cylinder
probabilities determines the full finite-prefix prevision surface.  This is the
non-circular bridge from the older `Represents` predicate to the projective
credal prefix adapter. -/
theorem externalPathLawPrefixPrevision_eq_bernoulliMixturePrefixPrevision_of_represents
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i))
    (M : BernoulliMixture) (hRep : DeFinetti.Represents M X μ)
    (n : ℕ) :
    externalPathLawPrefixPrevision μ X hX n =
      (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision := by
  classical
  ext Y
  unfold externalPathLawPrefixPrevision
  let path : Measure (ℕ → Bool) := Exchangeability.pathLaw (α := Bool) μ X
  haveI : IsProbabilityMeasure path := by
    dsimp [path, Exchangeability.pathLaw]
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ fun i => hX i).aemeasurable)
  let μprefix : Measure (Fin n → Bool) :=
    Measure.map (Exchangeability.prefixProj (α := Bool) n) path
  haveI : IsProbabilityMeasure μprefix :=
    Measure.isProbabilityMeasure_map
      ((Exchangeability.measurable_prefixProj (α := Bool) (n := n)).aemeasurable)
  have hprefix :
      μprefix = Measure.map (fun ω => fun i : Fin n => X i.val ω) μ := by
    dsimp [μprefix, path]
    exact externalPathLawPrefixMeasure_eq_processPrefix μ X hX n
  rw [PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_apply]
  rw [BernoulliMixturePrefixLaw.toPrecisePrevision_apply]
  apply Finset.sum_congr rfl
  intro xs _hxs
  have hsingleton :
      μprefix ({xs} : Set (Fin n → Bool)) =
        μ {ω | ∀ i : Fin n, X i.val ω = xs i} := by
    rw [hprefix]
    rw [Measure.map_apply
      (measurable_pi_lambda _ fun i : Fin n => hX i.val)
      (measurableSet_singleton xs)]
    congr 1
    ext ω
    simp [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
  rw [hsingleton, hRep n xs, ENNReal.toReal_ofReal]
  exact DeFinettiConnection.bernoulliMixture_prob_nonneg M n xs

/-- Canonical external-process realization from a represented measurable
Boolean process.  This replaces the raw all-prefix realization assumption by
the standard singleton-cylinder representation predicate whenever such a
process model is available. -/
theorem externalBoolProcessLawOf_realizes_bernoulliMixture_of_represents
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i))
    (M : BernoulliMixture) (hRep : DeFinetti.Represents M X μ) :
    BernoulliMixtureExternalProcessRealization M
      (ExternalBoolProcessLaw.ofProcess μ X hX) := by
  intro n Y
  simpa [ExternalBoolProcessLaw.ofProcess, ExternalBoolProcessLaw.prefixPrevision]
    using congrArg (fun P : PrecisePrevision (Fin n → Bool) => P Y)
      (externalPathLawPrefixPrevision_eq_bernoulliMixturePrefixPrevision_of_represents
        μ X hX M hRep n)

/-- Posterior specialization: a represented posterior Bernoulli mixture
canonically supplies the external realization consumed by the posterior
external-carrier crown. -/
theorem externalBoolProcessLawOf_realizes_posteriorBernoulliMixture_of_represents
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i))
    (hRep : DeFinetti.Represents (M.posteriorBernoulliMixture k l hZ) X μ) :
    BernoulliMixtureExternalProcessRealization
      (M.posteriorBernoulliMixture k l hZ)
      (ExternalBoolProcessLaw.ofProcess μ X hX) :=
  externalBoolProcessLawOf_realizes_bernoulliMixture_of_represents
    μ X hX (M.posteriorBernoulliMixture k l hZ) hRep

/-- The canonical external Boolean process law on `Bool^ℕ` carried by a
Bernoulli mixture. -/
noncomputable def bernoulliMixtureCanonicalExternalBoolProcessLaw
    (M : BernoulliMixture) :
    ExternalBoolProcessLaw (ℕ → Bool) :=
  ExternalBoolProcessLaw.ofProcess
    (bernoulliMixtureCanonicalProcessMeasure M)
    coordProcess
    bernoulliMixtureCanonical_coordProcess_measurable

/-- The canonical mixed `Bool^ℕ` process measure directly supplies the external
realization predicate for a Bernoulli mixture. -/
theorem bernoulliMixtureCanonicalExternalProcessRealization
    (M : BernoulliMixture) :
    BernoulliMixtureExternalProcessRealization M
      (bernoulliMixtureCanonicalExternalBoolProcessLaw M) := by
  exact externalBoolProcessLawOf_realizes_bernoulliMixture_of_represents
    (bernoulliMixtureCanonicalProcessMeasure M)
    coordProcess
    bernoulliMixtureCanonical_coordProcess_measurable
    M
    (bernoulliMixtureCanonicalProcessMeasure_represents M)

/-- The family of canonical external `Bool^ℕ` process laws generated by a set
of Bernoulli mixtures. -/
def bernoulliMixtureCanonicalExternalBoolProcessLawSet
    (C : Set BernoulliMixture) :
    Set (ExternalBoolProcessLaw (ℕ → Bool)) :=
  {A | ∃ M : BernoulliMixture, M ∈ C ∧
    A = bernoulliMixtureCanonicalExternalBoolProcessLaw M}

theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty
    (C : Set BernoulliMixture) (hC : C.Nonempty) :
    (bernoulliMixtureCanonicalExternalBoolProcessLawSet C).Nonempty := by
  rcases hC with ⟨M, hM⟩
  exact ⟨bernoulliMixtureCanonicalExternalBoolProcessLaw M, M, hM, rfl⟩

/-- At each finite prefix, the canonical external-process realization of a
Bernoulli-mixture credal set induces exactly the same precise-prevision carrier
as the analytic imprecise de Finetti prefix family. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (n : ℕ) :
    externalPathLawPrefixCredalSet
        (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n =
      bernoulliMixturePrefixCredalSet C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) := by
  ext P
  constructor
  · rintro ⟨A, hA, hP⟩
    rcases hA with ⟨M, hM, rfl⟩
    refine ⟨M, hM, ?_⟩
    calc
      P = (bernoulliMixtureCanonicalExternalBoolProcessLaw M).prefixPrevision n := hP
      _ = (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision := by
        ext X
        exact bernoulliMixtureCanonicalExternalProcessRealization M n X
  · rintro ⟨M, hM, hP⟩
    refine ⟨bernoulliMixtureCanonicalExternalBoolProcessLaw M, ?_, ?_⟩
    · exact ⟨M, hM, rfl⟩
    · calc
        P = (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision := hP
        _ = (bernoulliMixtureCanonicalExternalBoolProcessLaw M).prefixPrevision n := by
          ext X
          symm
          exact bernoulliMixtureCanonicalExternalProcessRealization M n X

/-- The canonical external process-law family of a Bernoulli-mixture credal
set computes exactly the same finite-prefix lower envelope as the imprecise de
Finetti family itself. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixLowerEnvelope_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (_hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixLowerEnvelope
        (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n X =
      impreciseDeFinettiPrefixLowerEnvelope C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X := by
  unfold externalPathLawPrefixLowerEnvelope
    impreciseDeFinettiPrefixLowerEnvelope
  rw [
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
      C n]

/-- The canonical external process-law family of a Bernoulli-mixture credal
set computes exactly the same finite-prefix upper envelope as the imprecise de
Finetti family itself. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixUpperEnvelope_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (_hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixUpperEnvelope
        (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n X =
      impreciseDeFinettiPrefixUpperEnvelope C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X := by
  unfold externalPathLawPrefixUpperEnvelope
    impreciseDeFinettiPrefixUpperEnvelope
  rw [
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
      C n]

/-- The canonical external process-law family of a Bernoulli-mixture credal
set computes exactly the same finite-prefix width-complement confidence
coordinate as the imprecise de Finetti family itself. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixWidthComplement_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (_hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixEnvelopeWidthComplement
        (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n X =
      impreciseDeFinettiPrefixEnvelopeWidthComplement C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X := by
  unfold externalPathLawPrefixEnvelopeWidthComplement
    impreciseDeFinettiPrefixEnvelopeWidthComplement
    credalEnvelopeWidthComplement credalEnvelopeWidth
  rw [
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
      C n]

/-- The canonical external process-law family of a Bernoulli-mixture credal
set computes exactly the same finite-prefix midpoint strength coordinate as the
imprecise de Finetti family itself. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixMidpoint_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (_hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixEnvelopeMidpoint
        (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n X =
      impreciseDeFinettiPrefixEnvelopeMidpoint C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X := by
  unfold externalPathLawPrefixEnvelopeMidpoint
    impreciseDeFinettiPrefixEnvelopeMidpoint
    credalEnvelopeMidpoint
  rw [
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
      C n]

/-- The compact bounded-measurable canonical external path-law carrier of a
Bernoulli-mixture credal set computes the same finite-prefix lower envelope as
the imprecise de Finetti family itself. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactNaturalExtension_prefix_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C))
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C)
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC))
        (externalPathLawPrefixBoundedMeasurableGamble n X) =
      impreciseDeFinettiPrefixLowerEnvelope C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X := by
  rw [
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
      (bernoulliMixtureCanonicalExternalBoolProcessLawSet C)
      (bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC) n X,
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixLowerEnvelope_eq_impreciseDeFinetti
      C hC n X]

/-- The compact bounded-measurable canonical external path-law carrier of a
Bernoulli-mixture credal set computes the same finite-prefix upper envelope as
the imprecise de Finetti family itself. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactNaturalUpperEnvelope_prefix_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCompactCredalSet
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C))
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C)
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC))
        (externalPathLawPrefixBoundedMeasurableGamble n X) =
      impreciseDeFinettiPrefixUpperEnvelope C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X := by
  rw [
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
      (bernoulliMixtureCanonicalExternalBoolProcessLawSet C)
      (bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC) n X,
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixUpperEnvelope_eq_impreciseDeFinetti
      C hC n X]

/-- The compact bounded-measurable canonical external path-law carrier of a
Bernoulli-mixture credal set computes the same finite-prefix width-complement
confidence coordinate as the imprecise de Finetti family itself. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactWidthComplement_prefix_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C))
        (externalPathLawPrefixBoundedMeasurableGamble n X) =
      impreciseDeFinettiPrefixEnvelopeWidthComplement C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
      (bernoulliMixtureCanonicalExternalBoolProcessLawSet C)
      (bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC) n X,
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixWidthComplement_eq_impreciseDeFinetti
      C hC n X]

/-- The compact bounded-measurable canonical external path-law carrier of a
Bernoulli-mixture credal set computes the same finite-prefix midpoint strength
coordinate as the imprecise de Finetti family itself. -/
theorem bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactMidpoint_prefix_eq_impreciseDeFinetti
    (C : Set BernoulliMixture) (hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C))
        (externalPathLawPrefixBoundedMeasurableGamble n X) =
      impreciseDeFinettiPrefixEnvelopeMidpoint C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X := by
  rw [
    boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_finitePrefixMidpoint
      (bernoulliMixtureCanonicalExternalBoolProcessLawSet C)
      (bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC) n X,
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixMidpoint_eq_impreciseDeFinetti
      C hC n X]

/-- Public sigma-additive mixing-family package for an imprecise de Finetti
credal set.

Positive example: it gives an actual external `Bool^ℕ` family whose finite-
prefix and compact bounded-measurable lower/upper/width-complement/midpoint
readouts agree exactly with the analytic Bernoulli-mixture family.

Negative example: it does not claim a raw all-gambles compatible completion or
process-law crown; those remain separate theorems. -/
structure ImpreciseDeFinettiCanonicalExternalMixingFamily
    (C : Set BernoulliMixture) (hC : C.Nonempty) : Prop where
  nonempty :
    (bernoulliMixtureCanonicalExternalBoolProcessLawSet C).Nonempty
  prefixProjectiveCompatibleCompletion :
    ∀ n : ℕ,
      (bernoulliMixturePrefixProjectiveSpec C n
        (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).hasCompatibleCompletion
  prefixCredalSet_eq_impreciseDeFinetti :
    ∀ n : ℕ,
      externalPathLawPrefixCredalSet
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n =
        bernoulliMixturePrefixCredalSet C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n)
  prefixLowerEnvelope_eq_impreciseDeFinetti :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      externalPathLawPrefixLowerEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n X =
        impreciseDeFinettiPrefixLowerEnvelope C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  prefixUpperEnvelope_eq_impreciseDeFinetti :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      externalPathLawPrefixUpperEnvelope
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n X =
        impreciseDeFinettiPrefixUpperEnvelope C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  prefixWidthComplement_eq_impreciseDeFinetti :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      externalPathLawPrefixEnvelopeWidthComplement
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n X =
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  prefixMidpoint_eq_impreciseDeFinetti :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      externalPathLawPrefixEnvelopeMidpoint
          (bernoulliMixtureCanonicalExternalBoolProcessLawSet C) n X =
        impreciseDeFinettiPrefixEnvelopeMidpoint C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  compactNaturalExtension_prefix_eq_impreciseDeFinetti :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableNaturalExtensionPrevision
          (externalPathLawBoundedMeasurableCompactCredalSet
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C))
          (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C)
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC))
          (externalPathLawPrefixBoundedMeasurableGamble n X) =
        impreciseDeFinettiPrefixLowerEnvelope C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  compactNaturalUpperEnvelope_prefix_eq_impreciseDeFinetti :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableNaturalUpperEnvelopePrevision
          (externalPathLawBoundedMeasurableCompactCredalSet
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C))
          (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C)
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC))
          (externalPathLawPrefixBoundedMeasurableGamble n X) =
        impreciseDeFinettiPrefixUpperEnvelope C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  compactWidthComplement_prefix_eq_impreciseDeFinetti :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableEnvelopeWidthComplement
          (externalPathLawBoundedMeasurableCompactCredalSet
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C))
          (externalPathLawPrefixBoundedMeasurableGamble n X) =
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  compactMidpoint_prefix_eq_impreciseDeFinetti :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableEnvelopeMidpoint
          (externalPathLawBoundedMeasurableCompactCredalSet
            (bernoulliMixtureCanonicalExternalBoolProcessLawSet C))
          (externalPathLawPrefixBoundedMeasurableGamble n X) =
        impreciseDeFinettiPrefixEnvelopeMidpoint C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  agreementDetermines :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ _hN : N ∈ C,
          (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision X =
            (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision X) →
        (bernoulliMixturePrefixProjectiveSpec C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).determinesGlobalGamble X
  agreementWidthComplement_eq_one :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ _hN : N ∈ C,
          (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision X =
            (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision X) →
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X = 1
  disagreementStrictWidth :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision X <
        (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision X →
        (bernoulliMixturePrefixProjectiveSpec C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n)).hasStrictGlobalWidth X
  disagreementEnvelopeWidth_pos :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision X <
        (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision X →
        0 < impreciseDeFinettiPrefixEnvelopeWidth C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X
  disagreementWidthComplement_lt_one :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision X <
        (bernoulliMixturePrefixLaw_analytic N n).toPrecisePrevision X →
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n
          (fun M _ => bernoulliMixturePrefixLaw_analytic M n) X < 1

/-- The canonical external `Bool^ℕ` Bernoulli-mixture family is the clean
public sigma-additive mixing-family object for the imprecise de Finetti
finite-prefix and compact bounded-measurable readouts. -/
theorem impreciseDeFinetti_canonicalExternalMixingFamily
    (C : Set BernoulliMixture) (hC : C.Nonempty) :
    ImpreciseDeFinettiCanonicalExternalMixingFamily C hC where
  nonempty :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_nonempty C hC
  prefixProjectiveCompatibleCompletion := by
    intro n
    exact bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
      C n (fun M _ => bernoulliMixturePrefixLaw_analytic M n) hC
  prefixCredalSet_eq_impreciseDeFinetti := by
    intro n
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
        C n
  prefixLowerEnvelope_eq_impreciseDeFinetti := by
    intro n X
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixLowerEnvelope_eq_impreciseDeFinetti
        C hC n X
  prefixUpperEnvelope_eq_impreciseDeFinetti := by
    intro n X
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixUpperEnvelope_eq_impreciseDeFinetti
        C hC n X
  prefixWidthComplement_eq_impreciseDeFinetti := by
    intro n X
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixWidthComplement_eq_impreciseDeFinetti
        C hC n X
  prefixMidpoint_eq_impreciseDeFinetti := by
    intro n X
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixMidpoint_eq_impreciseDeFinetti
        C hC n X
  compactNaturalExtension_prefix_eq_impreciseDeFinetti := by
    intro n X
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactNaturalExtension_prefix_eq_impreciseDeFinetti
        C hC n X
  compactNaturalUpperEnvelope_prefix_eq_impreciseDeFinetti := by
    intro n X
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactNaturalUpperEnvelope_prefix_eq_impreciseDeFinetti
        C hC n X
  compactWidthComplement_prefix_eq_impreciseDeFinetti := by
    intro n X
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactWidthComplement_prefix_eq_impreciseDeFinetti
        C hC n X
  compactMidpoint_prefix_eq_impreciseDeFinetti := by
    intro n X
    exact
      bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactMidpoint_prefix_eq_impreciseDeFinetti
        C hC n X
  agreementDetermines := by
    intro n X hAgree
    exact
      impreciseDeFinetti_prefixAgreement_projectiveDetermines
        C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) n X hAgree
  agreementWidthComplement_eq_one := by
    intro n X hAgree
    exact
      impreciseDeFinetti_prefixAgreement_confidence_eq_one
        C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC n X hAgree
  disagreementStrictWidth := by
    intro n X M N hM hN hlt
    exact
      impreciseDeFinetti_prefixDisagreement_strictWidth
        C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) n X hM hN hlt
  disagreementEnvelopeWidth_pos := by
    intro n X M N hM hN hlt
    exact
      impreciseDeFinetti_prefixDisagreement_envelopeWidth_pos
        C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) n X hM hN hlt
  disagreementWidthComplement_lt_one := by
    intro n X M N hM hN hlt
    exact
      impreciseDeFinetti_prefixDisagreement_confidence_lt_one
        C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) n X hM hN hlt

/-- Public analytic infinite de Finetti package at the current honest
process-law boundary.

Positive example: it records both the canonical sigma-additive `Bool^ℕ`
mixing-family object and the raw all-gambles process-law crown.

Negative example: it does not remove the remaining compact carrier/FIP
hypothesis boundary; this package sits exactly at that boundary rather than
hiding it. -/
structure ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
    (C : Set BernoulliMixture) (hC : C.Nonempty) : Prop where
  canonicalExternalMixingFamily :
    ImpreciseDeFinettiCanonicalExternalMixingFamily C hC
  processLawCrown :
    ImpreciseDeFinettiProcessLawCrown
      C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC

/-- Singleton specialization bridge for the analytic family-level crown.

This is the S0a guardrail for F2: if the raw all-gambles analytic crown is
claimed for the posterior singleton family, it really yields the existing
posterior-specific raw process-law crown.  Thus any later refutation of an
unconditional family-level raw crown can pass through the already-proved
posterior zero-interior-mass dichotomy. -/
theorem posteriorBernoulliMixture_processLawCrown_of_singletonAnalyticMixingFamilyCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hCrown :
      ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
        (posteriorBernoulliMixtureSet M k l hZ)
        (posteriorBernoulliMixtureSet_nonempty M k l hZ)) :
    PosteriorBernoulliMixtureProcessLawCrown M k l hZ where
  prefixProjectiveCrown :=
    posteriorBernoulliMixturePrefixProjectiveCrown M k l hZ
  processLawCrown := by
    simpa [posteriorBernoulliMixtureSetPrefixLaw] using hCrown.processLawCrown
  processCompatibleCompletion := by
    simpa [posteriorBernoulliMixturePrefixProcessLowerSpec,
      posteriorBernoulliMixtureSetPrefixLaw] using
      hCrown.processLawCrown.processCompatibleCompletion
  prefixEnvelopeWidth_eq_zero := by
    intro n X
    exact posteriorBernoulliMixturePrefixEnvelopeWidth_eq_zero M k l hZ n X
  prefixWidthComplement_eq_one := by
    intro n X
    exact posteriorBernoulliMixturePrefixEnvelopeWidthComplement_eq_one M k l hZ n X

/-- A positive-interior posterior singleton refutes any unconditional raw analytic
family-level crown for all nonempty credal sets.

This is the F2 guardrail: the canonical external mixing readout is unconditional,
but the raw all-gambles process-law crown is not. -/
theorem not_forall_impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    ¬ (∀ (C : Set BernoulliMixture) (hC : C.Nonempty),
        ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC) := by
  intro hAll
  have hZ : M.countEvidenceMass k l ≠ 0 := by
    exact ne_of_gt
      (BernoulliMixture.countEvidenceMass_pos_of_interiorMass M k l hInterior)
  have hSingleton :
      ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
        (posteriorBernoulliMixtureSet M k l hZ)
        (posteriorBernoulliMixtureSet_nonempty M k l hZ) :=
    hAll (posteriorBernoulliMixtureSet M k l hZ)
      (posteriorBernoulliMixtureSet_nonempty M k l hZ)
  have hPosterior :
      PosteriorBernoulliMixtureProcessLawCrown M k l hZ :=
    posteriorBernoulliMixture_processLawCrown_of_singletonAnalyticMixingFamilyCrown
      M k l hZ hSingleton
  exact
    not_posteriorBernoulliMixture_processLawCrown_of_interiorMixingMass
      M k l hZ hInterior hPosterior

/-- The neutral analytic compatibility condition for the F2 family-level raw
process-law crown.

Positive example: a proven analytic mixing-family process-law crown projects to
this condition.  Negative example: the positive-interior posterior singleton
refutation above shows that no theorem can supply this condition for every
nonempty credal family. -/
def AnalyticMixingFamilyRawProcessCompatible
    (C : Set BernoulliMixture) (hC : C.Nonempty) : Prop :=
  ImpreciseDeFinettiRawProcessCompatible C
    (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC

/-- Candidate pointwise zero-interior condition for the analytic family-level
raw process-law crown.

Positive example: a singleton family satisfies this condition exactly when its
one member has zero interior mixing mass.  Negative example: any member with
positive interior mixing mass refutes the condition. -/
def AnalyticMixingFamilyPointwiseZeroInterior
    (C : Set BernoulliMixture) : Prop :=
  ∀ M : BernoulliMixture, M ∈ C →
    M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0

/-- A single Bernoulli mixture has an all-gambles analytic prefix-process
witness when one precise prevision on infinite Boolean paths has exactly its
analytic finite-prefix marginals.

Positive example: the posterior zero-interior theorem proves this shape for
posterior singleton laws.  Negative example: the posterior interior-mass
dichotomy refutes this shape in the corresponding positive-interior posterior
case. -/
def BernoulliMixtureAnalyticPrefixProcessWitness
    (M : BernoulliMixture) : Prop :=
  ∃ P : PrecisePrevision (ℕ → Bool),
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n P) X =
        (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision X

/-- A zero-interior Bernoulli mixture has a raw all-gambles analytic prefix-process
witness: the infinite process is the two-point mixture of the all-true and
all-false paths, with weight determined by the one-bit true prefix. -/
theorem BernoulliMixtureAnalyticPrefixProcessWitness_of_zeroInteriorMixingMass
    (M : BernoulliMixture)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    BernoulliMixtureAnalyticPrefixProcessWitness M := by
  classical
  let t : ℝ :=
    (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
      oneBitTrueGamble
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact
      ((bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision).lower_bound
        oneBitTrueGamble 0 (by
          intro xs
          simpa [oneBitTrueGamble] using
            (PrecisePrevision.FiniteWeights.atomGamble_nonneg oneBitTruePrefix xs))
  have hFalseNonneg :
      0 ≤
        (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
          oneBitFalseGamble := by
    exact
      ((bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision).lower_bound
        oneBitFalseGamble 0 (by
          intro xs
          simpa [oneBitFalseGamble] using
            (PrecisePrevision.FiniteWeights.atomGamble_nonneg oneBitFalsePrefix xs))
  have hSum :
      t +
        (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
          oneBitFalseGamble = 1 := by
    simpa [t] using
      bernoulliMixture_oneBitPrefixPrevision_true_add_false M
  have ht1 : t ≤ 1 := by
    linarith
  let P : PrecisePrevision (ℕ → Bool) :=
    PrecisePrevision.mix t
      (PrecisePrevision.dirac allTruePath)
      (PrecisePrevision.dirac allFalsePath)
      ht0 ht1
  refine ⟨P, ?_⟩
  intro n X
  have hMarginalTrue :
      bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n
        (PrecisePrevision.dirac allTruePath) =
        PrecisePrevision.dirac (allTruePrefix n) := by
    ext Y
    rfl
  have hMarginalFalse :
      bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n
        (PrecisePrevision.dirac allFalsePath) =
        PrecisePrevision.dirac (allFalsePrefix n) := by
    ext Y
    rfl
  have hMarginalMix :
      bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n P =
        PrecisePrevision.mix t
          (PrecisePrevision.dirac (allTruePrefix n))
          (PrecisePrevision.dirac (allFalsePrefix n))
          ht0 ht1 := by
    change
      bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n P =
        PrecisePrevision.mix t
          (PrecisePrevision.dirac (allTruePrefix n))
          (PrecisePrevision.dirac (allFalsePrefix n))
          ht0 ht1
    rw [ProjectiveCylinderSystem.marginalPrevision_mix]
    rw [hMarginalTrue, hMarginalFalse]
    rfl
  have hLocalEq :
      bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision n P =
        (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision := by
    cases n with
    | zero =>
        have hWeights :
            PrecisePrevision.FiniteWeights.ofPrecisePrevision
              (Ω := Fin 0 → Bool)
              (bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision 0 P) =
              PrecisePrevision.FiniteWeights.ofPrecisePrevision
                (Ω := Fin 0 → Bool)
                ((bernoulliMixturePrefixLaw_analytic M 0).toPrecisePrevision) := by
          ext xs
          have hxs : xs = default := by
            ext i
            exact Fin.elim0 i
          subst hxs
          rw [PrecisePrevision.FiniteWeights.ofPrecisePrevision_weight,
            PrecisePrevision.FiniteWeights.ofPrecisePrevision_weight]
          rw [hMarginalMix]
          have hTrue0 : allTruePrefix 0 = (default : Fin 0 → Bool) := by
            ext i
            exact Fin.elim0 i
          have hFalse0 : allFalsePrefix 0 = (default : Fin 0 → Bool) := by
            ext i
            exact Fin.elim0 i
          have hLeft :
              (PrecisePrevision.mix t
                  (PrecisePrevision.dirac (allTruePrefix 0))
                  (PrecisePrevision.dirac (allFalsePrefix 0)) ht0 ht1)
                (PrecisePrevision.FiniteWeights.atomGamble (default : Fin 0 → Bool)) = 1 := by
            simp [PrecisePrevision.mix, PrecisePrevision.FiniteWeights.atomGamble, t,
              hTrue0, hFalse0]
          have hTotal :=
            (bernoulliMixturePrefixLaw_analytic M 0).total
          have hRight :
              (bernoulliMixturePrefixLaw_analytic M 0).toPrecisePrevision
                (PrecisePrevision.FiniteWeights.atomGamble (default : Fin 0 → Bool)) = 1 := by
            simp only [BernoulliMixturePrefixLaw.toPrecisePrevision_atomGamble]
            rw [Fintype.sum_unique] at hTotal
            exact hTotal
          exact hLeft.trans hRight.symm
        have hPrec := congrArg PrecisePrevision.FiniteWeights.toPrecisePrevision hWeights
        rw [PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision,
          PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision] at hPrec
        exact hPrec
    | succ m =>
        have hWeights :
            PrecisePrevision.FiniteWeights.ofPrecisePrevision
              (Ω := Fin (Nat.succ m) → Bool)
              (bernoulliMixturePrefixProcessCylinderSystem.marginalPrevision (Nat.succ m) P) =
              PrecisePrevision.FiniteWeights.ofPrecisePrevision
                (Ω := Fin (Nat.succ m) → Bool)
                ((bernoulliMixturePrefixLaw_analytic M (Nat.succ m)).toPrecisePrevision) := by
          ext xs
          rw [PrecisePrevision.FiniteWeights.ofPrecisePrevision_weight,
            PrecisePrevision.FiniteWeights.ofPrecisePrevision_weight]
          rw [hMarginalMix]
          by_cases hEqTrue : xs = allTruePrefix (Nat.succ m)
          · have hEqFalse : xs ≠ allFalsePrefix (Nat.succ m) := by
              intro hEqFalse'
              exact
                allTruePrefix_ne_allFalsePrefix (Nat.succ_pos m)
                  (hEqTrue.symm.trans hEqFalse')
            subst hEqTrue
            have hEqFalse' : allFalsePrefix (Nat.succ m) ≠ allTruePrefix (Nat.succ m) := by
              intro h
              exact hEqFalse h.symm
            have hLeft :
                (PrecisePrevision.mix t
                    (PrecisePrevision.dirac (allTruePrefix (Nat.succ m)))
                    (PrecisePrevision.dirac (allFalsePrefix (Nat.succ m))) ht0 ht1)
                  (PrecisePrevision.FiniteWeights.atomGamble (allTruePrefix (Nat.succ m))) = t := by
              simp [PrecisePrevision.mix, PrecisePrevision.FiniteWeights.atomGamble,
                hEqFalse', t]
            have hRight :
                (bernoulliMixturePrefixLaw_analytic M (Nat.succ m)).toPrecisePrevision
                  (PrecisePrevision.FiniteWeights.atomGamble (allTruePrefix (Nat.succ m))) = t := by
              simpa [t] using
                bernoulliMixture_allTruePrefixPrevision_eq_oneBitTrue_of_zeroInteriorMixingMass
                  M (Nat.succ m) (Nat.succ_pos m) hInterior
            exact hLeft.trans hRight.symm
          · by_cases hEqFalse : xs = allFalsePrefix (Nat.succ m)
            · subst hEqFalse
              have hEqTrue' : allTruePrefix (Nat.succ m) ≠ allFalsePrefix (Nat.succ m) := by
                intro h
                exact hEqTrue h.symm
              have hLeft :
                  (PrecisePrevision.mix t
                      (PrecisePrevision.dirac (allTruePrefix (Nat.succ m)))
                      (PrecisePrevision.dirac (allFalsePrefix (Nat.succ m))) ht0 ht1)
                    (PrecisePrevision.FiniteWeights.atomGamble (allFalsePrefix (Nat.succ m))) =
                    1 - t := by
                simp [PrecisePrevision.mix, PrecisePrevision.FiniteWeights.atomGamble,
                  hEqTrue', t]
              have hOneBitFalse :
                  (bernoulliMixturePrefixLaw_analytic M (Nat.succ m)).toPrecisePrevision
                    (PrecisePrevision.FiniteWeights.atomGamble (allFalsePrefix (Nat.succ m))) =
                    (bernoulliMixturePrefixLaw_analytic M 1).toPrecisePrevision
                      oneBitFalseGamble :=
                bernoulliMixture_allFalsePrefixPrevision_eq_oneBitFalse_of_zeroInteriorMixingMass
                  M (Nat.succ m) (Nat.succ_pos m) hInterior
              have hRight :
                  (bernoulliMixturePrefixLaw_analytic M (Nat.succ m)).toPrecisePrevision
                    (PrecisePrevision.FiniteWeights.atomGamble (allFalsePrefix (Nat.succ m))) =
                    1 - t := by
                linarith [hSum, hOneBitFalse]
              exact hLeft.trans hRight.symm
            · have hCountTruePos :
                  0 < Mettapedia.Logic.Exchangeability.countTrue xs := by
                by_contra hNotPos
                have hZero : Mettapedia.Logic.Exchangeability.countTrue xs = 0 :=
                  Nat.eq_zero_of_not_pos hNotPos
                exact hEqFalse (eq_allFalsePrefix_of_countTrue_eq_zero hZero)
              have hCountFalsePos :
                  0 < Mettapedia.Logic.Exchangeability.countFalse xs := by
                by_contra hNotPos
                have hZero : Mettapedia.Logic.Exchangeability.countFalse xs = 0 :=
                  Nat.eq_zero_of_not_pos hNotPos
                exact hEqTrue (eq_allTruePrefix_of_countFalse_eq_zero hZero)
              have hEqTrue' : allTruePrefix (Nat.succ m) ≠ xs := by
                intro h
                exact hEqTrue h.symm
              have hEqFalse' : allFalsePrefix (Nat.succ m) ≠ xs := by
                intro h
                exact hEqFalse h.symm
              have hLeft :
                  (PrecisePrevision.mix t
                      (PrecisePrevision.dirac (allTruePrefix (Nat.succ m)))
                      (PrecisePrevision.dirac (allFalsePrefix (Nat.succ m))) ht0 ht1)
                    (PrecisePrevision.FiniteWeights.atomGamble xs) = 0 := by
                simp [PrecisePrevision.mix, PrecisePrevision.FiniteWeights.atomGamble,
                  hEqTrue', hEqFalse', t]
              have hRight :
                  (bernoulliMixturePrefixLaw_analytic M (Nat.succ m)).toPrecisePrevision
                    (PrecisePrevision.FiniteWeights.atomGamble xs) = 0 := by
                exact
                  bernoulliMixture_prefixAtom_eq_zero_of_zeroInteriorMixingMass_of_countTrue_pos_of_countFalse_pos
                    M xs hCountTruePos hCountFalsePos hInterior
              exact hLeft.trans hRight.symm
        have hPrec := congrArg PrecisePrevision.FiniteWeights.toPrecisePrevision hWeights
        rw [PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision,
          PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision] at hPrec
        exact hPrec
  exact congrArg (fun Q => Q X) hLocalEq

/-- Neutral discovered sufficient condition for the analytic family-level raw
process-law crown: at least one admissible mixture already has an all-gambles
analytic prefix-process witness.

This is intentionally weaker than pointwise zero-interior.  Because the family
uses a lower envelope, a single compatible member is enough to dominate all
local lower assessments. -/
def AnalyticMixingFamilyHasCompatibleMember
    (C : Set BernoulliMixture) : Prop :=
  ∃ M : BernoulliMixture, M ∈ C ∧
    BernoulliMixtureAnalyticPrefixProcessWitness M

/-- A concrete sufficient condition for the discovered compatible-member
condition: the credal family contains at least one zero-interior mixture. -/
def AnalyticMixingFamilyHasZeroInteriorMember
    (C : Set BernoulliMixture) : Prop :=
  ∃ M : BernoulliMixture, M ∈ C ∧
    M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0

/-- The family contains at least one positive-interior mixture.  This is the
minimal witness that pointwise zero-interior fails. -/
def AnalyticMixingFamilyHasPositiveInteriorMember
    (C : Set BernoulliMixture) : Prop :=
  ∃ M : BernoulliMixture, M ∈ C ∧
    0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)

/-- A point mass at a Bernoulli parameter inside `[0,1]`, packaged as a
Bernoulli mixture. -/
noncomputable def bernoulliMixtureDiracOnUnit
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) : BernoulliMixture where
  mixingMeasure := Measure.dirac θ
  isProbability := by infer_instance
  support_unit := by
    simp [hθ]

/-- The zero-endpoint Dirac Bernoulli mixture. -/
noncomputable def bernoulliMixtureDiracZero : BernoulliMixture :=
  bernoulliMixtureDiracOnUnit 0 (by norm_num)

/-- The midpoint Dirac Bernoulli mixture. -/
noncomputable def bernoulliMixtureDiracHalf : BernoulliMixture :=
  bernoulliMixtureDiracOnUnit (1 / 2 : ℝ) (by norm_num)

theorem bernoulliMixtureDiracZero_zeroInterior :
    bernoulliMixtureDiracZero.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  simp [bernoulliMixtureDiracZero, bernoulliMixtureDiracOnUnit]

theorem bernoulliMixtureDiracHalf_positiveInterior :
    0 < bernoulliMixtureDiracHalf.mixingMeasure (Set.Ioo (0 : ℝ) 1) := by
  change 0 < (Measure.dirac (1 / 2 : ℝ)) (Set.Ioo (0 : ℝ) 1)
  rw [Measure.dirac_apply]
  rw [Set.indicator_of_mem]
  · norm_num
  · norm_num

/-- A two-member analytic family witnessing that pointwise zero-interior is not
necessary for the family-level raw crown: one member is endpoint-supported, the
other has positive interior mass. -/
noncomputable def analyticMixingFamilyPointwiseNecessityCounterexample :
    Set BernoulliMixture :=
  {bernoulliMixtureDiracZero, bernoulliMixtureDiracHalf}

/-- A concrete no-go condition for raw compatibility: the analytic lower
envelope gives every first-true cylinder a strictly positive lower mass. -/
noncomputable def AnalyticMixingFamilyPositiveFirstTrueLowerEnvelope
    (C : Set BernoulliMixture) : Prop :=
  ∀ n : ℕ,
    0 <
      impreciseDeFinettiPrefixLowerEnvelope C (n + 1)
        (bernoulliMixturePrefixLawAt C
          (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) (n + 1))
        (firstTruePrefixGamble n)

/-- A singleton analytic family has the pointwise-zero condition exactly when
its single member has zero interior mixing mass. -/
theorem AnalyticMixingFamilyPointwiseZeroInterior_singleton_iff
    (M : BernoulliMixture) :
    AnalyticMixingFamilyPointwiseZeroInterior ({M} : Set BernoulliMixture) ↔
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  constructor
  · intro hZero
    exact hZero M (by simp)
  · intro hZero N hN
    have hNM : N = M := by simpa using hN
    subst hNM
    exact hZero

/-- A positive-interior member refutes the candidate pointwise-zero condition. -/
theorem not_AnalyticMixingFamilyPointwiseZeroInterior_of_mem_interiorMixingMass
    (C : Set BernoulliMixture) {M : BernoulliMixture}
    (hM : M ∈ C)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    ¬ AnalyticMixingFamilyPointwiseZeroInterior C := by
  intro hZero
  have hMZero : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := hZero M hM
  rw [hMZero] at hInterior
  exact (lt_irrefl (0 : ENNReal)) hInterior

/-- A positive-interior member refutes the pointwise-zero candidate condition. -/
theorem not_AnalyticMixingFamilyPointwiseZeroInterior_of_hasPositiveInteriorMember
    (C : Set BernoulliMixture)
    (hPositiveMember : AnalyticMixingFamilyHasPositiveInteriorMember C) :
    ¬ AnalyticMixingFamilyPointwiseZeroInterior C := by
  rcases hPositiveMember with ⟨M, hM, hInterior⟩
  exact
    not_AnalyticMixingFamilyPointwiseZeroInterior_of_mem_interiorMixingMass
      C hM hInterior

/-- A zero-interior member supplies the discovered compatible-member condition. -/
theorem AnalyticMixingFamilyHasCompatibleMember_of_hasZeroInteriorMember
    (C : Set BernoulliMixture)
    (hZeroMember : AnalyticMixingFamilyHasZeroInteriorMember C) :
    AnalyticMixingFamilyHasCompatibleMember C := by
  rcases hZeroMember with ⟨M, hM, hZero⟩
  exact
    ⟨M, hM,
      BernoulliMixtureAnalyticPrefixProcessWitness_of_zeroInteriorMixingMass M hZero⟩

/-- Pointwise zero-interior is sufficient because any nonempty family then has a
zero-interior member.  It is not asserted here as necessary. -/
theorem AnalyticMixingFamilyHasZeroInteriorMember_of_pointwiseZeroInterior
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hZero : AnalyticMixingFamilyPointwiseZeroInterior C) :
    AnalyticMixingFamilyHasZeroInteriorMember C := by
  rcases hC with ⟨M, hM⟩
  exact ⟨M, hM, hZero M hM⟩

/-- Pointwise zero-interior supplies the discovered compatible-member condition
for any nonempty analytic family. -/
theorem AnalyticMixingFamilyHasCompatibleMember_of_pointwiseZeroInterior
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hZero : AnalyticMixingFamilyPointwiseZeroInterior C) :
    AnalyticMixingFamilyHasCompatibleMember C := by
  exact
    AnalyticMixingFamilyHasCompatibleMember_of_hasZeroInteriorMember C
      (AnalyticMixingFamilyHasZeroInteriorMember_of_pointwiseZeroInterior
        C hC hZero)

/-- A respecting global lower prevision supplies the analytic raw compatibility
predicate directly.  This is the constructive S1 target for any proposed
family-level compatibility condition. -/
theorem AnalyticMixingFamilyRawProcessCompatible_of_respectsLocalLower
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (L : LowerPrevision (ℕ → Bool))
    (hL :
      (bernoulliMixturePrefixProcessLowerSpec
        C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).respectsLocalLower L) :
    AnalyticMixingFamilyRawProcessCompatible C hC := by
  exact
    ImpreciseDeFinettiRawProcessCompatible_of_respectsLocalLower
      C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC L hL

/-- If one admissible mixture has an all-gambles analytic prefix-process
witness, then the whole analytic family lower envelope is raw-compatible. -/
theorem AnalyticMixingFamilyRawProcessCompatible_of_mem_analyticPrefixProcessWitness
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    {M : BernoulliMixture} (hM : M ∈ C)
    (hWitness : BernoulliMixtureAnalyticPrefixProcessWitness M) :
    AnalyticMixingFamilyRawProcessCompatible C hC := by
  rcases hWitness with ⟨P, hP⟩
  refine
    AnalyticMixingFamilyRawProcessCompatible_of_respectsLocalLower
      C hC P.toLowerPrevision ?_
  intro n X
  rw [bernoulliMixturePrefixProcessLowerSpec_localLower_apply]
  calc
    impreciseDeFinettiPrefixLowerEnvelope C n
        (bernoulliMixturePrefixLawAt C
          (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) n) X ≤
      (bernoulliMixturePrefixLaw_analytic M n).toPrecisePrevision X :=
        impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
          C n
          (bernoulliMixturePrefixLawAt C
            (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) n)
          hM X
    _ =
      P.toLowerPrevision
        (bernoulliMixturePrefixProcessCylinderSystem.cylinderGamble n X) := by
        simpa [PrecisePrevision.toLowerPrevision_apply] using (hP n X).symm

/-- F2 sufficiency in the discovered compatible-member form. -/
theorem AnalyticMixingFamilyRawProcessCompatible_of_hasCompatibleMember
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hMember : AnalyticMixingFamilyHasCompatibleMember C) :
    AnalyticMixingFamilyRawProcessCompatible C hC := by
  rcases hMember with ⟨M, hM, hWitness⟩
  exact
    AnalyticMixingFamilyRawProcessCompatible_of_mem_analyticPrefixProcessWitness
      C hC hM hWitness

/-- F2 sufficiency in concrete zero-interior-member form. -/
theorem AnalyticMixingFamilyRawProcessCompatible_of_hasZeroInteriorMember
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hZeroMember : AnalyticMixingFamilyHasZeroInteriorMember C) :
    AnalyticMixingFamilyRawProcessCompatible C hC := by
  exact
    AnalyticMixingFamilyRawProcessCompatible_of_hasCompatibleMember C hC
      (AnalyticMixingFamilyHasCompatibleMember_of_hasZeroInteriorMember
        C hZeroMember)

/-- F2 sufficiency for the original pointwise-zero candidate.  The necessity of
this condition remains a separate question because larger lower envelopes can be
compatible for weaker reasons. -/
theorem AnalyticMixingFamilyRawProcessCompatible_of_pointwiseZeroInterior
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hZero : AnalyticMixingFamilyPointwiseZeroInterior C) :
    AnalyticMixingFamilyRawProcessCompatible C hC := by
  exact
    AnalyticMixingFamilyRawProcessCompatible_of_hasCompatibleMember C hC
      (AnalyticMixingFamilyHasCompatibleMember_of_pointwiseZeroInterior
        C hC hZero)

/-- The family-level first-true exploding-gamble obstruction: if the local
analytic lower envelope assigns strictly positive lower mass to every first-true
cylinder, then no raw all-gambles process completion exists. -/
theorem not_AnalyticMixingFamilyRawProcessCompatible_of_positiveFirstTrueLowerEnvelope
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hPos : AnalyticMixingFamilyPositiveFirstTrueLowerEnvelope C) :
    ¬ AnalyticMixingFamilyRawProcessCompatible C hC := by
  intro hCompat
  let S :=
    bernoulliMixturePrefixProcessLowerSpec C
      (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC
  have hCompatS : S.toCredalSpec.hasCompatibleCompletion := by
    simpa [S, AnalyticMixingFamilyRawProcessCompatible,
      ImpreciseDeFinettiRawProcessCompatible] using hCompat
  rcases hCompatS with ⟨P, hP⟩
  apply no_rawPrecisePrevision_extends_positiveFirstTrueWeights P
  intro n
  have hDominates :
      S.localLower (n + 1) (firstTruePrefixGamble n) ≤
        (S.cylinders.marginalPrevision (n + 1) P)
          (firstTruePrefixGamble n) := by
    exact hP (n + 1) (firstTruePrefixGamble n)
  have hLocalPos :
      0 < S.localLower (n + 1) (firstTruePrefixGamble n) := by
    simpa [S, AnalyticMixingFamilyPositiveFirstTrueLowerEnvelope,
      bernoulliMixturePrefixProcessLowerSpec_localLower_apply] using hPos n
  have hMarginalPos :
      0 <
        (S.cylinders.marginalPrevision (n + 1) P)
          (firstTruePrefixGamble n) :=
    lt_of_lt_of_le hLocalPos hDominates
  have hCylinder :
      P (firstTrueCylinderGamble n) =
        (S.cylinders.marginalPrevision (n + 1) P)
          (firstTruePrefixGamble n) := by
    calc
      P (firstTrueCylinderGamble n)
          = P
              (bernoulliMixturePrefixProcessCylinderSystem.cylinderGamble
                (n + 1) (firstTruePrefixGamble n)) := by
                  rw [firstTrueCylinderGamble_eq_cylinderGamble]
      _ =
        (S.cylinders.marginalPrevision (n + 1) P)
          (firstTruePrefixGamble n) := by
            rfl
  rwa [hCylinder]

/-- Exact F2-facing lower-prevision form of analytic raw compatibility.  The
next substantive sufficiency proof is therefore exactly the construction of a
global lower prevision respecting the analytic prefix lower envelope. -/
theorem AnalyticMixingFamilyRawProcessCompatible_iff_exists_respectsLocalLower
    (C : Set BernoulliMixture) (hC : C.Nonempty) :
    AnalyticMixingFamilyRawProcessCompatible C hC ↔
      ∃ L : LowerPrevision (ℕ → Bool),
        (bernoulliMixturePrefixProcessLowerSpec
          C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).respectsLocalLower L := by
  simpa [AnalyticMixingFamilyRawProcessCompatible] using
    (ImpreciseDeFinettiRawProcessCompatible_iff_exists_respectsLocalLower
      C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC)

/-- The analytic family-level crown follows from the neutral raw compatibility
condition together with the unconditional canonical external mixing readout. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_rawProcessCompatible
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hCompat : AnalyticMixingFamilyRawProcessCompatible C hC) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC where
  canonicalExternalMixingFamily :=
    impreciseDeFinetti_canonicalExternalMixingFamily C hC
  processLawCrown :=
    impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_rawProcessCompatible
      C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC hCompat

/-- Exact analytic boundary: the external de-Finetti mixing-family readout is
unconditional, so the raw analytic crown is equivalent to the neutral raw
process-compatibility predicate. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_iff_rawProcessCompatible
    (C : Set BernoulliMixture) (hC : C.Nonempty) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC ↔
      AnalyticMixingFamilyRawProcessCompatible C hC := by
  constructor
  · intro hCrown
    exact hCrown.processLawCrown.processCompatibleCompletion
  · intro hCompat
    exact
      impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_rawProcessCompatible
        C hC hCompat

/-- Exact lower-prevision form of the analytic F2 boundary: the raw all-gambles
analytic crown exists iff some global lower prevision respects the analytic
finite-prefix lower envelope. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_iff_exists_respectsLocalLower
    (C : Set BernoulliMixture) (hC : C.Nonempty) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC ↔
      ∃ L : LowerPrevision (ℕ → Bool),
        (bernoulliMixturePrefixProcessLowerSpec
          C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).respectsLocalLower L := by
  rw [impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_iff_rawProcessCompatible]
  exact AnalyticMixingFamilyRawProcessCompatible_iff_exists_respectsLocalLower C hC

/-- Public F2 sharp compatibility statement: the external sigma-additive
de-Finetti mixing-family readout is unconditional, while the raw all-gambles
analytic crown is exactly the lower-prevision compatibility condition. -/
theorem impreciseDeFinetti_analyticMixingFamily_sharpCompatibilityCrown
    (C : Set BernoulliMixture) (hC : C.Nonempty) :
    ImpreciseDeFinettiCanonicalExternalMixingFamily C hC ∧
      (ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC ↔
        ∃ L : LowerPrevision (ℕ → Bool),
          (bernoulliMixturePrefixProcessLowerSpec
            C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).respectsLocalLower L) := by
  exact
    ⟨impreciseDeFinetti_canonicalExternalMixingFamily C hC,
      impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_iff_exists_respectsLocalLower
        C hC⟩

/-- Public S1 sufficiency in the discovered compatible-member form: if the
credal family contains one mixture with an all-gambles analytic prefix-process
witness, then the full analytic mixing-family process-law crown follows. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_hasCompatibleMember
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hMember : AnalyticMixingFamilyHasCompatibleMember C) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC := by
  exact
    impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_rawProcessCompatible
      C hC
      (AnalyticMixingFamilyRawProcessCompatible_of_hasCompatibleMember
        C hC hMember)

/-- Public S1 sufficiency in concrete zero-interior-member form. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_hasZeroInteriorMember
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hZeroMember : AnalyticMixingFamilyHasZeroInteriorMember C) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC := by
  exact
    impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_hasCompatibleMember
      C hC
      (AnalyticMixingFamilyHasCompatibleMember_of_hasZeroInteriorMember
        C hZeroMember)

/-- Public S1 sufficiency for the pointwise-zero candidate. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_pointwiseZeroInterior
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hZero : AnalyticMixingFamilyPointwiseZeroInterior C) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC := by
  exact
    impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_hasCompatibleMember
      C hC
      (AnalyticMixingFamilyHasCompatibleMember_of_pointwiseZeroInterior
        C hC hZero)

/-- Pointwise zero-interior is not necessary for the analytic family-level raw
crown: a zero-interior member supplies the compatible raw process, while a
positive-interior member refutes the pointwise-zero candidate condition. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_and_not_pointwiseZeroInterior
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hZeroMember : AnalyticMixingFamilyHasZeroInteriorMember C)
    (hPositiveMember : AnalyticMixingFamilyHasPositiveInteriorMember C) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC ∧
      ¬ AnalyticMixingFamilyPointwiseZeroInterior C := by
  exact
    ⟨impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_hasZeroInteriorMember
      C hC hZeroMember,
      not_AnalyticMixingFamilyPointwiseZeroInterior_of_hasPositiveInteriorMember
        C hPositiveMember⟩

/-- Consequently, the implication from analytic raw crown to pointwise
zero-interior is false for any nonempty family containing both a zero-interior
member and a positive-interior member. -/
theorem not_forall_impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_imp_pointwiseZeroInterior
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hZeroMember : AnalyticMixingFamilyHasZeroInteriorMember C)
    (hPositiveMember : AnalyticMixingFamilyHasPositiveInteriorMember C) :
    ¬ (∀ (D : Set BernoulliMixture) (hD : D.Nonempty),
        ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown D hD →
          AnalyticMixingFamilyPointwiseZeroInterior D) := by
  intro hAll
  have hPair :
      ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC ∧
        ¬ AnalyticMixingFamilyPointwiseZeroInterior C :=
    impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_and_not_pointwiseZeroInterior
      C hC hZeroMember hPositiveMember
  exact hPair.2 (hAll C hC hPair.1)

/-- Closed S2 counterexample: there exists an analytic mixing family whose raw
all-gambles crown exists but whose members do not all have zero interior mixing
mass. -/
theorem exists_impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_not_pointwiseZeroInterior :
    ∃ (C : Set BernoulliMixture), ∃ hC : C.Nonempty,
      ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC ∧
        ¬ AnalyticMixingFamilyPointwiseZeroInterior C := by
  let C : Set BernoulliMixture :=
    analyticMixingFamilyPointwiseNecessityCounterexample
  have hC : C.Nonempty := by
    exact ⟨bernoulliMixtureDiracZero, by
      simp [C, analyticMixingFamilyPointwiseNecessityCounterexample]⟩
  have hZeroMember : AnalyticMixingFamilyHasZeroInteriorMember C := by
    exact ⟨bernoulliMixtureDiracZero,
      by simp [C, analyticMixingFamilyPointwiseNecessityCounterexample],
      bernoulliMixtureDiracZero_zeroInterior⟩
  have hPositiveMember : AnalyticMixingFamilyHasPositiveInteriorMember C := by
    exact ⟨bernoulliMixtureDiracHalf,
      by simp [C, analyticMixingFamilyPointwiseNecessityCounterexample],
      bernoulliMixtureDiracHalf_positiveInterior⟩
  exact
    ⟨C, hC,
      impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_and_not_pointwiseZeroInterior
        C hC hZeroMember hPositiveMember⟩

/-- Closed refutation of the too-strong necessity claim: the analytic raw crown
does not force pointwise zero-interior for every member of the credal family. -/
theorem not_forall_impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_imp_pointwiseZeroInterior_closed :
    ¬ (∀ (C : Set BernoulliMixture) (hC : C.Nonempty),
        ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC →
          AnalyticMixingFamilyPointwiseZeroInterior C) := by
  intro hAll
  rcases exists_impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_not_pointwiseZeroInterior with
    ⟨C, hC, hCrown, hNotPointwise⟩
  exact hNotPointwise (hAll C hC hCrown)

/-- Crown-level form of the family first-true obstruction. -/
theorem not_impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_positiveFirstTrueLowerEnvelope
    (C : Set BernoulliMixture) (hC : C.Nonempty)
    (hPos : AnalyticMixingFamilyPositiveFirstTrueLowerEnvelope C) :
    ¬ ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC := by
  intro hCrown
  exact
    (not_AnalyticMixingFamilyRawProcessCompatible_of_positiveFirstTrueLowerEnvelope
      C hC hPos)
      ((impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_iff_rawProcessCompatible
        C hC).mp hCrown)

/-- The exact raw compatibility condition fails for a positive-interior
posterior singleton.  This is the predicate-level form of the Option-U
refutation. -/
theorem not_AnalyticMixingFamilyRawProcessCompatible_posteriorSingleton_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    ¬ AnalyticMixingFamilyRawProcessCompatible
        (posteriorBernoulliMixtureSet M k l
          (ne_of_gt
            (BernoulliMixture.countEvidenceMass_pos_of_interiorMass M k l hInterior)))
        (posteriorBernoulliMixtureSet_nonempty M k l
          (ne_of_gt
            (BernoulliMixture.countEvidenceMass_pos_of_interiorMass M k l hInterior))) := by
  intro hCompat
  let hZ : M.countEvidenceMass k l ≠ 0 :=
    ne_of_gt (BernoulliMixture.countEvidenceMass_pos_of_interiorMass M k l hInterior)
  have hCrown :
      ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
        (posteriorBernoulliMixtureSet M k l hZ)
        (posteriorBernoulliMixtureSet_nonempty M k l hZ) :=
    impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_rawProcessCompatible
      (posteriorBernoulliMixtureSet M k l hZ)
      (posteriorBernoulliMixtureSet_nonempty M k l hZ)
      hCompat
  have hPosterior :
      PosteriorBernoulliMixtureProcessLawCrown M k l hZ :=
    posteriorBernoulliMixture_processLawCrown_of_singletonAnalyticMixingFamilyCrown
      M k l hZ hCrown
  exact
    not_posteriorBernoulliMixture_processLawCrown_of_interiorMixingMass
      M k l hZ hInterior hPosterior

/-- The analytic imprecise de Finetti package already exists at the canonical
prefix finite-window realization boundary.  Compared with the concrete
tail-false carrier-subset theorem below, this keeps only the abstract
finite-window realization hypothesis for the canonical joint-window system. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixFiniteWindowRealization
    (C : Set BernoulliMixture)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec
          C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec
              C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).localLower n)})
    (hRealize :
      (bernoulliMixturePrefixProcessLowerSpec
        C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).jointPrevisionsRealizedInCarrier
        (bernoulliMixturePrefixProcessFiniteJointWindowSystem
          C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC)
        carrier) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC where
  canonicalExternalMixingFamily :=
    impreciseDeFinetti_canonicalExternalMixingFamily C hC
  processLawCrown :=
    impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_prefixMarginalConsistentCarrierRealization
      C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC
      carrier hCompact hCarrierConvex hClosed
      (bernoulliMixturePrefixProcessMarginalConsistent_analytic C)
      hRealize

/-- The canonical sigma-additive Bernoulli-mixture family and the raw
all-gambles process-law crown assemble into one honest analytic infinite de
Finetti package as soon as the explicit tail-false finite-window realizers sit
inside a compact carrier. -/
theorem impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixTailFalseExtensionCarrierSubset
    (C : Set BernoulliMixture)
    (hC : C.Nonempty)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((bernoulliMixturePrefixProcessLowerSpec
          C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((bernoulliMixturePrefixProcessLowerSpec
              C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC).localLower n)})
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C hC :=
  impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixFiniteWindowRealization
    C hC carrier hCompact hCarrierConvex hClosed
    (bernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_prefixTailFalseExtensionCarrierSubset
      C (fun M _ n => bernoulliMixturePrefixLaw_analytic M n) hC
      carrier hSubset)

/-- If an external Boolean process realizes a posterior Bernoulli mixture, its
one-bit true prefix prevision is the normalized posterior mixture's one-step
true evidence mass. -/
theorem posteriorBernoulliMixture_external_oneBitTruePrevision_eq_countEvidenceMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    A.prefixPrevision 1 oneBitTrueGamble =
      (M.posteriorBernoulliMixture k l hZ).countEvidenceMass 1 0 := by
  rw [hRealize 1 oneBitTrueGamble]
  exact
    bernoulliMixturePrefixPrevision_oneBitTrue_eq_countEvidenceMass
      (M.posteriorBernoulliMixture k l hZ)

/-- If an external Boolean process realizes a posterior Bernoulli mixture, its
one-bit false prefix prevision is the normalized posterior mixture's one-step
false evidence mass. -/
theorem posteriorBernoulliMixture_external_oneBitFalsePrevision_eq_countEvidenceMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    A.prefixPrevision 1 oneBitFalseGamble =
      (M.posteriorBernoulliMixture k l hZ).countEvidenceMass 0 1 := by
  rw [hRealize 1 oneBitFalseGamble]
  exact
    bernoulliMixturePrefixPrevision_oneBitFalse_eq_countEvidenceMass
      (M.posteriorBernoulliMixture k l hZ)

/-- Strengthened one-bit true external readout: once the external process
realizes the normalized posterior mixture, its true prefix prevision is exactly
the original mixture's Bayes-ratio posterior predictive probability. -/
theorem posteriorBernoulliMixture_external_oneBitTruePrevision_eq_posteriorPredictiveTrue
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    A.prefixPrevision 1 oneBitTrueGamble =
      M.posteriorPredictiveTrue k l := by
  rw [posteriorBernoulliMixture_external_oneBitTruePrevision_eq_countEvidenceMass
    M k l hZ A hRealize]
  exact
    BernoulliMixture.posteriorBernoulliMixture_countEvidenceMass_true_eq_posteriorPredictiveTrue
      M k l hZ

/-- Strengthened one-bit false external readout: once the external process
realizes the normalized posterior mixture, its false prefix prevision is exactly
the original mixture's Bayes-ratio posterior predictive probability. -/
theorem posteriorBernoulliMixture_external_oneBitFalsePrevision_eq_posteriorPredictiveFalse
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    A.prefixPrevision 1 oneBitFalseGamble =
      M.posteriorPredictiveFalse k l := by
  rw [posteriorBernoulliMixture_external_oneBitFalsePrevision_eq_countEvidenceMass
    M k l hZ A hRealize]
  exact
    BernoulliMixture.posteriorBernoulliMixture_countEvidenceMass_false_eq_posteriorPredictiveFalse
      M k l hZ

/-- Paper-facing posterior external-carrier package.  It does not construct the
external process law; it records exactly what follows once such a law realizes
the posterior Bernoulli mixture: the compact bounded path-law carrier is
nonempty and compact, finite-prefix cylinder observables are determined, and
their PLN width/complement readouts are precise. -/
structure PosteriorBernoulliMixtureExternalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω) : Prop where
  realizesPosterior :
    BernoulliMixtureExternalProcessRealization
      (M.posteriorBernoulliMixture k l hZ) A
  compactCarrier_nonempty :
    (externalPathLawBoundedMeasurableCompactCredalSet
      ({A} : Set (ExternalBoolProcessLaw Ω))).Nonempty
  compactCarrier_isCompact :
    @IsCompact (BoundedMeasurablePrecisePrevision (ℕ → Bool))
      (BoundedMeasurablePrecisePrevision.evaluationTopology
        (Ω := ℕ → Bool))
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw Ω)))
  prefixPrevision_eq_posterior :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      A.prefixPrevision n X =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  oneBitTruePrevision_eq_countEvidenceMass :
    A.prefixPrevision 1 oneBitTrueGamble =
      (M.posteriorBernoulliMixture k l hZ).countEvidenceMass 1 0
  oneBitFalsePrevision_eq_countEvidenceMass :
    A.prefixPrevision 1 oneBitFalseGamble =
      (M.posteriorBernoulliMixture k l hZ).countEvidenceMass 0 1
  oneBitTruePrevision_eq_posteriorPredictiveTrue :
    A.prefixPrevision 1 oneBitTrueGamble =
      M.posteriorPredictiveTrue k l
  oneBitFalsePrevision_eq_posteriorPredictiveFalse :
    A.prefixPrevision 1 oneBitFalseGamble =
      M.posteriorPredictiveFalse k l
  prefixProjectiveDetermines :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec
        ({A} : Set (ExternalBoolProcessLaw Ω)) n).determinesGlobalGamble X
  compactPrefixDetermines :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableCredalSetDetermines
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n X)
  compactPrefixWidth_eq_zero :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableEnvelopeWidth
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n X) = 0
  compactPrefixWidthComplement_eq_one :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n X) = 1

/-- Once an external Boolean process realizes the posterior Bernoulli mixture,
the compact bounded path-law carrier gives a precise posterior prefix process
surface.  The remaining construction problem is therefore exactly the external
realization predicate, not the PLN readout layer. -/
theorem posteriorBernoulliMixture_externalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    PosteriorBernoulliMixtureExternalCarrierCrown M k l hZ A where
  realizesPosterior := hRealize
  compactCarrier_nonempty :=
    externalPathLawBoundedMeasurableCompactCredalSet_nonempty
      ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩
  compactCarrier_isCompact :=
    externalPathLawBoundedMeasurableCompactCredalSet_isCompact
      ({A} : Set (ExternalBoolProcessLaw Ω))
  prefixPrevision_eq_posterior := hRealize
  oneBitTruePrevision_eq_countEvidenceMass :=
    posteriorBernoulliMixture_external_oneBitTruePrevision_eq_countEvidenceMass
      M k l hZ A hRealize
  oneBitFalsePrevision_eq_countEvidenceMass :=
    posteriorBernoulliMixture_external_oneBitFalsePrevision_eq_countEvidenceMass
      M k l hZ A hRealize
  oneBitTruePrevision_eq_posteriorPredictiveTrue :=
    posteriorBernoulliMixture_external_oneBitTruePrevision_eq_posteriorPredictiveTrue
      M k l hZ A hRealize
  oneBitFalsePrevision_eq_posteriorPredictiveFalse :=
    posteriorBernoulliMixture_external_oneBitFalsePrevision_eq_posteriorPredictiveFalse
      M k l hZ A hRealize
  prefixProjectiveDetermines := by
    intro n X
    exact
      externalPathLawPrefixProjectiveSpec_determinesGlobalGamble_of_processAgreement
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X
        (by
          intro B hB C hC
          have hB_eq : B = A := by
            simpa using hB
          have hC_eq : C = A := by
            simpa using hC
          subst B
          subst C
          rfl)
  compactPrefixDetermines := by
    intro n X
    exact
      externalPathLawBoundedMeasurableCompactCredalSet_determines_prefix_of_processAgreement
        ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩ n X
        (by
          intro B hB C hC
          have hB_eq : B = A := by
            simpa using hB
          have hC_eq : C = A := by
            simpa using hC
          subst B
          subst C
          rfl)
  compactPrefixWidth_eq_zero := by
    intro n X
    exact
      boundedMeasurableEnvelopeWidth_externalPathLawCompactCredalSet_prefix_eq_zero_of_processAgreement
        ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩ n X
        (by
          intro B hB C hC
          have hB_eq : B = A := by
            simpa using hB
          have hC_eq : C = A := by
            simpa using hC
          subst B
          subst C
          rfl)
  compactPrefixWidthComplement_eq_one := by
    intro n X
    exact
      boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_one_of_processAgreement
        ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩ n X
        (by
          intro B hB C hC
          have hB_eq : B = A := by
            simpa using hB
          have hC_eq : C = A := by
            simpa using hC
          subst B
          subst C
          rfl)

/-- The realizing external posterior process itself supplies an actual
bounded-measurable compact-carrier witness on the common infinite path space.

Positive example: when `A` is the canonical `Bool^ℕ` posterior process law, the
witness is the sigma-additive expectation induced by that global measure.
Negative example: this is not a raw all-gambles `PrecisePrevision (ℕ → Bool)`;
it lives exactly at the bounded-measurable carrier where the canonical global
process measure is honestly available. -/
theorem posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    A.pathBoundedMeasurablePrevision ∈
        externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)) ∧
      ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
        A.pathBoundedMeasurablePrevision
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  refine ⟨?_, ?_⟩
  · exact
      mem_externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw Ω)) (by simp)
  · intro n X
    calc
      A.pathBoundedMeasurablePrevision
          (externalPathLawPrefixBoundedMeasurableGamble n X)
          = A.prefixPrevision n X := by
              exact
                ExternalBoolProcessLaw.pathBoundedMeasurablePrevision_prefix_eq_prefixPrevision
                  A n X
      _ =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X :=
          hRealize n X

/-- Honest raw-vs-bounded-measurable boundary for any realizing posterior
external process law: the sigma-additive bounded-measurable witness exists
exactly, while the stronger raw all-gambles witness fails in the interior-mass
regime. -/
theorem posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness_and_noPrefixWitness_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    A.pathBoundedMeasurablePrevision ∈
        externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)) ∧
      (∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
        A.pathBoundedMeasurablePrevision
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      (posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness
        M k l hZ A hRealize).1
  · exact
      (posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness
        M k l hZ A hRealize).2
  · exact
      not_posteriorBernoulliMixturePrefixProcessWitness_of_interiorMixingMass
        M k l hZ hInterior

/-- For a singleton external posterior process law, the shared finite-prefix
lower envelope already equals the analytic posterior prefix prevision. -/
theorem posteriorBernoulliMixture_externalPathLawPrefixLowerEnvelope_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixLowerEnvelope
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  have hSingleton :
      externalPathLawPrefixCredalSet ({A} : Set (ExternalBoolProcessLaw Ω)) n =
        ({A.prefixPrevision n} : CredalPrevisionSet (Fin n → Bool)) := by
    ext P
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hBA : B = A := by simpa using hB
      subst B
      simp
    · intro hP
      exact ⟨A, by simp, by simpa using hP⟩
  have hDet :
      credalSetDetermines
        (externalPathLawPrefixCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)) n) X := by
    rw [hSingleton]
    exact credalSetDetermines_singleton (A.prefixPrevision n) X
  have hEq :
      externalPathLawPrefixLowerEnvelope
          ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
        A.prefixPrevision n X := by
    unfold externalPathLawPrefixLowerEnvelope
    exact lowerEnvelope_eq_of_credalSetDetermines
      (externalPathLawPrefixCredalSet ({A} : Set (ExternalBoolProcessLaw Ω)) n)
      X
      (externalPathLawPrefixCredalSet_nonempty
        ({A} : Set (ExternalBoolProcessLaw Ω)) n ⟨A, rfl⟩)
      (finite_credalRange_bddBelow
        (externalPathLawPrefixCredalSet ({A} : Set (ExternalBoolProcessLaw Ω)) n) X)
      (by exact ⟨A, by simp, rfl⟩)
      hDet
  calc
    externalPathLawPrefixLowerEnvelope ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
        A.prefixPrevision n X := hEq
    _ =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X :=
        hRealize n X

/-- For a singleton external posterior process law, the shared finite-prefix
upper envelope already equals the analytic posterior prefix prevision. -/
theorem posteriorBernoulliMixture_externalPathLawPrefixUpperEnvelope_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixUpperEnvelope
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  have hSingleton :
      externalPathLawPrefixCredalSet ({A} : Set (ExternalBoolProcessLaw Ω)) n =
        ({A.prefixPrevision n} : CredalPrevisionSet (Fin n → Bool)) := by
    ext P
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hBA : B = A := by simpa using hB
      subst B
      simp
    · intro hP
      exact ⟨A, by simp, by simpa using hP⟩
  have hDet :
      credalSetDetermines
        (externalPathLawPrefixCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)) n) X := by
    rw [hSingleton]
    exact credalSetDetermines_singleton (A.prefixPrevision n) X
  have hEq :
      externalPathLawPrefixUpperEnvelope
          ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
        A.prefixPrevision n X := by
    unfold externalPathLawPrefixUpperEnvelope
    exact upperEnvelope_eq_of_credalSetDetermines
      (externalPathLawPrefixCredalSet ({A} : Set (ExternalBoolProcessLaw Ω)) n)
      X
      (externalPathLawPrefixCredalSet_nonempty
        ({A} : Set (ExternalBoolProcessLaw Ω)) n ⟨A, rfl⟩)
      (finite_credalRange_bddAbove
        (externalPathLawPrefixCredalSet ({A} : Set (ExternalBoolProcessLaw Ω)) n) X)
      (by exact ⟨A, by simp, rfl⟩)
      hDet
  calc
    externalPathLawPrefixUpperEnvelope ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
        A.prefixPrevision n X := hEq
    _ =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X :=
        hRealize n X

/-- Shared bounded-measurable natural extension interface for the singleton
external posterior process law: on every finite-prefix cylinder observable, the
Walley lower envelope is already the analytic posterior prefix prevision. -/
theorem posteriorBernoulliMixture_externalCompactNaturalExtension_prefix_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    boundedMeasurableNaturalExtensionPrevision
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
          ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩)
        (externalPathLawPrefixBoundedMeasurableGamble n X) =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  rw [
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixLower
      ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩ n X]
  exact
    posteriorBernoulliMixture_externalPathLawPrefixLowerEnvelope_eq_posterior
      M k l hZ A hRealize n X

/-- Shared bounded-measurable upper-envelope interface for the singleton
external posterior process law: on every finite-prefix cylinder observable, the
upper Walley envelope is already the analytic posterior prefix prevision. -/
theorem posteriorBernoulliMixture_externalCompactNaturalUpperEnvelope_prefix_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A)
    (n : ℕ) (X : Gamble (Fin n → Bool)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
          ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩)
        (externalPathLawPrefixBoundedMeasurableGamble n X) =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  rw [
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_prefix_eq_finitePrefixUpper
      ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩ n X]
  exact
    posteriorBernoulliMixture_externalPathLawPrefixUpperEnvelope_eq_posterior
      M k l hZ A hRealize n X

/-- Paper-facing posterior-update/external-carrier package.  This joins the
Bayes-ratio update laws from `DeFinetti.lean` to the posterior singleton
projective-prefix crown and to the external process-carrier surface.  The
remaining infinite-process construction boundary is still explicit in
`posteriorExternalRealization`. -/
structure PosteriorBernoulliMixtureUpdateExternalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω) : Prop where
  updateCrown :
    BernoulliMixture.PosteriorUpdateCrown M k l
  prefixProjectiveCrown :
    PosteriorBernoulliMixturePrefixProjectiveCrown M k l hZ
  externalCarrierCrown :
    PosteriorBernoulliMixtureExternalCarrierCrown M k l hZ A
  posteriorExternalRealization :
    BernoulliMixtureExternalProcessRealization
      (M.posteriorBernoulliMixture k l hZ) A
  processPrefixPrevision_eq_posterior :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      A.prefixPrevision n X =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  processOneBitTruePrevision_eq_countEvidenceMass :
    A.prefixPrevision 1 oneBitTrueGamble =
      (M.posteriorBernoulliMixture k l hZ).countEvidenceMass 1 0
  processOneBitFalsePrevision_eq_countEvidenceMass :
    A.prefixPrevision 1 oneBitFalseGamble =
      (M.posteriorBernoulliMixture k l hZ).countEvidenceMass 0 1
  processOneBitTruePrevision_eq_posteriorPredictiveTrue :
    A.prefixPrevision 1 oneBitTrueGamble =
      M.posteriorPredictiveTrue k l
  processOneBitFalsePrevision_eq_posteriorPredictiveFalse :
    A.prefixPrevision 1 oneBitFalseGamble =
      M.posteriorPredictiveFalse k l
  predictiveTrue_ratio :
    M.posteriorPredictiveTrue k l =
      M.countEvidenceMass (k + 1) l / M.countEvidenceMass k l
  predictiveFalse_ratio :
    M.posteriorPredictiveFalse k l =
      M.countEvidenceMass k (l + 1) / M.countEvidenceMass k l
  predictiveTrue_update :
    M.posteriorPredictiveTrue k l * M.countEvidenceMass k l =
      M.countEvidenceMass (k + 1) l
  predictiveFalse_update :
    M.posteriorPredictiveFalse k l * M.countEvidenceMass k l =
      M.countEvidenceMass k (l + 1)

/-- Once an external Boolean process realizes the normalized posterior mixture,
the posterior update laws, singleton projective-prefix determinations, and
compact external-carrier readouts form one review-facing package. -/
theorem posteriorBernoulliMixture_updateExternalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    PosteriorBernoulliMixtureUpdateExternalCarrierCrown M k l hZ A where
  updateCrown :=
    BernoulliMixture.posteriorUpdateCrown M k l hZ
  prefixProjectiveCrown :=
    posteriorBernoulliMixturePrefixProjectiveCrown M k l hZ
  externalCarrierCrown :=
    posteriorBernoulliMixture_externalCarrierCrown M k l hZ A hRealize
  posteriorExternalRealization := hRealize
  processPrefixPrevision_eq_posterior := hRealize
  processOneBitTruePrevision_eq_countEvidenceMass :=
    posteriorBernoulliMixture_external_oneBitTruePrevision_eq_countEvidenceMass
      M k l hZ A hRealize
  processOneBitFalsePrevision_eq_countEvidenceMass :=
    posteriorBernoulliMixture_external_oneBitFalsePrevision_eq_countEvidenceMass
      M k l hZ A hRealize
  processOneBitTruePrevision_eq_posteriorPredictiveTrue :=
    posteriorBernoulliMixture_external_oneBitTruePrevision_eq_posteriorPredictiveTrue
      M k l hZ A hRealize
  processOneBitFalsePrevision_eq_posteriorPredictiveFalse :=
    posteriorBernoulliMixture_external_oneBitFalsePrevision_eq_posteriorPredictiveFalse
      M k l hZ A hRealize
  predictiveTrue_ratio :=
    BernoulliMixture.posteriorPredictiveTrue_eq_countEvidenceMass_ratio M k l
  predictiveFalse_ratio :=
    BernoulliMixture.posteriorPredictiveFalse_eq_countEvidenceMass_ratio M k l
  predictiveTrue_update :=
    BernoulliMixture.posteriorPredictiveTrue_update_identity M k l hZ
  predictiveFalse_update :=
    BernoulliMixture.posteriorPredictiveFalse_update_identity M k l hZ

/-- Posterior/update/external-carrier package from a represented measurable
posterior process.  Compared with
`PosteriorBernoulliMixtureUpdateExternalCarrierCrown`, the infinite-process
boundary has been reduced from a raw all-prefix realization predicate to the
standard de Finetti singleton-cylinder representation predicate
`DeFinetti.Represents`. -/
structure PosteriorBernoulliMixtureRepresentedExternalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i)) : Prop where
  representedPosterior :
    DeFinetti.Represents (M.posteriorBernoulliMixture k l hZ) X μ
  inducedExternalRealization :
    BernoulliMixtureExternalProcessRealization
      (M.posteriorBernoulliMixture k l hZ)
      (ExternalBoolProcessLaw.ofProcess μ X hX)
  updateExternalCarrierCrown :
    PosteriorBernoulliMixtureUpdateExternalCarrierCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess μ X hX)
  processPrefixPrevision_eq_posterior :
    ∀ (n : ℕ) (Y : Gamble (Fin n → Bool)),
      (ExternalBoolProcessLaw.ofProcess μ X hX).prefixPrevision n Y =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision Y
  processOneBitTruePrevision_eq_posteriorPredictiveTrue :
    (ExternalBoolProcessLaw.ofProcess μ X hX).prefixPrevision 1
        oneBitTrueGamble =
      M.posteriorPredictiveTrue k l
  processOneBitFalsePrevision_eq_posteriorPredictiveFalse :
    (ExternalBoolProcessLaw.ofProcess μ X hX).prefixPrevision 1
        oneBitFalseGamble =
      M.posteriorPredictiveFalse k l

/-- A represented measurable posterior process canonically supplies the
external realization consumed by the posterior update/external-carrier crown. -/
theorem posteriorBernoulliMixture_representedExternalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Bool) (hX : ∀ i : ℕ, Measurable (X i))
    (hRep : DeFinetti.Represents
      (M.posteriorBernoulliMixture k l hZ) X μ) :
    PosteriorBernoulliMixtureRepresentedExternalCarrierCrown
      M k l hZ μ X hX where
  representedPosterior := hRep
  inducedExternalRealization :=
    externalBoolProcessLawOf_realizes_posteriorBernoulliMixture_of_represents
      M k l hZ μ X hX hRep
  updateExternalCarrierCrown :=
    posteriorBernoulliMixture_updateExternalCarrierCrown
      M k l hZ (ExternalBoolProcessLaw.ofProcess μ X hX)
      (externalBoolProcessLawOf_realizes_posteriorBernoulliMixture_of_represents
        M k l hZ μ X hX hRep)
  processPrefixPrevision_eq_posterior :=
    externalBoolProcessLawOf_realizes_posteriorBernoulliMixture_of_represents
      M k l hZ μ X hX hRep
  processOneBitTruePrevision_eq_posteriorPredictiveTrue :=
    posteriorBernoulliMixture_external_oneBitTruePrevision_eq_posteriorPredictiveTrue
      M k l hZ (ExternalBoolProcessLaw.ofProcess μ X hX)
      (externalBoolProcessLawOf_realizes_posteriorBernoulliMixture_of_represents
        M k l hZ μ X hX hRep)
  processOneBitFalsePrevision_eq_posteriorPredictiveFalse :=
    posteriorBernoulliMixture_external_oneBitFalsePrevision_eq_posteriorPredictiveFalse
      M k l hZ (ExternalBoolProcessLaw.ofProcess μ X hX)
      (externalBoolProcessLawOf_realizes_posteriorBernoulliMixture_of_represents
        M k l hZ μ X hX hRep)

/-- The posterior Bernoulli mixture has a canonical represented global
`Bool^ℕ` process witness, obtained by mixing the internal iid `Theta → Bool^ℕ`
kernel against the posterior `Theta` law itself. -/
theorem posteriorBernoulliMixture_canonicalRepresentedExternalCarrierCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureRepresentedExternalCarrierCrown
      M k l hZ
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      coordProcess
      bernoulliMixtureCanonical_coordProcess_measurable := by
  exact posteriorBernoulliMixture_representedExternalCarrierCrown
    M k l hZ
    (bernoulliMixtureCanonicalProcessMeasure
      (M.posteriorBernoulliMixture k l hZ))
    coordProcess
    bernoulliMixtureCanonical_coordProcess_measurable
    (bernoulliMixtureCanonicalProcessMeasure_represents
      (M.posteriorBernoulliMixture k l hZ))

/-- The posterior Bernoulli mixture therefore also has a canonical external
path-law carrier crown with no extra realization assumptions. -/
theorem posteriorBernoulliMixture_canonicalExternalCarrierCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureExternalCarrierCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) := by
  exact posteriorBernoulliMixture_externalCarrierCrown
    M k l hZ
    (ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      coordProcess
      bernoulliMixtureCanonical_coordProcess_measurable)
    (bernoulliMixtureCanonicalExternalProcessRealization
      (M.posteriorBernoulliMixture k l hZ))

/-- Canonical posterior/update/external-carrier package: the posterior
Bernoulli mixture itself supplies the required external `Bool^ℕ` process law by
mixing the internal iid `Theta → Bool^ℕ` kernel against its own posterior
`Theta` law. -/
theorem posteriorBernoulliMixture_canonicalUpdateExternalCarrierCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureUpdateExternalCarrierCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) := by
  exact posteriorBernoulliMixture_updateExternalCarrierCrown
    M k l hZ
    (ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      coordProcess
      bernoulliMixtureCanonical_coordProcess_measurable)
    (bernoulliMixtureCanonicalExternalProcessRealization
      (M.posteriorBernoulliMixture k l hZ))

/-- Honest unconditional posterior Crown 2 endpoint at the shared
projective/cylinder/external-envelope layer.

Positive example: it packages the exact singleton posterior prefix/projective
surface, the compatible cylinder completion with zero finite-cylinder width,
and an external process law whose bounded-measurable compact path carrier
computes the same posterior prefix observables exactly.

Negative example: it does not claim a raw all-gambles
`PosteriorBernoulliMixtureProcessLawCrown`; that stronger compact/FIP carrier
boundary remains separate. -/
structure PosteriorBernoulliMixtureProcessEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω) : Prop where
  prefixProjectiveCrown :
    PosteriorBernoulliMixturePrefixProjectiveCrown M k l hZ
  prefixCylinderCompatibleCompletion :
    (posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec.hasCompatibleCylinderCompletion
  prefixCylinderEnvelopeWidth_eq_zero :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).cylinderEnvelopeWidth
        n X = 0
  prefixCylinderWidthComplement_eq_one :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      ((posteriorBernoulliMixturePrefixProcessLowerSpec M k l hZ).toCredalSpec).cylinderEnvelopeWidthComplement
        n X = 1
  externalCarrierCrown :
    PosteriorBernoulliMixtureExternalCarrierCrown M k l hZ A
  updateExternalCarrierCrown :
    PosteriorBernoulliMixtureUpdateExternalCarrierCrown M k l hZ A

/-- Once an external Boolean process realizes the posterior Bernoulli mixture,
the exact prefix/projective crown, exact cylinder completion, and external
bounded-measurable compact carrier readouts form one honest Crown 2 package. -/
theorem posteriorBernoulliMixture_processEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    PosteriorBernoulliMixtureProcessEnvelopeCrown M k l hZ A where
  prefixProjectiveCrown :=
    posteriorBernoulliMixturePrefixProjectiveCrown M k l hZ
  prefixCylinderCompatibleCompletion :=
    posteriorBernoulliMixturePrefixProcess_hasCompatibleCylinderCompletion M k l hZ
  prefixCylinderEnvelopeWidth_eq_zero := by
    intro n X
    exact posteriorBernoulliMixturePrefixProcess_cylinderEnvelopeWidth_eq_zero
      M k l hZ n X
  prefixCylinderWidthComplement_eq_one := by
    intro n X
    exact
      posteriorBernoulliMixturePrefixProcess_cylinderEnvelopeWidthComplement_eq_one
        M k l hZ n X
  externalCarrierCrown :=
    posteriorBernoulliMixture_externalCarrierCrown M k l hZ A hRealize
  updateExternalCarrierCrown :=
    posteriorBernoulliMixture_updateExternalCarrierCrown M k l hZ A hRealize

/-- Canonical unconditional posterior Crown 2 endpoint: the posterior
Bernoulli mixture itself supplies the needed global `Bool^ℕ` external process
law by mixing the iid `Theta → Bool^ℕ` kernel against its posterior `Theta`
law. -/
theorem posteriorBernoulliMixture_canonicalProcessEnvelopeCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureProcessEnvelopeCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) := by
  exact posteriorBernoulliMixture_processEnvelopeCrown
    M k l hZ
    (ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      coordProcess
      bernoulliMixtureCanonical_coordProcess_measurable)
    (bernoulliMixtureCanonicalExternalProcessRealization
      (M.posteriorBernoulliMixture k l hZ))

/-- Honest Crown 2 endpoint at the shared `ProjectiveCredal` envelope layer.

This packages the process-envelope crown together with the exact lower, upper,
and bounded-measurable natural-extension readouts on every finite-prefix
observable. It is the minimal interface needed to connect the posterior
predictive object to downstream credal-envelope consumers. -/
structure PosteriorBernoulliMixtureSharedEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω) : Prop where
  processEnvelopeCrown :
    PosteriorBernoulliMixtureProcessEnvelopeCrown M k l hZ A
  prefixLowerEnvelope_eq_posterior :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      externalPathLawPrefixLowerEnvelope
          ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  prefixUpperEnvelope_eq_posterior :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      externalPathLawPrefixUpperEnvelope
          ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  compactNaturalExtension_prefix_eq_posterior :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableNaturalExtensionPrevision
          (externalPathLawBoundedMeasurableCompactCredalSet
            ({A} : Set (ExternalBoolProcessLaw Ω)))
          (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
            ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩)
          (externalPathLawPrefixBoundedMeasurableGamble n X) =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  compactNaturalUpperEnvelope_prefix_eq_posterior :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      boundedMeasurableNaturalUpperEnvelopePrevision
          (externalPathLawBoundedMeasurableCompactCredalSet
            ({A} : Set (ExternalBoolProcessLaw Ω)))
          (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
            ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩)
          (externalPathLawPrefixBoundedMeasurableGamble n X) =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X

/-- Any external process law realizing the posterior Bernoulli mixture yields
the full shared-envelope Crown 2 interface. -/
theorem posteriorBernoulliMixture_sharedEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A where
  processEnvelopeCrown :=
    posteriorBernoulliMixture_processEnvelopeCrown M k l hZ A hRealize
  prefixLowerEnvelope_eq_posterior := by
    intro n X
    exact posteriorBernoulliMixture_externalPathLawPrefixLowerEnvelope_eq_posterior
      M k l hZ A hRealize n X
  prefixUpperEnvelope_eq_posterior := by
    intro n X
    exact posteriorBernoulliMixture_externalPathLawPrefixUpperEnvelope_eq_posterior
      M k l hZ A hRealize n X
  compactNaturalExtension_prefix_eq_posterior := by
    intro n X
    exact posteriorBernoulliMixture_externalCompactNaturalExtension_prefix_eq_posterior
      M k l hZ A hRealize n X
  compactNaturalUpperEnvelope_prefix_eq_posterior := by
    intro n X
    exact
      posteriorBernoulliMixture_externalCompactNaturalUpperEnvelope_prefix_eq_posterior
        M k l hZ A hRealize n X

/-- Honest final boundary package for any realizing posterior external process
law: the exact shared-envelope endpoint exists, the sigma-additive
bounded-measurable witness exists on the common compact path carrier, and the
remaining stronger raw all-gambles process-law crown is classified separately. -/
theorem posteriorBernoulliMixture_sharedEnvelopeCrown_and_pathBoundedMeasurableCompactWitness_and_processLawCrown_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω)
    (hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A ∧
      A.pathBoundedMeasurablePrevision ∈
        externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)) ∧
      (∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
        A.pathBoundedMeasurablePrevision
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X) ∧
      (PosteriorBernoulliMixtureProcessLawCrown M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact posteriorBernoulliMixture_sharedEnvelopeCrown M k l hZ A hRealize
  · exact
      (posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness
        M k l hZ A hRealize).1
  · exact
      (posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness
        M k l hZ A hRealize).2
  · exact
      posteriorBernoulliMixture_processLawCrown_iff_zeroInteriorMixingMass
        M k l hZ

/-- Canonical shared-envelope Crown 2 interface from the posterior's own
global `Bool^ℕ` process law. -/
theorem posteriorBernoulliMixture_canonicalSharedEnvelopeCrown
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) := by
  exact posteriorBernoulliMixture_sharedEnvelopeCrown
    M k l hZ
    (ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      coordProcess
      bernoulliMixtureCanonical_coordProcess_measurable)
    (bernoulliMixtureCanonicalExternalProcessRealization
      (M.posteriorBernoulliMixture k l hZ))

/-- The canonical posterior process always lives at the exact shared-envelope
endpoint, and its stronger raw all-gambles witness exists exactly in the
zero-interior-mass regime. -/
theorem posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_prefixWitness_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) ∧
      (posteriorBernoulliMixturePrefixProcessWitness M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_canonicalSharedEnvelopeCrown M k l hZ,
      posteriorBernoulliMixturePrefixProcessWitness_iff_zeroInteriorMixingMass M k l hZ⟩

/-- The same canonical shared-envelope endpoint also classifies the remaining
carrier-witness boundary exactly: some raw carrier witness exists iff the prior
puts zero mass on the interior `(0,1)`. -/
theorem posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) ∧
      ((∃ carrier : CredalPrevisionSet (ℕ → Bool),
          posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier) ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_canonicalSharedEnvelopeCrown M k l hZ,
      posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_iff_zeroInteriorMixingMass
        M k l hZ⟩

/-- The canonical posterior process already gives the full exact shared-envelope
endpoint, and the stronger raw process-law crown exists exactly in the
zero-interior-mass regime. -/
theorem posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_processLawCrown_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) ∧
      (PosteriorBernoulliMixtureProcessLawCrown M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_canonicalSharedEnvelopeCrown M k l hZ,
      posteriorBernoulliMixture_processLawCrown_iff_zeroInteriorMixingMass
        M k l hZ⟩

/-- Canonical posterior-process version of the full honest final boundary
package: exact shared-envelope endpoint, actual sigma-additive
bounded-measurable witness, and exact raw process-law crown classification. -/
theorem posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_pathBoundedMeasurableCompactWitness_and_processLawCrown_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A ∧
      A.pathBoundedMeasurablePrevision ∈
        externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      (∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
        A.pathBoundedMeasurablePrevision
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X) ∧
      (PosteriorBernoulliMixtureProcessLawCrown M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      coordProcess
      bernoulliMixtureCanonical_coordProcess_measurable
  exact
    posteriorBernoulliMixture_sharedEnvelopeCrown_and_pathBoundedMeasurableCompactWitness_and_processLawCrown_iff_zeroInteriorMixingMass
      M k l hZ A
      (bernoulliMixtureCanonicalExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ))

/-- In the nondegenerate interior-mass regime, Crown 2 has an exact canonical
shared-envelope posterior process object, while the stronger single-global raw
all-gambles witness is impossible.  This is the sharp formal statement of the
current raw-vs-bounded-measurable boundary. -/
theorem posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_noPrefixCarrierWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) ∧
      ∀ carrier : CredalPrevisionSet (ℕ → Bool),
        ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier := by
  refine ⟨posteriorBernoulliMixture_canonicalSharedEnvelopeCrown M k l hZ, ?_⟩
  intro carrier
  exact
    not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_interiorMixingMass
      M k l hZ carrier hInterior

/-- Direct-witness form of the same boundary: in the interior-mass regime, the
canonical shared-envelope endpoint exists exactly, while the stronger raw
global all-gambles witness itself is impossible. -/
theorem posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_noPrefixWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ
      (ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  refine ⟨posteriorBernoulliMixture_canonicalSharedEnvelopeCrown M k l hZ, ?_⟩
  exact
    not_posteriorBernoulliMixturePrefixProcessWitness_of_interiorMixingMass
      M k l hZ hInterior

/-- Canonical posterior-process witness at the honest sigma-additive layer:
the posterior de Finetti `Bool^ℕ` process measure yields an actual
bounded-measurable precise prevision member in the compact carrier, with exact
analytic prefix-cylinder values, while the stronger raw witness remains
impossible in the same nondegenerate interior-mass regime. -/
theorem posteriorBernoulliMixture_canonicalPathBoundedMeasurableCompactWitness_and_noPrefixWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable
    A.pathBoundedMeasurablePrevision ∈
        externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      (∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
        A.pathBoundedMeasurablePrevision
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      coordProcess
      bernoulliMixtureCanonical_coordProcess_measurable
  exact
    posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness_and_noPrefixWitness_of_interiorMixingMass
      M k l hZ A
      (bernoulliMixtureCanonicalExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ))
      hInterior

namespace PosteriorBernoulliMixtureSharedEnvelopeCrown

theorem prefixEnvelopeWidth_eq_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixEnvelopeWidth ({A} : Set (ExternalBoolProcessLaw Ω)) n X = 0 := by
  unfold externalPathLawPrefixEnvelopeWidth credalEnvelopeWidth
  change externalPathLawPrefixUpperEnvelope ({A} : Set (ExternalBoolProcessLaw Ω)) n X -
      externalPathLawPrefixLowerEnvelope ({A} : Set (ExternalBoolProcessLaw Ω)) n X = 0
  rw [hCrown.prefixUpperEnvelope_eq_posterior n X,
    hCrown.prefixLowerEnvelope_eq_posterior n X]
  ring

theorem prefixEnvelopeWidthComplement_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixEnvelopeWidthComplement
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X = 1 := by
  unfold externalPathLawPrefixEnvelopeWidthComplement credalEnvelopeWidthComplement
  change 1 - externalPathLawPrefixEnvelopeWidth
      ({A} : Set (ExternalBoolProcessLaw Ω)) n X = 1
  rw [hCrown.prefixEnvelopeWidth_eq_zero n X]
  ring

theorem prefixEnvelopeMidpoint_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixEnvelopeMidpoint
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold externalPathLawPrefixEnvelopeMidpoint credalEnvelopeMidpoint
  change
      (externalPathLawPrefixLowerEnvelope
          ({A} : Set (ExternalBoolProcessLaw Ω)) n X +
        externalPathLawPrefixUpperEnvelope
          ({A} : Set (ExternalBoolProcessLaw Ω)) n X) / 2 =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  rw [hCrown.prefixLowerEnvelope_eq_posterior n X,
    hCrown.prefixUpperEnvelope_eq_posterior n X]
  ring

theorem prefixPLNCoordinates_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    ( externalPathLawPrefixEnvelopeMidpoint
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X
    , externalPathLawPrefixEnvelopeWidthComplement
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X ) =
      ( (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
      , (1 : ℝ) ) := by
  refine Prod.ext ?_ ?_
  · exact hCrown.prefixEnvelopeMidpoint_eq_posterior n X
  · exact hCrown.prefixEnvelopeWidthComplement_eq_one n X

theorem compactPLNCoordinates_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    ( boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n X)
    , boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n X) ) =
      ( (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
      , (1 : ℝ) ) := by
  refine Prod.ext ?_ ?_
  · calc
      boundedMeasurableEnvelopeMidpoint
          (externalPathLawBoundedMeasurableCompactCredalSet
            ({A} : Set (ExternalBoolProcessLaw Ω)))
          (externalPathLawPrefixBoundedMeasurableGamble n X)
          =
        externalPathLawPrefixEnvelopeMidpoint
          ({A} : Set (ExternalBoolProcessLaw Ω)) n X := by
            exact
              boundedMeasurableEnvelopeMidpoint_externalPathLawCompactCredalSet_prefix_eq_finitePrefixMidpoint
                ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩ n X
      _ =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X :=
        hCrown.prefixEnvelopeMidpoint_eq_posterior n X
  · calc
      boundedMeasurableEnvelopeWidthComplement
          (externalPathLawBoundedMeasurableCompactCredalSet
            ({A} : Set (ExternalBoolProcessLaw Ω)))
          (externalPathLawPrefixBoundedMeasurableGamble n X)
          =
        externalPathLawPrefixEnvelopeWidthComplement
          ({A} : Set (ExternalBoolProcessLaw Ω)) n X := by
            exact
              boundedMeasurableEnvelopeWidthComplement_externalPathLawCompactCredalSet_prefix_eq_finitePrefixComplement
                ({A} : Set (ExternalBoolProcessLaw Ω)) ⟨A, rfl⟩ n X
      _ = 1 := hCrown.prefixEnvelopeWidthComplement_eq_one n X

end PosteriorBernoulliMixtureSharedEnvelopeCrown

/-- The shared-envelope Crown 2 interface collapses the singleton external
posterior prefix credal width to zero. -/
theorem posteriorBernoulliMixture_sharedEnvelopeCrown_prefixEnvelopeWidth_eq_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixEnvelopeWidth ({A} : Set (ExternalBoolProcessLaw Ω)) n X = 0 :=
  hCrown.prefixEnvelopeWidth_eq_zero n X

/-- The shared-envelope Crown 2 interface makes the singleton external
posterior prefix width-complement coordinate maximal. -/
theorem posteriorBernoulliMixture_sharedEnvelopeCrown_prefixEnvelopeWidthComplement_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixEnvelopeWidthComplement
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X = 1 :=
  hCrown.prefixEnvelopeWidthComplement_eq_one n X

/-- The shared-envelope Crown 2 interface makes the singleton external
posterior prefix midpoint equal the analytic posterior prevision. -/
theorem posteriorBernoulliMixture_sharedEnvelopeCrown_prefixEnvelopeMidpoint_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    externalPathLawPrefixEnvelopeMidpoint
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X :=
  hCrown.prefixEnvelopeMidpoint_eq_posterior n X

/-- The shared-envelope Crown 2 interface exposes exact PLN-style
midpoint/confidence coordinates on the singleton external posterior prefix
credal slice. -/
theorem posteriorBernoulliMixture_sharedEnvelopeCrown_prefixPLNCoordinates_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    ( externalPathLawPrefixEnvelopeMidpoint
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X
    , externalPathLawPrefixEnvelopeWidthComplement
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X ) =
      ( (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
      , (1 : ℝ) ) :=
  hCrown.prefixPLNCoordinates_eq_posterior n X

/-- The shared-envelope Crown 2 interface exposes exact PLN-style
midpoint/confidence coordinates on the compact bounded-measurable posterior
path carrier. -/
theorem posteriorBernoulliMixture_sharedEnvelopeCrown_compactPLNCoordinates_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A)
    (n : ℕ)
    (X : Gamble (Fin n → Bool)) :
    ( boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n X)
    , boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n X) ) =
      ( (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
      , (1 : ℝ) ) :=
  hCrown.compactPLNCoordinates_eq_posterior n X

/-- The external Boolean process law obtained by conditioning a represented
prior process on an observed finite prefix and then reading its shifted tail.

Positive example: with observed prefix length `m`, the external process's first
coordinate is the original coordinate `m` under the normalized prefix
restriction.  Negative example: this is not a fresh Kolmogorov extension; it is
the explicit conditioned tail carried by an already represented process. -/
noncomputable def conditionedTailExternalBoolProcessLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    ExternalBoolProcessLaw Ω := by
  letI : IsProbabilityMeasure
      (BernoulliMixture.conditionedOnPrefixMeasure μ X obs) :=
    BernoulliMixture.conditionedOnPrefixMeasure_isProbability M X μ hrep obs hZ
  exact ExternalBoolProcessLaw.ofProcess
    (BernoulliMixture.conditionedOnPrefixMeasure μ X obs)
    (BernoulliMixture.tailProcess X m)
    (BernoulliMixture.tailProcess_measurable X m hX)

/-- The conditioned-tail external process law realizes the posterior Bernoulli
mixture induced by the observed prefix. -/
theorem conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    BernoulliMixtureExternalProcessRealization
      (M.posteriorBernoulliMixture (countTrue obs) (countFalse obs) hZ)
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) := by
  unfold conditionedTailExternalBoolProcessLaw
  letI : IsProbabilityMeasure
      (BernoulliMixture.conditionedOnPrefixMeasure μ X obs) :=
    BernoulliMixture.conditionedOnPrefixMeasure_isProbability M X μ hrep obs hZ
  exact
    externalBoolProcessLawOf_realizes_posteriorBernoulliMixture_of_represents
      M (countTrue obs) (countFalse obs) hZ
      (BernoulliMixture.conditionedOnPrefixMeasure μ X obs)
      (BernoulliMixture.tailProcess X m)
      (BernoulliMixture.tailProcess_measurable X m hX)
      (BernoulliMixture.conditionedOnPrefixMeasure_tail_represents_posteriorBernoulliMixture
        M X μ hX hrep obs hZ)

/-- A represented prior process plus a nonzero observed prefix supplies the
posterior external-carrier crown through the conditioned tail process. -/
theorem posteriorBernoulliMixture_conditionedTail_externalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureExternalCarrierCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) := by
  exact posteriorBernoulliMixture_externalCarrierCrown
    M (countTrue obs) (countFalse obs) hZ
    (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ)
    (conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
      M X μ hX hrep obs hZ)

/-- A represented prior process plus a nonzero observed prefix supplies the
posterior update/external-carrier crown through the conditioned tail process. -/
theorem posteriorBernoulliMixture_conditionedTail_updateExternalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureUpdateExternalCarrierCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) := by
  exact posteriorBernoulliMixture_updateExternalCarrierCrown
    M (countTrue obs) (countFalse obs) hZ
    (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ)
    (conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
      M X μ hX hrep obs hZ)

/-- Honest conditioned-tail Crown 2 endpoint.

Starting from a represented prior process and a nonzero observed prefix, the
shifted conditioned tail supplies the external realization consumed by the
unconditional process-envelope crown at the posterior counts
`(countTrue obs, countFalse obs)`. -/
theorem posteriorBernoulliMixture_conditionedTail_processEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureProcessEnvelopeCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) := by
  exact posteriorBernoulliMixture_processEnvelopeCrown
    M (countTrue obs) (countFalse obs) hZ
    (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ)
    (conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
      M X μ hX hrep obs hZ)

/-- Honest conditioned-tail shared-envelope Crown 2 interface.

Starting from a represented prior process and a nonzero observed prefix, the
shifted conditioned tail computes the exact posterior lower, upper, and natural
Walley envelopes on every finite-prefix observable. -/
theorem posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) := by
  exact posteriorBernoulliMixture_sharedEnvelopeCrown
    M (countTrue obs) (countFalse obs) hZ
    (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ)
    (conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
      M X μ hX hrep obs hZ)

/-- After conditioning a represented prior process on a finite observed prefix,
the shifted posterior tail always stays at the exact shared-envelope endpoint,
and the stronger raw all-gambles witness exists exactly in the zero-interior
regime of the underlying prior mixture. -/
theorem posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_prefixWitness_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) ∧
      (posteriorBernoulliMixturePrefixProcessWitness
          M (countTrue obs) (countFalse obs) hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
        M X μ hX hrep obs hZ,
      posteriorBernoulliMixturePrefixProcessWitness_iff_zeroInteriorMixingMass
        M (countTrue obs) (countFalse obs) hZ⟩

/-- Conditioned-tail version of the same exact carrier-witness classification:
the shared-envelope posterior object always exists, while a raw carrier
witness exists exactly in the zero-interior regime. -/
theorem posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) ∧
      ((∃ carrier : CredalPrevisionSet (ℕ → Bool),
          posteriorBernoulliMixturePrefixProcessCarrierWitness
            M (countTrue obs) (countFalse obs) hZ carrier) ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
        M X μ hX hrep obs hZ,
      posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_iff_zeroInteriorMixingMass
        M (countTrue obs) (countFalse obs) hZ⟩

/-- After conditioning a represented prior process on a finite observed prefix,
the shifted posterior tail still lives at the exact shared-envelope endpoint,
while the stronger single-global raw witness remains impossible in the same
nondegenerate interior-mass regime. -/
theorem posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_noPrefixCarrierWitness_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) ∧
      ∀ carrier : CredalPrevisionSet (ℕ → Bool),
        ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness
          M (countTrue obs) (countFalse obs) hZ carrier := by
  refine
    ⟨posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
      M X μ hX hrep obs hZ, ?_⟩
  intro carrier
  exact
    not_posteriorBernoulliMixturePrefixProcessCarrierWitness_of_interiorMixingMass
      M (countTrue obs) (countFalse obs) hZ carrier hInterior

/-- Direct-witness form of the conditioned-tail boundary: after conditioning a
represented prior process on an observed prefix, the shifted tail remains at
the exact shared-envelope endpoint, while the stronger raw global witness is
still impossible in the same interior-mass regime. -/
theorem posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_noPrefixWitness_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness
        M (countTrue obs) (countFalse obs) hZ := by
  refine
    ⟨posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
      M X μ hX hrep obs hZ, ?_⟩
  exact
    not_posteriorBernoulliMixturePrefixProcessWitness_of_interiorMixingMass
      M (countTrue obs) (countFalse obs) hZ hInterior

/-- Conditioned-tail counterpart of the honest sigma-additive witness
boundary: after updating on a finite observed prefix, the shifted posterior
tail itself yields an actual bounded-measurable compact-carrier witness with
exact analytic prefix-cylinder values, while the stronger raw witness remains
impossible in the same nondegenerate interior-mass regime. -/
theorem posteriorBernoulliMixture_conditionedTail_pathBoundedMeasurableCompactWitness_and_noPrefixWitness_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    let A : ExternalBoolProcessLaw Ω :=
      conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ
    A.pathBoundedMeasurablePrevision ∈
        externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)) ∧
      (∀ (n : ℕ) (G : Gamble (Fin n → Bool)),
        A.pathBoundedMeasurablePrevision
            (externalPathLawPrefixBoundedMeasurableGamble n G) =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture
              (countTrue obs) (countFalse obs) hZ) n).toPrecisePrevision G) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness
          M (countTrue obs) (countFalse obs) hZ := by
  let A : ExternalBoolProcessLaw Ω :=
    conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ
  exact
    posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness_and_noPrefixWitness_of_interiorMixingMass
      M (countTrue obs) (countFalse obs) hZ A
      (conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
        M X μ hX hrep obs hZ)
      hInterior

/-- The conditioned posterior tail exposes exact PLN-style midpoint/confidence
coordinates on each singleton finite-prefix credal slice. -/
theorem posteriorBernoulliMixture_conditionedTail_prefixPLNCoordinates_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (n : ℕ)
    (G : Gamble (Fin n → Bool)) :
    ( externalPathLawPrefixEnvelopeMidpoint
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω)) n G
    , externalPathLawPrefixEnvelopeWidthComplement
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω)) n G ) =
      ( (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture
              (countTrue obs) (countFalse obs) hZ) n).toPrecisePrevision G
      , (1 : ℝ) ) := by
  exact
    posteriorBernoulliMixture_sharedEnvelopeCrown_prefixPLNCoordinates_eq_posterior
      (posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
        M X μ hX hrep obs hZ) n G

/-- The conditioned posterior tail exposes exact PLN-style midpoint/confidence
coordinates on the compact bounded-measurable path carrier. -/
theorem posteriorBernoulliMixture_conditionedTail_compactPLNCoordinates_eq_posterior
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (n : ℕ)
    (G : Gamble (Fin n → Bool)) :
    ( boundedMeasurableEnvelopeMidpoint
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
            Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n G)
    , boundedMeasurableEnvelopeWidthComplement
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
            Set (ExternalBoolProcessLaw Ω)))
        (externalPathLawPrefixBoundedMeasurableGamble n G) ) =
      ( (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture
              (countTrue obs) (countFalse obs) hZ) n).toPrecisePrevision G
      , (1 : ℝ) ) := by
  exact
    posteriorBernoulliMixture_sharedEnvelopeCrown_compactPLNCoordinates_eq_posterior
      (posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
        M X μ hX hrep obs hZ) n G

/-- Posterior process-law and conditioned-tail carrier package.

This is the review-facing endpoint that joins the two remaining Crown 2
interfaces: a compact/FIP posterior singleton process-law crown, and the
external posterior carrier obtained by conditioning a represented prior process
on the observed prefix and reading its shifted tail. -/
structure PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) {m : ℕ} (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (μ : Measure Ω) (X : ℕ → Ω → Bool)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) : Prop where
  posteriorProcessLawCrown :
    PosteriorBernoulliMixtureProcessLawCrown
      M (countTrue obs) (countFalse obs) hZ
  conditionedTailRealization :
    BernoulliMixtureExternalProcessRealization
      (M.posteriorBernoulliMixture (countTrue obs) (countFalse obs) hZ)
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ)
  conditionedTailExternalCarrierCrown :
    PosteriorBernoulliMixtureExternalCarrierCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ)
  conditionedTailUpdateExternalCarrierCrown :
    PosteriorBernoulliMixtureUpdateExternalCarrierCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ)

/-- Combined posterior process-law and conditioned-tail carrier package from
the minimal compact finite-window compatibility boundary. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_finiteWindowCompatibleInCarrier
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec
          M (countTrue obs) (countFalse obs) hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec
            M (countTrue obs) (countFalse obs) hZ).localLower n)})
    (hFIP :
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ).finiteWindowCompatibleInCarrier
        carrier) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep where
  posteriorProcessLawCrown :=
    posteriorBernoulliMixture_processLawCrown_of_finiteWindowCompatibleInCarrier
      M (countTrue obs) (countFalse obs) hZ
      carrier hCompact hCarrierConvex hClosed hFIP
  conditionedTailRealization :=
    conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
      M X μ hX hrep obs hZ
  conditionedTailExternalCarrierCrown :=
    posteriorBernoulliMixture_conditionedTail_externalCarrierCrown
      M X μ hX hrep obs hZ
  conditionedTailUpdateExternalCarrierCrown :=
    posteriorBernoulliMixture_conditionedTail_updateExternalCarrierCrown
      M X μ hX hrep obs hZ

/-- Combined posterior process-law and conditioned-tail carrier package from
structured finite joint-window realization data. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_finiteWindowRealization
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec
          M (countTrue obs) (countFalse obs) hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec
            M (countTrue obs) (countFalse obs) hZ).localLower n)})
    (J : ProjectiveLocalLowerPrevisionSpec.FiniteJointWindowSystem
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ))
    (hLocal :
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ).finiteWindowLocalCoherent J)
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ).jointPrevisionsRealizedInCarrier
        J carrier) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep := by
  have hFIP :
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ).finiteWindowCompatibleInCarrier
        carrier :=
    ProjectiveLocalLowerPrevisionSpec.finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ)
      J carrier hLocal hRealize
  exact
    posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_finiteWindowCompatibleInCarrier
      M X μ hX hrep obs hZ carrier hCompact hCarrierConvex hClosed hFIP

/-- Combined posterior process-law and conditioned-tail carrier package from
the canonical largest-prefix finite joint-window system.

This fixes the finite-window system in the combined Crown 2 endpoint to
`posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem`.  The remaining
finite-window assumptions are now exactly local coherence and carrier
realization for that canonical Boolean-prefix joint system. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixFiniteWindowRealization
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec
          M (countTrue obs) (countFalse obs) hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec
            M (countTrue obs) (countFalse obs) hZ).localLower n)})
    (hLocal :
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ).finiteWindowLocalCoherent
        (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
          M (countTrue obs) (countFalse obs) hZ))
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ).jointPrevisionsRealizedInCarrier
        (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
          M (countTrue obs) (countFalse obs) hZ)
        carrier) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep :=
  posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_finiteWindowRealization
    M X μ hX hrep obs hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
      M (countTrue obs) (countFalse obs) hZ)
    hLocal hRealize

/-- Combined posterior process-law and conditioned-tail carrier package from
canonical prefix marginal consistency plus carrier realization.

This is the sharpest conditioned-tail Crown 2 reduction currently exposed:
`hMarginal` is the finite product-sum marginal theorem for the canonical
largest-prefix windows, and `hRealize` is the remaining carrier realization
boundary for those same finite joint previsions. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixMarginalConsistentCarrierRealization
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec
          M (countTrue obs) (countFalse obs) hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec
            M (countTrue obs) (countFalse obs) hZ).localLower n)})
    (hMarginal :
      posteriorBernoulliMixturePrefixProcessMarginalConsistent
        M (countTrue obs) (countFalse obs) hZ)
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ).jointPrevisionsRealizedInCarrier
        (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
          M (countTrue obs) (countFalse obs) hZ)
        carrier) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep :=
  posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixFiniteWindowRealization
    M X μ hX hrep obs hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem_localCoherent_of_marginalConsistent
      M (countTrue obs) (countFalse obs) hZ hMarginal)
    hRealize

/-- Combined posterior process-law and conditioned-tail carrier package from
canonical carrier realization alone.

The finite-prefix marginal theorem for the canonical largest-prefix windows is
now proved internally; the only remaining assumption here is the explicit
carrier realization of those same canonical joint previsions. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixCarrierRealization
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec
          M (countTrue obs) (countFalse obs) hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec
            M (countTrue obs) (countFalse obs) hZ).localLower n)})
    (hRealize :
      (posteriorBernoulliMixturePrefixProcessLowerSpec
        M (countTrue obs) (countFalse obs) hZ).jointPrevisionsRealizedInCarrier
        (posteriorBernoulliMixturePrefixProcessFiniteJointWindowSystem
          M (countTrue obs) (countFalse obs) hZ)
        carrier) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep :=
  posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixMarginalConsistentCarrierRealization
    M X μ hX hrep obs hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcessMarginalConsistent_analytic
      M (countTrue obs) (countFalse obs) hZ)
    hRealize

/-- Combined posterior process-law and conditioned-tail carrier package from a
single global carrier witness for the analytic posterior prefix laws.

As in `posteriorBernoulliMixture_processLawCrown_of_prefixCarrierWitness`, the
auxiliary compactness scaffolding is supplied internally by the singleton
witness carrier, so the visible remaining assumption is just the witness
itself. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixCarrierWitness
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hWitness :
      posteriorBernoulliMixturePrefixProcessCarrierWitness
        M (countTrue obs) (countFalse obs) hZ carrier) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep := by
  rcases hWitness with ⟨P, _hPcarrier, hPmarg⟩
  let carrier' : CredalPrevisionSet (ℕ → Bool) := ({P} : CredalPrevisionSet (ℕ → Bool))
  letI : TopologicalSpace (PrecisePrevision (ℕ → Bool)) := ⊥
  letI : DiscreteTopology (PrecisePrevision (ℕ → Bool)) :=
    discreteTopology_bot (PrecisePrevision (ℕ → Bool))
  have hCompact : IsCompact carrier' := by
    exact isCompact_singleton
  have hCarrierConvex : CredalPrevisionSet.IsConvex carrier' := by
    exact CredalPrevisionSet.isConvex_singleton P
  have hClosed : ∀ n, IsClosed {Q : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec
          M (countTrue obs) (countFalse obs) hZ).cylinders.marginalPrevision
          n Q) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec
            M (countTrue obs) (countFalse obs) hZ).localLower n)} := by
    intro n
    exact isClosed_discrete _
  have hWitness' :
      posteriorBernoulliMixturePrefixProcessCarrierWitness
        M (countTrue obs) (countFalse obs) hZ carrier' := by
    refine ⟨P, ?_, hPmarg⟩
    simp [carrier']
  exact
    posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixCarrierRealization
      M X μ hX hrep obs hZ carrier' hCompact hCarrierConvex hClosed
      (posteriorBernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_carrierWitness
        M (countTrue obs) (countFalse obs) hZ carrier' hWitness')

/-- Combined posterior process-law and conditioned-tail carrier package from
the raw global posterior-process witness itself. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixWitness
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (hWitness :
      posteriorBernoulliMixturePrefixProcessWitness
        M (countTrue obs) (countFalse obs) hZ) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep := by
  rcases hWitness with ⟨P, hPmarg⟩
  exact
    posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixCarrierWitness
      M X μ hX hrep obs hZ ({P} : CredalPrevisionSet (ℕ → Bool))
      ⟨P, by simp, hPmarg⟩

/-- In the zero-interior-mass regime, the raw posterior-process witness exists,
so the full conditioned-tail raw carrier crown follows directly. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (hInterior : M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep := by
  exact
    posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixWitness
      M X μ hX hrep obs hZ
      (posteriorBernoulliMixturePrefixProcessWitness_of_zeroInteriorMixingMass
        M (countTrue obs) (countFalse obs) hZ hInterior)

/-- A conditioned-tail Crown 2 package already contains the raw posterior
process-law crown, hence the raw global posterior-process witness. -/
theorem posteriorBernoulliMixturePrefixProcessWitness_of_conditionedTail_processCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (hCrown :
      PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
        M obs hZ μ X hX hrep) :
    posteriorBernoulliMixturePrefixProcessWitness
      M (countTrue obs) (countFalse obs) hZ :=
  posteriorBernoulliMixturePrefixProcessWitness_of_processLawCrown
    M (countTrue obs) (countFalse obs) hZ hCrown.posteriorProcessLawCrown

/-- Consequently, a conditioned-tail Crown 2 package also forces existence of
some raw carrier witness for the analytic posterior prefix marginals. -/
theorem posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_of_conditionedTail_processCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (hCrown :
      PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
        M obs hZ μ X hX hrep) :
    ∃ carrier : CredalPrevisionSet (ℕ → Bool),
      posteriorBernoulliMixturePrefixProcessCarrierWitness
        M (countTrue obs) (countFalse obs) hZ carrier := by
  exact
    (posteriorBernoulliMixturePrefixProcessWitness_iff_existsCarrierWitness
      M (countTrue obs) (countFalse obs) hZ).mp
      (posteriorBernoulliMixturePrefixProcessWitness_of_conditionedTail_processCarrierCrown
        M X μ hX hrep obs hZ hCrown)

/-- The conditioned-tail Crown 2 package is equivalent to existence of some raw
carrier witness for the analytic posterior prefix marginals. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_iff_exists_prefixCarrierWitness
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep ↔
      ∃ carrier : CredalPrevisionSet (ℕ → Bool),
        posteriorBernoulliMixturePrefixProcessCarrierWitness
          M (countTrue obs) (countFalse obs) hZ carrier := by
  constructor
  · intro hCrown
    exact
      posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_of_conditionedTail_processCarrierCrown
        M X μ hX hrep obs hZ hCrown
  · rintro ⟨carrier, hWitness⟩
    exact
      posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixCarrierWitness
        M X μ hX hrep obs hZ carrier hWitness

/-- Exact regime split for the conditioned-tail Crown 2 package itself: it
exists precisely in the zero-interior-mixing regime. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep ↔
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  constructor
  · intro hCrown
    exact
      (posteriorBernoulliMixturePrefixProcessCarrierWitness_exists_iff_zeroInteriorMixingMass
        M (countTrue obs) (countFalse obs) hZ).mp
        ((posteriorBernoulliMixture_conditionedTail_processCarrierCrown_iff_exists_prefixCarrierWitness
          M X μ hX hrep obs hZ).mp hCrown)
  · intro hInterior
    exact
      posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_zeroInteriorMixingMass
        M X μ hX hrep obs hZ hInterior

/-- Conditioned-tail version of the same honest final boundary package: the
shifted posterior tail gives the exact shared-envelope endpoint, an actual
sigma-additive bounded-measurable witness, and an exact classification of the
stronger raw conditioned-tail process-carrier crown. -/
theorem posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_pathBoundedMeasurableCompactWitness_and_processCarrierCrown_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    let A : ExternalBoolProcessLaw Ω :=
      conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ
    PosteriorBernoulliMixtureSharedEnvelopeCrown
      M (countTrue obs) (countFalse obs) hZ A ∧
      A.pathBoundedMeasurablePrevision ∈
        externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw Ω)) ∧
      (∀ (n : ℕ) (G : Gamble (Fin n → Bool)),
        A.pathBoundedMeasurablePrevision
            (externalPathLawPrefixBoundedMeasurableGamble n G) =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture
              (countTrue obs) (countFalse obs) hZ) n).toPrecisePrevision G) ∧
      (PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
          M obs hZ μ X hX hrep ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  let A : ExternalBoolProcessLaw Ω :=
    conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
        M X μ hX hrep obs hZ
  · exact
      (posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness
        M (countTrue obs) (countFalse obs) hZ A
        (conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
          M X μ hX hrep obs hZ)).1
  · exact
      (posteriorBernoulliMixture_externalPathBoundedMeasurableCompactWitness
        M (countTrue obs) (countFalse obs) hZ A
        (conditionedTailExternalBoolProcessLaw_realizes_posteriorBernoulliMixture
          M X μ hX hrep obs hZ)).2
  · exact
      posteriorBernoulliMixture_conditionedTail_processCarrierCrown_iff_zeroInteriorMixingMass
        M X μ hX hrep obs hZ

/-- Conditioned-tail version of the same exact crown-level split: the
shared-envelope posterior object always exists, while the stronger raw
conditioned-tail process-carrier crown exists exactly in the zero-interior
regime. -/
theorem posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_processCarrierCrown_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0) :
    PosteriorBernoulliMixtureSharedEnvelopeCrown
      M (countTrue obs) (countFalse obs) hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) ∧
      (PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
          M obs hZ μ X hX hrep ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
        M X μ hX hrep obs hZ,
      posteriorBernoulliMixture_conditionedTail_processCarrierCrown_iff_zeroInteriorMixingMass
        M X μ hX hrep obs hZ⟩

/-- In the nondegenerate interior-mass regime, the stronger conditioned-tail
raw process-carrier crown is impossible. -/
theorem not_posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    ¬ PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep := by
  intro hCrown
  have hZero :
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 :=
    (posteriorBernoulliMixture_conditionedTail_processCarrierCrown_iff_zeroInteriorMixingMass
      M X μ hX hrep obs hZ).mp hCrown
  have hNot :
      ¬ 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1) := by
    rw [hZero]
    exact lt_irrefl 0
  exact hNot hInterior

/-- Combined posterior process-law and conditioned-tail carrier package from
any compact/convex/closed raw carrier containing the explicit tail-false
finite-window realizers. -/
theorem posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixTailFalseExtensionCarrierSubset
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ : M.countEvidenceMass (countTrue obs) (countFalse obs) ≠ 0)
    [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
    (carrier : CredalPrevisionSet (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
      ((posteriorBernoulliMixturePrefixProcessLowerSpec
          M (countTrue obs) (countFalse obs) hZ).cylinders.marginalPrevision
          n P) ∈
        dominatingPreciseCompletions
          ((posteriorBernoulliMixturePrefixProcessLowerSpec
            M (countTrue obs) (countFalse obs) hZ).localLower n)})
    (hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) :
    PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
      M obs hZ μ X hX hrep :=
  posteriorBernoulliMixture_conditionedTail_processCarrierCrown_of_prefixCarrierRealization
    M X μ hX hrep obs hZ carrier hCompact hCarrierConvex hClosed
    (posteriorBernoulliMixturePrefixProcess_jointPrevisionsRealizedInCarrier_of_prefixTailFalseExtensionCarrierSubset
      M (countTrue obs) (countFalse obs) hZ carrier hSubset)

/-! ## Profile surface -/

/-- Proof-carrying profile for the de Finetti face of the shared projective
credal abstraction. -/
structure ProjectiveDeFinettiCredalBridgeProfile where
  analyticPrefixLaw :
    ∀ (M : BernoulliMixture) (n : ℕ),
      BernoulliMixturePrefixLaw M n
  prefixLawIffFiniteWeights :
    ∀ (M : BernoulliMixture) (n : ℕ),
      BernoulliMixturePrefixLaw M n ↔
        ∃ w : PrecisePrevision.FiniteWeights (Fin n → Bool),
          ∀ xs : Fin n → Bool, w.weight xs = M.prob xs
  externalIIDProductPrefixMeasureEqProduct :
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ),
      (Exchangeability.Probability.iidProduct ν).map
          (Exchangeability.prefixProj (α := Bool) n) =
        Measure.pi fun _ : Fin n => ν
  externalIIDProductPrefixPrevisionIsPrecise :
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ),
      (externalIIDProductPrefixPrevision ν n).toLowerPrevision.isPrecise
  externalPathLawPrefixMeasureEqProcessPrefix :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (X : ℕ → Ω → Bool)
      (_hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ),
      Measure.map (Exchangeability.prefixProj (α := Bool) n)
          (Exchangeability.pathLaw (α := Bool) μ X) =
        Measure.map (fun ω => fun i : Fin n => X i ω) μ
  externalPathLawPrefixCylinderApply :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (X : ℕ → Ω → Bool)
      (_hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ)
      (S : Set (Fin n → Bool)) (_hS : MeasurableSet S),
      Exchangeability.pathLaw (α := Bool) μ X
          (Exchangeability.prefixCylinder (α := Bool) S) =
        Measure.map (fun ω => fun i : Fin n => X i ω) μ S
  externalPathLawPrefixPrevisionIsPrecise :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Bool) (_hX : ∀ i : ℕ, Measurable (X i)) (n : ℕ),
      (externalPathLawPrefixPrevision μ X _hX n).toLowerPrevision.isPrecise
  externalProcessPrefixPrevisionIsPrecise :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (_A : ExternalBoolProcessLaw Ω) (n : ℕ),
      (_A.prefixPrevision n).toLowerPrevision.isPrecise
  externalProcessPrefixCylinderApply :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (_A : ExternalBoolProcessLaw Ω) (n : ℕ)
      (S : Set (Fin n → Bool)) (_hS : MeasurableSet S),
      Exchangeability.pathLaw (α := Bool) _A.μ _A.X
          (Exchangeability.prefixCylinder (α := Bool) S) =
        Measure.map (fun ω => fun i : Fin n => _A.X i ω) _A.μ S
  externalPathLawPrefixCredalSetNonempty :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      C.Nonempty → (externalPathLawPrefixCredalSet C n).Nonempty
  externalPathLawPrefixProjectiveSpecLimitSet :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      (externalPathLawPrefixProjectiveSpec C n).projectiveLimitCredalSet =
        externalPathLawPrefixCredalSet C n
  externalPathLawPrefixProjectiveSpecHasCompatibleCompletion :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      C.Nonempty →
        (externalPathLawPrefixProjectiveSpec C n).hasCompatibleCompletion
  externalPathLawPrefixProjectiveSpecNaturalExtensionEqLowerEnvelope :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec C n).globalNaturalExtension X =
        externalPathLawPrefixLowerEnvelope C n X
  externalPathLawPrefixLowerEnvelopeLeProcess :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      {A : ExternalBoolProcessLaw Ω},
      A ∈ C →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        externalPathLawPrefixLowerEnvelope C n X ≤ A.prefixPrevision n X
  externalPathLawPrefixLowerEnvelopeGreatestLowerBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      C.Nonempty →
      ∀ L : LowerPrevision (Fin n → Bool),
      (∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
          (Fin n → Bool), L X ≤ A.prefixPrevision n X) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        L X ≤ externalPathLawPrefixLowerEnvelope C n X
  externalPathLawPrefixProjectiveSpecUpperEnvelopeEqUpperEnvelope :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      upperEnvelope
          (externalPathLawPrefixProjectiveSpec C n).projectiveLimitCredalSet X =
        externalPathLawPrefixUpperEnvelope C n X
  externalPathLawPrefixProjectiveSpecWidthEqEnvelopeWidth :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidth X =
        externalPathLawPrefixEnvelopeWidth C n X
  externalPathLawPrefixProjectiveSpecWidthComplementEqEnvelopeWidthComplement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeWidthComplement X =
        externalPathLawPrefixEnvelopeWidthComplement C n X
  externalPathLawPrefixProjectiveSpecMidpointEqEnvelopeMidpoint :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (externalPathLawPrefixProjectiveSpec C n).globalEnvelopeMidpoint X =
        externalPathLawPrefixEnvelopeMidpoint C n X
  externalPathLawPrefixPrevisionLeUpperEnvelope :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      {A : ExternalBoolProcessLaw Ω},
      A ∈ C →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        A.prefixPrevision n X ≤ externalPathLawPrefixUpperEnvelope C n X
  externalPathLawPrefixUpperEnvelopeLeastUpperBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ),
      C.Nonempty →
      ∀ U : UpperPrevision (Fin n → Bool),
      (∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
          (Fin n → Bool), A.prefixPrevision n X ≤ U X) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        externalPathLawPrefixUpperEnvelope C n X ≤ U X
  externalPathLawBoundedNaturalExtensionLeProcess :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ {A : ExternalBoolProcessLaw Ω}, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCredalSet C)
            (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X ≤
          A.pathBoundedMeasurablePrevision X
  externalPathLawBoundedNaturalExtensionGreatestLowerBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ L : BoundedMeasurableLowerPrevision (ℕ → Bool),
      (∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
        ∀ X : BoundedMeasurableGamble (ℕ → Bool),
          L X ≤ A.pathBoundedMeasurablePrevision X) →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        L X ≤
          boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCredalSet C)
            (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X
  externalPathLawBoundedNaturalUpperEnvelopeProcessLe :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ {A : ExternalBoolProcessLaw Ω}, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        A.pathBoundedMeasurablePrevision X ≤
          boundedMeasurableNaturalUpperEnvelopePrevision
            (externalPathLawBoundedMeasurableCredalSet C)
            (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X
  externalPathLawBoundedNaturalUpperEnvelopeLeastUpperBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ U : BoundedMeasurableUpperPrevision (ℕ → Bool),
      (∀ A : ExternalBoolProcessLaw Ω, A ∈ C →
        ∀ X : BoundedMeasurableGamble (ℕ → Bool),
          A.pathBoundedMeasurablePrevision X ≤ U X) →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        boundedMeasurableNaturalUpperEnvelopePrevision
            (externalPathLawBoundedMeasurableCredalSet C)
            (externalPathLawBoundedMeasurableCredalSet_nonempty C hC) X ≤
          U X
  externalPathLawCompactBoundedNaturalExtensionLeProcess :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ {A : ExternalBoolProcessLaw Ω}, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCompactCredalSet C)
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC) X ≤
          A.pathBoundedMeasurablePrevision X
  externalPathLawCompactBoundedNaturalUpperEnvelopeProcessLe :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)),
      (hC : C.Nonempty) →
      ∀ {A : ExternalBoolProcessLaw Ω}, A ∈ C →
      ∀ X : BoundedMeasurableGamble (ℕ → Bool),
        A.pathBoundedMeasurablePrevision X ≤
          boundedMeasurableNaturalUpperEnvelopePrevision
            (externalPathLawBoundedMeasurableCompactCredalSet C)
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty C hC) X
  canonicalExternalBoolProcessLaw :
    BernoulliMixture → ExternalBoolProcessLaw (ℕ → Bool)
  canonicalExternalProcessRealization :
    ∀ (M : BernoulliMixture),
      BernoulliMixtureExternalProcessRealization M
        (canonicalExternalBoolProcessLaw M)
  canonicalExternalBoolProcessLawSetPrefixCredalSetEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture) (n : ℕ),
      externalPathLawPrefixCredalSet
          ({A | ∃ M : BernoulliMixture, M ∈ C ∧
            A = canonicalExternalBoolProcessLaw M}) n =
        bernoulliMixturePrefixCredalSet C n
          (fun M _ => analyticPrefixLaw M n)
  canonicalExternalBoolProcessLawSetPrefixLowerEnvelopeEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture), C.Nonempty →
      ∀ (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
        externalPathLawPrefixLowerEnvelope
            ({A | ∃ M : BernoulliMixture, M ∈ C ∧
              A = canonicalExternalBoolProcessLaw M}) n X =
          impreciseDeFinettiPrefixLowerEnvelope C n
            (fun M _ => analyticPrefixLaw M n) X
  canonicalExternalBoolProcessLawSetPrefixUpperEnvelopeEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture), C.Nonempty →
      ∀ (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
        externalPathLawPrefixUpperEnvelope
            ({A | ∃ M : BernoulliMixture, M ∈ C ∧
              A = canonicalExternalBoolProcessLaw M}) n X =
          impreciseDeFinettiPrefixUpperEnvelope C n
            (fun M _ => analyticPrefixLaw M n) X
  canonicalExternalBoolProcessLawSetPrefixWidthComplementEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture), C.Nonempty →
      ∀ (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
        externalPathLawPrefixEnvelopeWidthComplement
            ({A | ∃ M : BernoulliMixture, M ∈ C ∧
              A = canonicalExternalBoolProcessLaw M}) n X =
          impreciseDeFinettiPrefixEnvelopeWidthComplement C n
            (fun M _ => analyticPrefixLaw M n) X
  canonicalExternalBoolProcessLawSetPrefixMidpointEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture), C.Nonempty →
      ∀ (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
        externalPathLawPrefixEnvelopeMidpoint
            ({A | ∃ M : BernoulliMixture, M ∈ C ∧
              A = canonicalExternalBoolProcessLaw M}) n X =
          impreciseDeFinettiPrefixEnvelopeMidpoint C n
            (fun M _ => analyticPrefixLaw M n) X
  canonicalExternalBoolProcessLawSetCompactNaturalExtensionPrefixEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture), (hC : C.Nonempty) →
      ∀ (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
        boundedMeasurableNaturalExtensionPrevision
            (externalPathLawBoundedMeasurableCompactCredalSet
              ({A | ∃ M : BernoulliMixture, M ∈ C ∧
                A = canonicalExternalBoolProcessLaw M}))
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
              ({A | ∃ M : BernoulliMixture, M ∈ C ∧
                A = canonicalExternalBoolProcessLaw M})
              (by
                rcases hC with ⟨M, hM⟩
                exact ⟨canonicalExternalBoolProcessLaw M, ⟨M, hM, rfl⟩⟩))
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          impreciseDeFinettiPrefixLowerEnvelope C n
            (fun M _ => analyticPrefixLaw M n) X
  canonicalExternalBoolProcessLawSetCompactNaturalUpperEnvelopePrefixEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture), (hC : C.Nonempty) →
      ∀ (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
        boundedMeasurableNaturalUpperEnvelopePrevision
            (externalPathLawBoundedMeasurableCompactCredalSet
              ({A | ∃ M : BernoulliMixture, M ∈ C ∧
                A = canonicalExternalBoolProcessLaw M}))
            (externalPathLawBoundedMeasurableCompactCredalSet_nonempty
              ({A | ∃ M : BernoulliMixture, M ∈ C ∧
                A = canonicalExternalBoolProcessLaw M})
              (by
                rcases hC with ⟨M, hM⟩
                exact ⟨canonicalExternalBoolProcessLaw M, ⟨M, hM, rfl⟩⟩))
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          impreciseDeFinettiPrefixUpperEnvelope C n
            (fun M _ => analyticPrefixLaw M n) X
  canonicalExternalBoolProcessLawSetCompactWidthComplementPrefixEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture), (hC : C.Nonempty) →
      ∀ (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
        boundedMeasurableEnvelopeWidthComplement
            (externalPathLawBoundedMeasurableCompactCredalSet
              ({A | ∃ M : BernoulliMixture, M ∈ C ∧
                A = canonicalExternalBoolProcessLaw M}))
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          impreciseDeFinettiPrefixEnvelopeWidthComplement C n
            (fun M _ => analyticPrefixLaw M n) X
  canonicalExternalBoolProcessLawSetCompactMidpointPrefixEqImpreciseDeFinetti :
    ∀ (C : Set BernoulliMixture), (hC : C.Nonempty) →
      ∀ (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
        boundedMeasurableEnvelopeMidpoint
            (externalPathLawBoundedMeasurableCompactCredalSet
              ({A | ∃ M : BernoulliMixture, M ∈ C ∧
                A = canonicalExternalBoolProcessLaw M}))
            (externalPathLawPrefixBoundedMeasurableGamble n X) =
          impreciseDeFinettiPrefixEnvelopeMidpoint C n
            (fun M _ => analyticPrefixLaw M n) X
  externalPathLawPrefixProjectiveDeterminesOfProcessAgreement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (∀ A : ExternalBoolProcessLaw Ω, ∀ _hA : A ∈ C,
        ∀ B : ExternalBoolProcessLaw Ω, ∀ _hB : B ∈ C,
          A.prefixPrevision n X = B.prefixPrevision n X) →
        (externalPathLawPrefixProjectiveSpec C n).determinesGlobalGamble X
  externalPathLawPrefixProjectiveStrictWidthOfProcessDisagreement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {A B : ExternalBoolProcessLaw Ω} (_hA : A ∈ C) (_hB : B ∈ C),
      A.prefixPrevision n X < B.prefixPrevision n X →
        (externalPathLawPrefixProjectiveSpec C n).hasStrictGlobalWidth X
  externalPathLawPrefixCredalSetEnvelopeNontrivialOfProcessDisagreement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {A B : ExternalBoolProcessLaw Ω} (_hA : A ∈ C) (_hB : B ∈ C),
      A.prefixPrevision n X < B.prefixPrevision n X →
        lowerEnvelope (externalPathLawPrefixCredalSet C n) X <
          upperEnvelope (externalPathLawPrefixCredalSet C n) X
  externalPathLawPrefixCredalSetWidthPositiveOfProcessDisagreement :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : Set (ExternalBoolProcessLaw Ω)) (n : ℕ)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {A B : ExternalBoolProcessLaw Ω} (_hA : A ∈ C) (_hB : B ∈ C),
      A.prefixPrevision n X < B.prefixPrevision n X →
        0 < credalEnvelopeWidth (externalPathLawPrefixCredalSet C n) X
  prefixMixturePrevisionIsPrecise :
    ∀ (M : BernoulliMixture) (n : ℕ)
      (_h : BernoulliMixturePrefixLaw M n),
      _h.toPrecisePrevision.toLowerPrevision.isPrecise
  imprecisePrefixCredalSetNonempty :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      C.Nonempty →
        (bernoulliMixturePrefixCredalSet C n _hLaw).Nonempty
  prefixProjectiveSpecLimitSet :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).projectiveLimitCredalSet =
        bernoulliMixturePrefixCredalSet C n _hLaw
  prefixProjectiveSpecHasCompatibleCompletion :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      C.Nonempty →
        (bernoulliMixturePrefixProjectiveSpec C n _hLaw).hasCompatibleCompletion
  prefixProjectiveSpecNaturalExtensionEqLowerEnvelope :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).globalNaturalExtension X =
        impreciseDeFinettiPrefixLowerEnvelope C n _hLaw X
  imprecisePrefixLowerEnvelopeLeMixture :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      {M : BernoulliMixture},
      (hM : M ∈ C) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        impreciseDeFinettiPrefixLowerEnvelope C n _hLaw X ≤
          (_hLaw M hM).toPrecisePrevision X
  imprecisePrefixLowerEnvelopeGreatestLowerBound :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      C.Nonempty →
      ∀ L : LowerPrevision (Fin n → Bool),
      (∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
          (Fin n → Bool), L X ≤ (_hLaw M hM).toPrecisePrevision X) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        L X ≤ impreciseDeFinettiPrefixLowerEnvelope C n _hLaw X
  prefixProjectiveSpecUpperEnvelopeEqUpperEnvelope :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      upperEnvelope
          (bernoulliMixturePrefixProjectiveSpec C n _hLaw).projectiveLimitCredalSet X =
        impreciseDeFinettiPrefixUpperEnvelope C n _hLaw X
  prefixProjectiveSpecWidthEqEnvelopeWidth :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).globalEnvelopeWidth X =
        impreciseDeFinettiPrefixEnvelopeWidth C n _hLaw X
  prefixProjectiveSpecWidthComplementEqEnvelopeWidthComplement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).globalEnvelopeWidthComplement X =
        impreciseDeFinettiPrefixEnvelopeWidthComplement C n _hLaw X
  prefixProjectiveSpecMidpointEqEnvelopeMidpoint :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (bernoulliMixturePrefixProjectiveSpec C n _hLaw).globalEnvelopeMidpoint X =
        impreciseDeFinettiPrefixEnvelopeMidpoint C n _hLaw X
  imprecisePrefixPrevisionLeUpperEnvelope :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      {M : BernoulliMixture},
      (hM : M ∈ C) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        (_hLaw M hM).toPrecisePrevision X ≤
          impreciseDeFinettiPrefixUpperEnvelope C n _hLaw X
  imprecisePrefixUpperEnvelopeLeastUpperBound :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n),
      C.Nonempty →
      ∀ U : UpperPrevision (Fin n → Bool),
      (∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
          (Fin n → Bool), (_hLaw M hM).toPrecisePrevision X ≤ U X) →
      ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool),
        impreciseDeFinettiPrefixUpperEnvelope C n _hLaw X ≤ U X
  prefixProjectiveDeterminesOfMixtureAgreement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool)),
      (∀ M : BernoulliMixture, ∀ hM : M ∈ C,
        ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
          (_hLaw M hM).toPrecisePrevision X =
            (_hLaw N hN).toPrecisePrevision X) →
        (bernoulliMixturePrefixProjectiveSpec C n _hLaw).determinesGlobalGamble X
  prefixProjectiveStrictWidthOfMixtureDisagreement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (_hLaw M _hM).toPrecisePrevision X <
        (_hLaw N _hN).toPrecisePrevision X →
        (bernoulliMixturePrefixProjectiveSpec C n _hLaw).hasStrictGlobalWidth X
  prefixCredalSetEnvelopeNontrivialOfMixtureDisagreement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (_hLaw M _hM).toPrecisePrevision X <
        (_hLaw N _hN).toPrecisePrevision X →
        lowerEnvelope (bernoulliMixturePrefixCredalSet C n _hLaw) X <
          upperEnvelope (bernoulliMixturePrefixCredalSet C n _hLaw) X
  prefixCredalSetWidthPositiveOfMixtureDisagreement :
    ∀ (C : Set BernoulliMixture) (n : ℕ)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        BernoulliMixturePrefixLaw M n)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      {M N : BernoulliMixture} (_hM : M ∈ C) (_hN : N ∈ C),
      (_hLaw M _hM).toPrecisePrevision X <
        (_hLaw N _hN).toPrecisePrevision X →
        0 < credalEnvelopeWidth (bernoulliMixturePrefixCredalSet C n _hLaw) X
  prefixProcessFiniteJointWindowSystemLocalCoherentOfMarginalConsistent :
    ∀ (C : Set BernoulliMixture)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        ∀ n : ℕ, BernoulliMixturePrefixLaw M n)
      (_hC : C.Nonempty),
      bernoulliMixturePrefixProcessMarginalConsistent C _hLaw →
        (bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).finiteWindowLocalCoherent
          (bernoulliMixturePrefixProcessFiniteJointWindowSystem C _hLaw _hC)
  prefixProcessFiniteWindowCompatibleInCarrierOfMarginalConsistentCarrierRealization :
    ∀ (C : Set BernoulliMixture)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        ∀ n : ℕ, BernoulliMixturePrefixLaw M n)
      (_hC : C.Nonempty)
      (carrier : CredalPrevisionSet (ℕ → Bool)),
      bernoulliMixturePrefixProcessMarginalConsistent C _hLaw →
        (bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).jointPrevisionsRealizedInCarrier
          (bernoulliMixturePrefixProcessFiniteJointWindowSystem C _hLaw _hC)
          carrier →
          (bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).finiteWindowCompatibleInCarrier
            carrier
  processLawCompatibleCompletionOfPrefixMarginalConsistentCarrierRealization :
    ∀ (C : Set BernoulliMixture)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        ∀ n : ℕ, BernoulliMixturePrefixLaw M n)
      (_hC : C.Nonempty)
      [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
      (carrier : CredalPrevisionSet (ℕ → Bool))
      (_hCompact : IsCompact carrier)
      (_hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
      (_hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
        ((bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).cylinders.marginalPrevision
            n P) ∈
          dominatingPreciseCompletions
            ((bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).localLower n)}),
      bernoulliMixturePrefixProcessMarginalConsistent C _hLaw →
        (bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).jointPrevisionsRealizedInCarrier
          (bernoulliMixturePrefixProcessFiniteJointWindowSystem C _hLaw _hC)
          carrier →
          ((bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).toCredalSpec).hasCompatibleCompletion
  processLawCrownOfPrefixMarginalConsistentCarrierRealization :
    ∀ (C : Set BernoulliMixture)
      (_hLaw : ∀ M : BernoulliMixture, M ∈ C →
        ∀ n : ℕ, BernoulliMixturePrefixLaw M n)
      (_hC : C.Nonempty)
      [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
      (carrier : CredalPrevisionSet (ℕ → Bool))
      (_hCompact : IsCompact carrier)
      (_hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
      (_hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
        ((bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).cylinders.marginalPrevision
            n P) ∈
          dominatingPreciseCompletions
            ((bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).localLower n)}),
      bernoulliMixturePrefixProcessMarginalConsistent C _hLaw →
        (bernoulliMixturePrefixProcessLowerSpec C _hLaw _hC).jointPrevisionsRealizedInCarrier
          (bernoulliMixturePrefixProcessFiniteJointWindowSystem C _hLaw _hC)
          carrier →
          ImpreciseDeFinettiProcessLawCrown C _hLaw _hC
  analyticMixingFamilyProcessLawCrownOfPrefixFiniteWindowRealization :
    ∀ (C : Set BernoulliMixture)
      (_hC : C.Nonempty)
      [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
      (carrier : CredalPrevisionSet (ℕ → Bool))
      (_hCompact : IsCompact carrier)
      (_hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
      (_hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
        ((bernoulliMixturePrefixProcessLowerSpec
            C (fun M _ n => analyticPrefixLaw M n) _hC).cylinders.marginalPrevision
            n P) ∈
          dominatingPreciseCompletions
            ((bernoulliMixturePrefixProcessLowerSpec
                C (fun M _ n => analyticPrefixLaw M n) _hC).localLower n)}),
      (_hRealize :
        (bernoulliMixturePrefixProcessLowerSpec
          C (fun M _ n => analyticPrefixLaw M n) _hC).jointPrevisionsRealizedInCarrier
          (bernoulliMixturePrefixProcessFiniteJointWindowSystem
            C (fun M _ n => analyticPrefixLaw M n) _hC)
          carrier) →
          ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C _hC
  analyticMixingFamilyProcessLawCrownOfPrefixTailFalseExtensionCarrierSubset :
    ∀ (C : Set BernoulliMixture)
      (_hC : C.Nonempty)
      [TopologicalSpace (PrecisePrevision (ℕ → Bool))]
      (carrier : CredalPrevisionSet (ℕ → Bool))
      (_hCompact : IsCompact carrier)
      (_hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
      (_hClosed : ∀ n, IsClosed {P : PrecisePrevision (ℕ → Bool) |
        ((bernoulliMixturePrefixProcessLowerSpec
            C (fun M _ n => analyticPrefixLaw M n) _hC).cylinders.marginalPrevision
            n P) ∈
          dominatingPreciseCompletions
            ((bernoulliMixturePrefixProcessLowerSpec
                C (fun M _ n => analyticPrefixLaw M n) _hC).localLower n)}),
      (_hSubset : prefixTailFalseExtensionCarrier ⊆ carrier) →
          ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown C _hC
  hasCompatibleCompletionOfFactorization :
    ∀ {Ω Window Global : Type*} [MeasurableSpace Ω] [LE Window]
      {X : ℕ → Ω → Bool} {μ : Measure Ω}
      (_D : DeFinettiProjectiveCredalSpecialization
        (Window := Window) (Global := Global) X μ),
      CategoricalDeFinettiFactorization X μ →
        _D.projectiveSpec.hasCompatibleCompletion
  hasCompatibleCompletionOfExchangeable :
    ∀ {Ω Window Global : Type*} [MeasurableSpace Ω] [LE Window]
      {X : ℕ → Ω → Bool} {μ : Measure Ω}
      (_D : DeFinettiProjectiveCredalSpecialization
        (Window := Window) (Global := Global) X μ)
      [IsProbabilityMeasure μ],
      (∀ i : ℕ, Measurable (X i)) →
        InfiniteExchangeable X μ →
          _D.projectiveSpec.hasCompatibleCompletion

/-- Current de Finetti projective credal bridge profile. -/
noncomputable def projectiveDeFinettiCredalBridgeProfile :
    ProjectiveDeFinettiCredalBridgeProfile where
  analyticPrefixLaw :=
    bernoulliMixturePrefixLaw_analytic
  prefixLawIffFiniteWeights :=
    bernoulliMixturePrefixLaw_iff_finiteWeights
  externalIIDProductPrefixMeasureEqProduct :=
    externalIIDProductPrefixMeasure_eq_product
  externalIIDProductPrefixPrevisionIsPrecise :=
    externalIIDProductPrefixPrevision_precise
  externalPathLawPrefixMeasureEqProcessPrefix :=
    externalPathLawPrefixMeasure_eq_processPrefix
  externalPathLawPrefixCylinderApply :=
    externalPathLawPrefixCylinder_apply
  externalPathLawPrefixPrevisionIsPrecise :=
    externalPathLawPrefixPrevision_precise
  externalProcessPrefixPrevisionIsPrecise :=
    ExternalBoolProcessLaw.prefixPrevision_precise
  externalProcessPrefixCylinderApply :=
    ExternalBoolProcessLaw.prefixCylinder_apply
  externalPathLawPrefixCredalSetNonempty :=
    externalPathLawPrefixCredalSet_nonempty
  externalPathLawPrefixProjectiveSpecLimitSet :=
    externalPathLawPrefixProjectiveSpec_projectiveLimitCredalSet
  externalPathLawPrefixProjectiveSpecHasCompatibleCompletion :=
    externalPathLawPrefixProjectiveSpec_hasCompatibleCompletion
  externalPathLawPrefixProjectiveSpecNaturalExtensionEqLowerEnvelope :=
    externalPathLawPrefixProjectiveSpec_globalNaturalExtension
  externalPathLawPrefixLowerEnvelopeLeProcess :=
    externalPathLawPrefixLowerEnvelope_le_processPrevision
  externalPathLawPrefixLowerEnvelopeGreatestLowerBound :=
    externalPathLawPrefixLowerEnvelope_greatest_lower_bound
  externalPathLawPrefixProjectiveSpecUpperEnvelopeEqUpperEnvelope :=
    externalPathLawPrefixProjectiveSpec_upperEnvelope
  externalPathLawPrefixProjectiveSpecWidthEqEnvelopeWidth :=
    externalPathLawPrefixProjectiveSpec_globalEnvelopeWidth
  externalPathLawPrefixProjectiveSpecWidthComplementEqEnvelopeWidthComplement :=
    externalPathLawPrefixProjectiveSpec_globalEnvelopeWidthComplement
  externalPathLawPrefixProjectiveSpecMidpointEqEnvelopeMidpoint :=
    externalPathLawPrefixProjectiveSpec_globalEnvelopeMidpoint
  externalPathLawPrefixPrevisionLeUpperEnvelope :=
    externalPathLawPrefixPrevision_le_upperEnvelope
  externalPathLawPrefixUpperEnvelopeLeastUpperBound :=
    externalPathLawPrefixUpperEnvelope_least_upper_bound
  externalPathLawBoundedNaturalExtensionLeProcess :=
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_le_processPrevision
  externalPathLawBoundedNaturalExtensionGreatestLowerBound :=
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCredalSet_greatest_lower_bound
  externalPathLawBoundedNaturalUpperEnvelopeProcessLe :=
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_processPrevision_le
  externalPathLawBoundedNaturalUpperEnvelopeLeastUpperBound :=
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCredalSet_least_upper_bound
  externalPathLawCompactBoundedNaturalExtensionLeProcess :=
    boundedMeasurableNaturalExtensionPrevision_externalPathLawCompactCredalSet_le_processPrevision
  externalPathLawCompactBoundedNaturalUpperEnvelopeProcessLe :=
    boundedMeasurableNaturalUpperEnvelopePrevision_externalPathLawCompactCredalSet_processPrevision_le
  canonicalExternalBoolProcessLaw :=
    bernoulliMixtureCanonicalExternalBoolProcessLaw
  canonicalExternalProcessRealization :=
    bernoulliMixtureCanonicalExternalProcessRealization
  canonicalExternalBoolProcessLawSetPrefixCredalSetEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixCredalSet_eq_impreciseDeFinetti
  canonicalExternalBoolProcessLawSetPrefixLowerEnvelopeEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixLowerEnvelope_eq_impreciseDeFinetti
  canonicalExternalBoolProcessLawSetPrefixUpperEnvelopeEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixUpperEnvelope_eq_impreciseDeFinetti
  canonicalExternalBoolProcessLawSetPrefixWidthComplementEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixWidthComplement_eq_impreciseDeFinetti
  canonicalExternalBoolProcessLawSetPrefixMidpointEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_prefixMidpoint_eq_impreciseDeFinetti
  canonicalExternalBoolProcessLawSetCompactNaturalExtensionPrefixEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactNaturalExtension_prefix_eq_impreciseDeFinetti
  canonicalExternalBoolProcessLawSetCompactNaturalUpperEnvelopePrefixEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactNaturalUpperEnvelope_prefix_eq_impreciseDeFinetti
  canonicalExternalBoolProcessLawSetCompactWidthComplementPrefixEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactWidthComplement_prefix_eq_impreciseDeFinetti
  canonicalExternalBoolProcessLawSetCompactMidpointPrefixEqImpreciseDeFinetti :=
    bernoulliMixtureCanonicalExternalBoolProcessLawSet_compactMidpoint_prefix_eq_impreciseDeFinetti
  externalPathLawPrefixProjectiveDeterminesOfProcessAgreement :=
    externalPathLawPrefixProjectiveSpec_determinesGlobalGamble_of_processAgreement
  externalPathLawPrefixProjectiveStrictWidthOfProcessDisagreement :=
    externalPathLawPrefixProjectiveSpec_hasStrictGlobalWidth_of_processDisagreement
  externalPathLawPrefixCredalSetEnvelopeNontrivialOfProcessDisagreement :=
    externalPathLawPrefixCredalSet_lowerUpperEnvelope_nontrivial_of_processDisagreement
  externalPathLawPrefixCredalSetWidthPositiveOfProcessDisagreement :=
    externalPathLawPrefixCredalSet_envelopeWidth_pos_of_processDisagreement
  prefixMixturePrevisionIsPrecise :=
    by
      intro M n h
      exact BernoulliMixturePrefixLaw.toPrecisePrevision_precise h
  imprecisePrefixCredalSetNonempty :=
    bernoulliMixturePrefixCredalSet_nonempty
  prefixProjectiveSpecLimitSet :=
    bernoulliMixturePrefixProjectiveSpec_projectiveLimitCredalSet
  prefixProjectiveSpecHasCompatibleCompletion :=
    bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
  prefixProjectiveSpecNaturalExtensionEqLowerEnvelope :=
    bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension
  imprecisePrefixLowerEnvelopeLeMixture :=
    impreciseDeFinettiPrefixLowerEnvelope_le_mixturePrevision
  imprecisePrefixLowerEnvelopeGreatestLowerBound :=
    impreciseDeFinettiPrefixLowerEnvelope_greatest_lower_bound
  prefixProjectiveSpecUpperEnvelopeEqUpperEnvelope :=
    bernoulliMixturePrefixProjectiveSpec_upperEnvelope
  prefixProjectiveSpecWidthEqEnvelopeWidth :=
    bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth
  prefixProjectiveSpecWidthComplementEqEnvelopeWidthComplement :=
    bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement
  prefixProjectiveSpecMidpointEqEnvelopeMidpoint :=
    bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint
  imprecisePrefixPrevisionLeUpperEnvelope :=
    impreciseDeFinettiPrefixPrevision_le_upperEnvelope
  imprecisePrefixUpperEnvelopeLeastUpperBound :=
    impreciseDeFinettiPrefixUpperEnvelope_least_upper_bound
  prefixProjectiveDeterminesOfMixtureAgreement :=
    bernoulliMixturePrefixProjectiveSpec_determinesGlobalGamble_of_mixtureAgreement
  prefixProjectiveStrictWidthOfMixtureDisagreement :=
    bernoulliMixturePrefixProjectiveSpec_hasStrictGlobalWidth_of_mixtureDisagreement
  prefixCredalSetEnvelopeNontrivialOfMixtureDisagreement :=
    bernoulliMixturePrefixCredalSet_lowerUpperEnvelope_nontrivial_of_mixtureDisagreement
  prefixCredalSetWidthPositiveOfMixtureDisagreement :=
    bernoulliMixturePrefixCredalSet_envelopeWidth_pos_of_mixtureDisagreement
  prefixProcessFiniteJointWindowSystemLocalCoherentOfMarginalConsistent :=
    bernoulliMixturePrefixProcessFiniteJointWindowSystem_localCoherent_of_marginalConsistent
  prefixProcessFiniteWindowCompatibleInCarrierOfMarginalConsistentCarrierRealization :=
    bernoulliMixturePrefixProcess_finiteWindowCompatibleInCarrier_of_prefixMarginalConsistentCarrierRealization
  processLawCompatibleCompletionOfPrefixMarginalConsistentCarrierRealization :=
    impreciseDeFinetti_processLawCompatibleCompletion_of_prefixMarginalConsistentCarrierRealization
  processLawCrownOfPrefixMarginalConsistentCarrierRealization :=
    impreciseDeFinetti_processLaw_projectiveNaturalExtension_crown_of_prefixMarginalConsistentCarrierRealization
  analyticMixingFamilyProcessLawCrownOfPrefixFiniteWindowRealization :=
    impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixFiniteWindowRealization
  analyticMixingFamilyProcessLawCrownOfPrefixTailFalseExtensionCarrierSubset :=
    impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixTailFalseExtensionCarrierSubset
  hasCompatibleCompletionOfFactorization :=
    DeFinettiProjectiveCredalSpecialization.hasCompatibleCompletion_of_factorization
  hasCompatibleCompletionOfExchangeable :=
    DeFinettiProjectiveCredalSpecialization.hasCompatibleCompletion_of_exchangeable

end Mettapedia.Logic.DeFinettiProjectiveCredalBridge
