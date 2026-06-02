import Mettapedia.CategoryTheory.DeFinettiCategoricalInterface
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

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

end BernoulliMixturePrefixLaw

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

/-! ## Profile surface -/

/-- Proof-carrying profile for the de Finetti face of the shared projective
credal abstraction. -/
structure ProjectiveDeFinettiCredalBridgeProfile where
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
  prefixMixturePrevisionIsPrecise :=
    by
      intro M n h
      exact BernoulliMixturePrefixLaw.toPrecisePrevision_precise h
  imprecisePrefixCredalSetNonempty :=
    bernoulliMixturePrefixCredalSet_nonempty
  hasCompatibleCompletionOfFactorization :=
    DeFinettiProjectiveCredalSpecialization.hasCompatibleCompletion_of_factorization
  hasCompatibleCompletionOfExchangeable :=
    DeFinettiProjectiveCredalSpecialization.hasCompatibleCompletion_of_exchangeable

end Mettapedia.Logic.DeFinettiProjectiveCredalBridge
