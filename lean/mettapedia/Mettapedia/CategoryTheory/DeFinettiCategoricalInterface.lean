import Mettapedia.Logic.DeFinetti
import Mettapedia.CategoryTheory.DeFinettiHausdorffBridge

/-!
# Categorical Interface for de Finetti Factorization

This file isolates a qualitative/category-facing interface for de Finetti:
exchangeability yields a latent Bernoulli-mixture factorization of finite-prefix laws.

No quantitative rates are involved here.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open Mettapedia.Logic.Exchangeability
open Mettapedia.Logic.DeFinetti
open Mettapedia.ProbabilityTheory.HigherOrderProbability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Qualitative de Finetti factorization interface:
existence of a latent Bernoulli-mixture object that represents finite prefixes. -/
def CategoricalDeFinettiFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω) : Prop :=
  ∃ (M : BernoulliMixture), Represents M X μ

/-- Kernel-flavored alias for the same qualitative factorization interface. -/
def LatentBernoulliKernelFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω) : Prop :=
  CategoricalDeFinettiFactorization X μ

/-- Consumer API: extract the latent Bernoulli mixture from a factorization witness. -/
noncomputable def latentBernoulliMixtureOf
    {X : ℕ → Ω → Bool} {μ : Measure Ω}
    (hfac : CategoricalDeFinettiFactorization X μ) : BernoulliMixture :=
  Classical.choose hfac

/-- Consumer API: the extracted latent mixture satisfies the representation law. -/
theorem latentBernoulliMixtureOf_represents
    {X : ℕ → Ω → Bool} {μ : Measure Ω}
    (hfac : CategoricalDeFinettiFactorization X μ) :
    Represents (latentBernoulliMixtureOf hfac) X μ :=
  Classical.choose_spec hfac

/-- Consumer API: finite-prefix law is represented by the extracted latent mixture. -/
theorem prefixLaw_eq_of_categoricalFactorization
    {X : ℕ → Ω → Bool} {μ : Measure Ω}
    (hfac : CategoricalDeFinettiFactorization X μ)
    (n : ℕ) (xs : Fin n → Bool) :
    μ {ω | ∀ i : Fin n, X i.val ω = xs i} =
      ENNReal.ofReal ((latentBernoulliMixtureOf hfac).prob xs) :=
  latentBernoulliMixtureOf_represents hfac n xs

/-- Interface theorem (factorization-level only):
exchangeable binary processes admit a categorical de Finetti factorization. -/
theorem categoricalDeFinetti_factorization_of_exchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    CategoricalDeFinettiFactorization X μ :=
  deFinetti_infinite X μ hX hexch

/-- Kernel-flavored alias of
`categoricalDeFinetti_factorization_of_exchangeable`. -/
theorem latentBernoulliKernelFactorization_of_exchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    LatentBernoulliKernelFactorization X μ :=
  categoricalDeFinetti_factorization_of_exchangeable X μ hX hexch

/-- Bridge theorem:
the new categorical interface is equivalent to the existing exchangeability notion. -/
theorem exchangeable_iff_categoricalDeFinettiFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    InfiniteExchangeable X μ ↔ CategoricalDeFinettiFactorization X μ := by
  simpa [CategoricalDeFinettiFactorization] using
    (exchangeable_iff_bernoulliMixture X μ hX)

/-- Kernel-flavored alias of
`exchangeable_iff_categoricalDeFinettiFactorization`. -/
theorem exchangeable_iff_latentBernoulliKernelFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    InfiniteExchangeable X μ ↔ LatentBernoulliKernelFactorization X μ :=
  exchangeable_iff_categoricalDeFinettiFactorization X μ hX

/-- Latent-`Theta` factorization interface:
there exists a latent measure on `Theta = [0,1]` representing the process law. -/
def LatentThetaFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω) : Prop :=
  ∃ ν : Measure DeFinettiConnection.Theta, RepresentsLatentTheta X μ ν

/-- Direct latent-`Theta` interface theorem:
exchangeable binary processes admit a unique latent `Theta` measure. -/
theorem categorical_existsUnique_latentThetaMeasure_of_exchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    ∃! ν : Measure DeFinettiConnection.Theta, RepresentsLatentTheta X μ ν :=
  existsUnique_latentThetaMeasure_of_exchangeable (X := X) (μ := μ) hX hexch

/-- Canonical latent-`Theta` mediator for an exchangeable law. -/
noncomputable def canonicalLatentThetaMediatorOfExchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    Measure DeFinettiConnection.Theta :=
  Classical.choose (categorical_existsUnique_latentThetaMeasure_of_exchangeable (X := X) (μ := μ) hX hexch)

/-- The canonical latent mediator satisfies the latent representation interface. -/
theorem canonicalLatentThetaMediatorOfExchangeable_spec
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    RepresentsLatentTheta X μ (canonicalLatentThetaMediatorOfExchangeable X μ hX hexch) :=
  (Classical.choose_spec (categorical_existsUnique_latentThetaMeasure_of_exchangeable
    (X := X) (μ := μ) hX hexch)).1

/-- Canonicality: any latent-`Theta` mediator equals the canonical one. -/
theorem canonicalLatentThetaMediatorOfExchangeable_unique
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ)
    (ν : Measure DeFinettiConnection.Theta)
    (hν : RepresentsLatentTheta X μ ν) :
    ν = canonicalLatentThetaMediatorOfExchangeable X μ hX hexch := by
  exact (Classical.choose_spec (categorical_existsUnique_latentThetaMeasure_of_exchangeable
    (X := X) (μ := μ) hX hexch)).2 ν hν

/-- Limit-cone wording: exchangeable laws admit a unique latent-`Theta` mediator map. -/
theorem deFinetti_limitCone_universalMediator_latentTheta
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    ∃! ν : Measure DeFinettiConnection.Theta, RepresentsLatentTheta X μ ν :=
  categorical_existsUnique_latentThetaMeasure_of_exchangeable (X := X) (μ := μ) hX hexch

/-- Existence-only latent-`Theta` factorization from exchangeability. -/
theorem latentThetaFactorization_of_exchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : InfiniteExchangeable X μ) :
    LatentThetaFactorization X μ := by
  rcases categorical_existsUnique_latentThetaMeasure_of_exchangeable (X := X) (μ := μ) hX hexch with
    ⟨ν, hν, _⟩
  exact ⟨ν, hν⟩

/-- Exchangeability is equivalent to existence of a latent-`Theta` factorization. -/
theorem exchangeable_iff_latentThetaFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    InfiniteExchangeable X μ ↔ LatentThetaFactorization X μ := by
  constructor
  · intro hexch
    exact latentThetaFactorization_of_exchangeable (X := X) (μ := μ) hX hexch
  · intro hθ
    rcases hθ with ⟨ν, hν⟩
    rcases hν with ⟨M, hrep, _⟩
    exact (exchangeable_iff_categoricalDeFinettiFactorization (X := X) (μ := μ) hX).2 ⟨M, hrep⟩

/-! ## API Index

Category-route theorem chain (qualitative):
- Measure level:
  `exchangeable_iff_categoricalDeFinettiFactorization`
  `categorical_existsUnique_latentThetaMeasure_of_exchangeable`
  `deFinetti_limitCone_universalMediator_latentTheta`
  `exchangeable_iff_latentThetaFactorization`
- Kernel level (`DeFinettiKernelInterface`):
  `kernelExchangeable_iff_kernelLatentThetaFactorization`
  `existsUnique_latentThetaKernel_of_kernelExchangeable`
  `existsUnique_kernelLatentThetaConeMorphism_of_kernelExchangeable`
- Sequence-cone bridge (`DeFinettiSequenceKernelCone`):
  `sequenceKernelConeObj_iff_kernelLatentThetaFactorization_coord`
  `sequenceKernelConeObj_roundTrip_latentThetaMediator`
-/

end Mettapedia.CategoryTheory
