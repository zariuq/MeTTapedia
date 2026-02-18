import Mettapedia.ProbabilityTheory.MarkovCategory.Kernels
import Mettapedia.CategoryTheory.DeFinettiKernelInterface
import Mettapedia.CategoryTheory.DeFinettiPerNDiagram
import Mettapedia.CategoryTheory.DeFinettiGlobalFinitaryDiagram

/-!
# De Finetti Bridge to Markov-Category Core

Packages the existing kernel-level de Finetti universal-mediator theorem under
the kernel `MarkovCategoryCore` viewpoint.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.ProbabilityTheory

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Markov-core phrasing of exchangeability for kernel-indexed coordinate laws. -/
def KernelExchangeableInMarkovCore
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  KernelExchangeable X κ

/-- Markov-core phrasing of latent-`Theta` kernel representation. -/
def KernelLatentThetaMediatorInMarkovCore
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∃! L : Y →
      Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
    KernelRepresentsLatentTheta X κ L

/-- Markov-core universal mediator API:
for every exchangeable Markov kernel, there is a unique latent-`Theta` mediator. -/
def KernelLatentThetaUniversalMediatorInMarkovCore
    (X : ℕ → Ω → Bool) : Prop :=
  ∀ (_hX : ∀ i : ℕ, Measurable (X i))
    (κ : ProbabilityTheory.Kernel Y Ω) [ProbabilityTheory.IsMarkovKernel κ],
      KernelExchangeableInMarkovCore (Y := Y) (Ω := Ω) X κ →
        KernelLatentThetaMediatorInMarkovCore (Y := Y) (Ω := Ω) X κ

/-- In the kernel Markov-category core, exchangeable kernels admit a unique
latent-`Theta` mediator. -/
theorem kernelMarkovCore_exchangeable_implies_unique_latentThetaMediator
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeableInMarkovCore (Y := Y) (Ω := Ω) X κ) :
    KernelLatentThetaMediatorInMarkovCore (Y := Y) (Ω := Ω) X κ := by
  simpa [KernelExchangeableInMarkovCore, KernelLatentThetaMediatorInMarkovCore] using
    (existsUnique_latentThetaKernel_of_kernelExchangeable
      (X := X) (κ := κ) hX hexch)

/-- Markov-core universal mediator API is definitionally equivalent to the
existing kernel-level universal mediator API. -/
theorem kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X ↔
      KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X := by
  constructor <;> intro h
  · intro hX κ _ hexch
    exact h hX κ hexch
  · intro hX κ _ hexch
    exact h hX κ hexch

/-- If we have:
1. per-`n` mediator uniqueness packaging, and
2. global finitary lifted commutation giving cross-`n` package witnesses,
then we get the Markov-core universal mediator API. -/
theorem kernelLatentThetaUniversalMediatorInMarkovCore_of_globalCommutes_and_mediatorUniqueness
    (X : ℕ → Ω → Bool)
    (hperN : ExchangeablePerNLimitMediatorUnique (Ω := Ω) X)
    (_hglobal :
      ∀ μ : Measure Ω, GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ)) :
    KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X := by
  have huniv :
      KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X :=
    (kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
      (Y := Y) (Ω := Ω) X).2 hperN
  exact
    (kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
      (Y := Y) (Ω := Ω) X).2 huniv

end Mettapedia.CategoryTheory
