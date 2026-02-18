import Mettapedia.CategoryTheory.DeFinettiKernelInterface
import Mettapedia.CategoryTheory.DeFinettiCategoricalInterface

/-!
# Lightweight Limit-Cone Package for Categorical de Finetti

This file provides a lightweight universal-property package for the
categorical de Finetti route without requiring `CategoryTheory.Limits.IsLimit`
infrastructure.

The package is intentionally proposition-level and reuses the existing
mediator API (`KernelRepresentsLatentTheta` and associated existence-uniqueness
theorems) as its semantic core.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.ProbabilityTheory.HigherOrderProbability

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Proposition-level universal mediator API at kernel level:
for every exchangeable kernel, a latent `Theta` mediator family exists uniquely. -/
def KernelLatentThetaUniversalMediator
    (X : ℕ → Ω → Bool) : Prop :=
  ∀ (_hX : ∀ i : ℕ, Measurable (X i))
    (κ : ProbabilityTheory.Kernel Y Ω) [ProbabilityTheory.IsMarkovKernel κ],
      KernelExchangeable X κ →
        ∃! L : Y → Measure DeFinettiConnection.Theta,
          KernelRepresentsLatentTheta (X := X) (κ := κ) L

/-- All-sources strengthening of the universal mediator API:
the same property must hold for every source type `Y'`. -/
def KernelLatentThetaUniversalMediator_allSources
    (X : ℕ → Ω → Bool) : Prop :=
  ∀ (Y' : Type*) [MeasurableSpace Y'],
    KernelLatentThetaUniversalMediator (Y := Y') (Ω := Ω) X

/-- Lightweight limit-cone package for categorical de Finetti:
the package stores exactly the universal mediator property. -/
structure DeFinettiLimitConePackage
    (X : ℕ → Ω → Bool) : Prop where
  universal : KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X

/-- Canonical construction of the lightweight limit-cone package from the
existing kernel-level de Finetti mediator theorem chain. -/
theorem deFinettiLimitConePackage_default
    (X : ℕ → Ω → Bool) :
    DeFinettiLimitConePackage (Y := Y) (Ω := Ω) X := by
  refine ⟨?_⟩
  intro hX κ _ hexch
  exact existsUnique_latentThetaKernel_of_kernelExchangeable (X := X) (κ := κ) hX hexch

/-- Canonical construction of the all-sources universal mediator API from the
existing kernel-level de Finetti mediator theorem chain. -/
theorem kernelLatentThetaUniversalMediator_allSources_default
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator_allSources (Ω := Ω) X := by
  intro Y' _ hX κ _ hexch
  exact existsUnique_latentThetaKernel_of_kernelExchangeable
    (Y := Y') (X := X) (κ := κ) hX hexch

/-- Canonical bridge theorem:
the lightweight package is equivalent to the existing universal mediator API. -/
theorem deFinettiLimitConePackage_iff_kernelLatentThetaUniversalMediator
    (X : ℕ → Ω → Bool) :
    Nonempty (DeFinettiLimitConePackage (Y := Y) (Ω := Ω) X) ↔
      KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact pkg.universal
  · intro h
    exact ⟨⟨h⟩⟩

/-- The universal mediator API follows directly from a package value. -/
theorem kernelLatentThetaUniversalMediator_of_package
    (X : ℕ → Ω → Bool)
    (pkg : DeFinettiLimitConePackage (Y := Y) (Ω := Ω) X) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X :=
  pkg.universal

/-- The lightweight limit-cone package is always inhabited via the default
construction. -/
theorem nonempty_deFinettiLimitConePackage
    (X : ℕ → Ω → Bool) :
    Nonempty (DeFinettiLimitConePackage (Y := Y) (Ω := Ω) X) :=
  ⟨deFinettiLimitConePackage_default (Y := Y) (Ω := Ω) X⟩

end Mettapedia.CategoryTheory
