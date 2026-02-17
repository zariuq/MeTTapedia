import Mettapedia.CategoryTheory.DeFinettiPerNDiagram
import Mettapedia.CategoryTheory.DeFinettiSequenceKernelCone

/-!
# Stable Export Surface for Categorical de Finetti

Downstream modules should prefer importing this file instead of importing
multiple internal category-route files directly.

This module re-exports the stable theorem chain by providing lightweight alias
theorems.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.ProbabilityTheory.HigherOrderProbability

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Stable alias: exchangeability iff latent-`Theta` factorization (measure level). -/
theorem deFinettiStable_exchangeable_iff_latentThetaFactorization
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    Mettapedia.Logic.Exchangeability.InfiniteExchangeable X μ ↔
      LatentThetaFactorization X μ :=
  exchangeable_iff_latentThetaFactorization X μ hX

/-- Stable alias: unique latent mediator at measure level. -/
theorem deFinettiStable_existsUnique_latentThetaMeasure_of_exchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : Mettapedia.Logic.Exchangeability.InfiniteExchangeable X μ) :
    ∃! ν : Measure DeFinettiConnection.Theta, RepresentsLatentTheta X μ ν :=
  deFinetti_limitCone_universalMediator_latentTheta X μ hX hexch

/-- Stable alias: canonical mediator object at measure level. -/
noncomputable def deFinettiStable_canonicalLatentThetaMediatorOfExchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : Mettapedia.Logic.Exchangeability.InfiniteExchangeable X μ) :
    Measure DeFinettiConnection.Theta :=
  canonicalLatentThetaMediatorOfExchangeable X μ hX hexch

/-- Stable alias: kernel exchangeability iff kernel latent-`Theta` factorization. -/
theorem deFinettiStable_kernelExchangeable_iff_kernelLatentThetaFactorization
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i)) :
    KernelExchangeable X κ ↔ KernelLatentThetaFactorization X κ :=
  kernelExchangeable_iff_kernelLatentThetaFactorization X κ hX

/-- Stable alias: unique latent mediator at kernel level. -/
theorem deFinettiStable_existsUnique_latentThetaKernel_of_kernelExchangeable
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ) :
    ∃! L : Y → Measure DeFinettiConnection.Theta, KernelRepresentsLatentTheta X κ L :=
  existsUnique_latentThetaKernel_of_kernelExchangeable (X := X) (κ := κ) hX hexch

/-- Stable alias: cone-morphism packaging unique mediator theorem. -/
theorem deFinettiStable_existsUnique_kernelLatentThetaConeMorphism_of_kernelExchangeable
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeable X κ) :
    ∃! Φ : KernelLatentThetaConeMorphism X κ,
      Φ.mediator =
        latentThetaKernelOf
          (kernelIIDFactorization_of_kernelExchangeable (X := X) (κ := κ) hX hexch) :=
  existsUnique_kernelLatentThetaConeMorphism_of_kernelExchangeable (X := X) (κ := κ) hX hexch

/-- Stable alias: package bridge theorem for the lightweight limit-cone API. -/
theorem deFinettiStable_limitConePackage_bridge
    (X : ℕ → Ω → Bool) :
    Nonempty (DeFinettiLimitConePackage (Y := Y) (Ω := Ω) X) ↔
      KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X :=
  deFinettiLimitConePackage_iff_kernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X

/-- Stable alias: sequence-kernel cone round-trip theorem. -/
theorem deFinettiStable_sequenceKernelCone_roundTrip
    (κ : ProbabilityTheory.Kernel Y (ℕ → Bool))
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔
      (KernelLatentThetaFactorization (X := coordProcess) κ ∧
        ∃! L :
          Y →
            Measure
              Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
          KernelRepresentsLatentTheta (X := coordProcess) κ L) :=
  sequenceKernelConeObj_roundTrip_latentThetaMediator (κ := κ)

/-- Stable export: forward bridge from lightweight package witnesses to
per-`n` `IsLimit`-style witnesses. -/
theorem deFinettiStable_limitConePackage_to_perNIsLimit
    (X : ℕ → Ω → Bool)
    (pkg : DeFinettiLimitConePackage (Y := Y) (Ω := Ω) X) :
    DeFinettiPerNIsLimit (Y := Y) (Ω := Ω) X :=
  deFinettiLimitConePackage_to_perNIsLimit (Y := Y) (Ω := Ω) (X := X) pkg

/-- Stable export: true per-`n` cone-commutativity family is equivalent to
the existing `IsPrefixLawCone` predicate. -/
theorem deFinettiStable_isPrefixLawCone_iff_perNPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    IsPrefixLawCone (Ω := Ω) X μ ↔
      ∀ n : ℕ, PerNPrefixLawConeCommutes (Ω := Ω) X μ n :=
  isPrefixLawCone_iff_perNPrefixLawConeCommutes (Ω := Ω) X μ

/-- Stable export: true limit cone for the per-`n` permutation diagram. -/
def deFinettiStable_perNPrefixDiagramLimitCone (n : ℕ) :
    CategoryTheory.Limits.LimitCone (perNPrefixDiagramFunctor n) :=
  perNPrefixDiagramLimitCone n

/-- Stable export: lightweight `DeFinettiPerNIsLimit` naming implies the true
per-`n` `LimitCone` packaging. -/
theorem deFinettiStable_perNIsLimit_to_trueLimitCone
    (X : ℕ → Ω → Bool) (n : ℕ)
    (h : DeFinettiPerNIsLimit (Y := Y) (Ω := Ω) X) :
    Nonempty (CategoryTheory.Limits.LimitCone (perNPrefixDiagramFunctor n)) :=
  deFinettiPerNIsLimit_to_trueLimitCone (Y := Y) (Ω := Ω) (X := X) (n := n) h

/-- Stable export: `HasLimit` packaging for the true per-`n` diagram. -/
theorem deFinettiStable_hasLimit_perNPrefixDiagramFunctor (n : ℕ) :
    CategoryTheory.Limits.HasLimit (perNPrefixDiagramFunctor n) :=
  hasLimit_perNPrefixDiagramFunctor n

end Mettapedia.CategoryTheory
