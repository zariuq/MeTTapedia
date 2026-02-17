import Mettapedia.CategoryTheory.DeFinettiStableExports

/-!
# De Finetti Category Exports (Recommended Import Surface)

This is the single recommended import path for the categorical de Finetti route.
It re-exports the stable theorem chain needed by downstream users.

## API Chain (Recommended Order)
1. `deFinettiExport_kernelUniversalMediator_iff_crossNPackageFamily`
2. `deFinettiExport_kernelUniversalMediator_iff_perNUnique`
3. `deFinettiExport_crossNPackage_of_prefixCone`
4. `deFinettiExport_kernelUniversalMediator_endToEndChain`
5. `deFinettiExport_kernelUniversalMediator_endToEnd_globalChain`
6. `deFinettiExport_isLimit_iff_globalIIDConeMediatorUnique`
7. `deFinettiExport_isLimit_iff_globalIIDConeMediatorUniqueProbBool`
8. `deFinettiExport_isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta`
9. `deFinettiExport_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance`
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Recommended export: kernel-level universal mediator API is equivalent to
per-`n` limit-mediator uniqueness packaging. -/
theorem deFinettiExport_kernelUniversalMediator_iff_perNUnique
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ExchangeablePerNLimitMediatorUnique (Ω := Ω) X :=
  deFinettiStable_kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
    (Y := Y) (Ω := Ω) X

/-- Recommended export: kernel-level universal mediator API is equivalent, in one
hop, to the global cross-`n` package family. -/
theorem deFinettiExport_kernelUniversalMediator_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  deFinettiStable_kernelLatentThetaUniversalMediator_iff_crossNPackageFamily
    (Y := Y) (Ω := Ω) X

/-- Recommended end-to-end theorem chain: kernel universal mediator API,
per-`n` uniqueness package, and cross-`n` package family are bundled in one
equivalence statement for downstream imports. -/
theorem deFinettiExport_kernelUniversalMediator_endToEndChain
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      (ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ∧
        (∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
          Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ))) := by
  constructor
  · intro h
    exact ⟨
      (deFinettiExport_kernelUniversalMediator_iff_perNUnique
        (Y := Y) (Ω := Ω) X).1 h,
      (deFinettiExport_kernelUniversalMediator_iff_crossNPackageFamily
        (Y := Y) (Ω := Ω) X).1 h⟩
  · intro h
    exact (deFinettiExport_kernelUniversalMediator_iff_perNUnique
      (Y := Y) (Ω := Ω) X).2 h.1

/-- Recommended end-to-end theorem chain (global-action form):
kernel universal mediator API is equivalent to:
1. per-`n` mediator uniqueness, and
2. global lifted commutation producing cross-`n` packages. -/
theorem deFinettiExport_kernelUniversalMediator_endToEnd_globalChain
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      (ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ∧
        (∀ μ : Measure Ω, GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ →
          Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ))) :=
  deFinettiStable_kernelUniversalMediator_endToEnd_globalChain
    (Y := Y) (Ω := Ω) X

/-- Recommended export: global cross-`n` limit package from prefix-law
exchangeability. -/
def deFinettiExport_crossNPackage_of_prefixCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ) :
    ExchangeableCrossNLimitPackage (Ω := Ω) X μ :=
  deFinettiStable_exchangeableCrossNLimitPackage_of_isPrefixLawCone
    (Ω := Ω) X μ hcone

/-- Recommended export: mediator uniqueness check inside the cross-`n` package. -/
theorem deFinettiExport_crossNPackage_mediators_eq_of_fac
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (pkg : ExchangeableCrossNLimitPackage (Ω := Ω) X μ)
    (n : ℕ) (m₁ m₂ : PUnit ⟶ PerNPrefixFixedPoints n)
    (hm₁ :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m₁ ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n pkg.hcone).π.app j)
    (hm₂ :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m₂ ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n pkg.hcone).π.app j) :
    m₁ = m₂ :=
  deFinettiStable_exchangeableCrossNLimitPackage_mediators_eq_of_fac
    (Ω := Ω) X μ pkg n m₁ m₂ hm₁ hm₂

/-- Recommended export: explicit iid-prefix factorization form for sequence
kernels. This is the direct kernel-level statement closest to
`k̃ ≫ iid = k` at finite-prefix granularity. -/
theorem deFinettiExport_existsUnique_latentThetaKernel_with_iidPrefixFactorization_coord
    (κ : ProbabilityTheory.Kernel Y (ℕ → Bool))
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ →
      ∃! L :
        Y →
          Measure
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
        KernelRepresentsLatentTheta (X := coordProcess) κ L ∧
          (∀ (y : Y) (n : ℕ) (xs : Fin n → Bool),
            (κ y) (seqPrefixEvent n xs) =
              ∫⁻ θ :
                  Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
                (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) ∂(L y)) :=
  deFinettiStable_existsUnique_latentThetaKernel_with_iidPrefixFactorization_coord
    (κ := κ)

/-- Recommended export: explicit sequence-level mediator record packaging
finite-prefix iid-factorization equations. -/
theorem deFinettiExport_existsUnique_kernelIIDPrefixMediator_of_sequenceKernelConeObj
    (κ : ProbabilityTheory.Kernel Y (ℕ → Bool))
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ →
      ∃! M : KernelIIDPrefixMediator (κ := κ),
        KernelRepresentsLatentTheta (X := coordProcess) κ M.latent :=
  deFinettiStable_existsUnique_kernelIIDPrefixMediator_of_sequenceKernelConeObj
    (κ := κ)

/-- Recommended export: global finitary-permutation lifted commutation laws are
equivalent to `IsPrefixLawCone`. -/
theorem deFinettiExport_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    IsPrefixLawCone (Ω := Ω) X μ ↔
      GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ :=
  deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
    (Ω := Ω) X μ

/-- Recommended export: one-hop bridge from global finitary lifted commutation
to cross-`n` mediator uniqueness packaging. -/
theorem deFinettiExport_globalLiftedPrefixLawConeCommutes_to_crossNPackage
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hglobal : GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ) :
    Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  deFinettiStable_globalLiftedPrefixLawConeCommutes_to_crossNPackage
    (Ω := Ω) X μ hglobal

/-- Recommended export: for fixed `μ`, global finitary lifted commutation is
equivalent to prefix-cone plus a concrete cross-`n` package witness. -/
theorem deFinettiExport_globalLiftedPrefixLawConeCommutes_iff_prefixCone_and_crossNPackage
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ ↔
      (IsPrefixLawCone (Ω := Ω) X μ ∧
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ)) :=
  deFinettiStable_globalLiftedPrefixLawConeCommutes_iff_prefixCone_and_crossNPackage
    (Ω := Ω) X μ

/-- Recommended export: per-`n` uniqueness package iff global cross-`n` package
family over exchangeable prefix-law cones. -/
theorem deFinettiExport_perNUnique_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  deFinettiStable_perNUnique_iff_crossNPackageFamily (Ω := Ω) X

/-- Recommended export: true global Kleisli(Giry) `IsLimit` packaging is
equivalent to global mediator uniqueness for an iid-cone skeleton. -/
theorem deFinettiExport_isLimit_iff_globalIIDConeMediatorUnique
    (cone : KleisliGiryIIDConeSkeleton) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUnique cone :=
  deFinettiStable_isLimit_iff_globalIIDConeMediatorUnique cone

/-- Recommended export: specialized `P Bool` form of the true global
Kleisli(Giry) `IsLimit` equivalence. -/
theorem deFinettiExport_isLimit_iff_globalIIDConeMediatorUniqueProbBool
    (cone : KleisliGiryProbBoolIIDCone) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUniqueProbBool cone :=
  deFinettiStable_isLimit_iff_globalIIDConeMediatorUniqueProbBool cone

/-- Recommended export: horizon-`n` cylinder evaluation for
`iidSequenceKernelTheta`, assuming the canonical Dirac latent mediator
interface. -/
theorem deFinettiExport_iidSequenceKernelTheta_prefix_apply_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) :=
  deFinettiStable_iidSequenceKernelTheta_prefix_apply_of_latentDirac hrep θ n xs

/-- Recommended export: for the cone built from `iidSequenceKernelTheta`, true
`IsLimit` is equivalent to global mediator uniqueness. -/
theorem deFinettiExport_isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
      GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta hcommutes

/-- Recommended export: no-extra-hypothesis (beyond global finitary invariance)
IsLimit-ready bundle for `iidSequenceKernelTheta`.
This provides in one hop:
1. the derived commutation witness,
2. unconditional horizon-`n` prefix evaluation via the canonical latent-kernel,
3. the true `IsLimit`/mediator-uniqueness equivalence for the induced cone. -/
theorem deFinettiExport_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    ∃ hcommutes : ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
          iidSequenceKleisliHomTheta,
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ)) ∧
      (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :=
  deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance hglobal

/-- Recommended export: true `HasLimit` packaging for each per-`n` diagram. -/
theorem deFinettiExport_hasLimit_perN (n : ℕ) :
    CategoryTheory.Limits.HasLimit (perNPrefixDiagramFunctor n) :=
  deFinettiStable_hasLimit_perNPrefixDiagramFunctor (n := n)

/-- Recommended export: explicit true `LimitCone` for each per-`n` diagram. -/
def deFinettiExport_limitCone_perN (n : ℕ) :
    CategoryTheory.Limits.LimitCone (perNPrefixDiagramFunctor n) :=
  deFinettiStable_perNPrefixDiagramLimitCone (n := n)

end Mettapedia.CategoryTheory
