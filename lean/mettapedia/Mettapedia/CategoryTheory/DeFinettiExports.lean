import Mettapedia.CategoryTheory.DeFinettiStableExports
import Mettapedia.CategoryTheory.DeFinettiExternalBridge
import Mettapedia.CategoryTheory.DeFinettiMarkovCategoryBridge
import Mettapedia.Logic.SolomonoffExchangeable

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
10. `deFinettiExport_iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals`
11. `deFinettiExport_markovCoreUniversal_iff_crossNPackageFamily`
12. `deFinettiExport_markovCore_to_kleisliRoute`
13. `deFinettiExport_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique`
14. `deFinettiExport_markovCore_to_kleisliIsLimit`
15. `deFinettiExport_isLimit_implies_globalIIDConeMediatorUnique_markovOnly`
16. `deFinettiExport_kernelUniversalMediator_allSources_default`
17. `deFinettiExport_restrictedSolomonoff_prefixLaw_implies_unique_latentThetaMediator`
18. `deFinettiExport_restrictedSolomonoff_totalOutput_implies_nupln_master_chain_and_unique_latentThetaMediator`
19. `deFinettiExport_restrictedSolomonoff_totalOutput_and_programMassComplete_implies_nupln_master_chain_and_unique_latentThetaMediator`

## Markov-Core Route (Recommended)
1. Use `deFinettiExport_markovCoreUniversal_iff_crossNPackageFamily` to align
   Markov-core universality with the cross-`n` package family.
2. Use `deFinettiExport_markovCore_to_kleisliRoute` to obtain the concrete
   Kleisli(Giry) `IsLimit`-ready witness bundle.
3. When global mediator uniqueness is available, use
   `deFinettiExport_markovCore_to_kleisliIsLimit` for a concrete
   `Nonempty IsLimit` witness.
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

/-- Recommended export: in the kernel Markov-category core, exchangeability
implies unique latent-`Theta` mediation. -/
theorem deFinettiExport_kernelMarkovCore_exchangeable_implies_unique_latentThetaMediator
    (X : ℕ → Ω → Bool) (κ : ProbabilityTheory.Kernel Y Ω)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : KernelExchangeableInMarkovCore (Y := Y) (Ω := Ω) X κ) :
    KernelLatentThetaMediatorInMarkovCore (Y := Y) (Ω := Ω) X κ :=
  kernelMarkovCore_exchangeable_implies_unique_latentThetaMediator
    (Y := Y) (Ω := Ω) X κ hX hexch

/-- Recommended export: Markov-core universal mediator API is equivalent to the
global cross-`n` package family. -/
theorem deFinettiExport_markovCoreUniversal_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) := by
  calc
    KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X ↔
        KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X := by
          exact
            kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
              (Y := Y) (Ω := Ω) X
    _ ↔ ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) := by
          exact deFinettiExport_kernelUniversalMediator_iff_crossNPackageFamily
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

/-- Recommended export (Path-B): finite-prefix Bernoulli product marginals for
`iidSequenceKernelTheta` imply the full IsLimit-ready Kleisli(Giry) bundle. -/
theorem deFinettiExport_iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) :
    ∃ hcommutes : ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
          iidSequenceKleisliHomTheta,
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance
              (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidProduct_bridge
                (iidSequenceKernelTheta_eq_iidProduct_of_prefix_pi_marginals hprefix)) θ)) ∧
      (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :=
  deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals hprefix

/-- Recommended export: concrete `IsLimit` witness for the global Kleisli(Giry)
cone built from `iidSequenceKernelTheta`, assuming:
1. global finitary invariance, and
2. global mediator uniqueness for the induced cone. -/
theorem deFinettiExport_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmed :
      GlobalIIDConeMediatorUnique
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal))) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) :=
  deFinettiStable_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique
    (hglobal := hglobal) hmed

/-- Recommended alias theorem: Markov-core universal mediation plus global
finitary invariance provides the practical bridge to the true Kleisli(Giry)
`IsLimit`-ready package.

This bundles:
1. recovery of the standard kernel-level universal mediator API, and
2. the concrete Kleisli(Giry) `IsLimit`-ready witness/equivalence package for
   `iidSequenceKernelTheta`. -/
theorem deFinettiExport_markovCore_to_kleisliRoute
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      (∃ hcommutes : ∀ τ : FinSuppPermNat,
          CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
            iidSequenceKleisliHomTheta,
        (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
          iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
            ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
              (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ)) ∧
        (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
          GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes))) := by
  exact deFinettiStable_markovCore_to_kleisliRoute
    (Y := Y) (Ω := Ω) X hcore hglobal

/-- Recommended alias theorem: Markov-core universal mediation plus global
finitary invariance and mediator uniqueness yield a concrete global
Kleisli(Giry) `IsLimit` witness for `iidSequenceKernelTheta`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmed :
      GlobalIIDConeMediatorUnique
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal))) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact deFinettiStable_markovCore_to_kleisliIsLimit
    (Y := Y) (Ω := Ω) X hcore hglobal hmed

/-- Recommended export: any concrete `IsLimit` witness yields the Markov-only
global mediator-uniqueness property for the same Kleisli cone. -/
theorem deFinettiExport_isLimit_implies_globalIIDConeMediatorUnique_markovOnly
    (cone : KleisliGiryIIDConeSkeleton)
    (hlim : CategoryTheory.Limits.IsLimit (cone.toCone)) :
    GlobalIIDConeMediatorUnique_markovOnly cone :=
  deFinettiStable_isLimit_implies_globalIIDConeMediatorUnique_markovOnly
    cone hlim

/-- Recommended export: canonical all-sources strengthening of the kernel
universal mediator API (quantifier-complete source side). -/
theorem deFinettiExport_kernelUniversalMediator_allSources_default
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator_allSources (Ω := Ω) X :=
  deFinettiStable_kernelUniversalMediator_allSources_default (Ω := Ω) X

/-- Recommended export: true `HasLimit` packaging for each per-`n` diagram. -/
theorem deFinettiExport_hasLimit_perN (n : ℕ) :
    CategoryTheory.Limits.HasLimit (perNPrefixDiagramFunctor n) :=
  deFinettiStable_hasLimit_perNPrefixDiagramFunctor (n := n)

/-- Recommended export: direct bridge to the vendored `exchangeability` L²
de Finetti theorem (`Exchangeable -> ConditionallyIID`) for real-valued
processes. -/
theorem deFinettiExport_external_viaL2_exchangeable_implies_conditionallyIID
    {Ωr : Type*} [MeasurableSpace Ωr] [StandardBorelSpace Ωr]
    (μ : Measure Ωr) [IsProbabilityMeasure μ]
    (X : ℕ → Ωr → ℝ)
    (hX_meas : ∀ i : ℕ, Measurable (X i))
    (hX_exch : Exchangeability.Exchangeable μ X)
    (hX_L2 : ∀ i : ℕ, MemLp (X i) 2 μ) :
    Exchangeability.ConditionallyIID μ X :=
  deFinettiExternal_viaL2_exchangeable_implies_conditionallyIID
    (μ := μ) (X := X) hX_meas hX_exch hX_L2

/-- Recommended bridge for νPLN/Solomonoff restriction:
if a probability law on infinite binary sequences realizes the finite-prefix
weights of a restricted exchangeable Solomonoff prior, then the coordinate
process admits a unique latent-`Theta` de Finetti mediator. -/
theorem deFinettiExport_restrictedSolomonoff_prefixLaw_implies_unique_latentThetaMediator
    (M : Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior)
    (μ : Measure Mettapedia.Logic.SolomonoffPrior.InfBinString)
    [IsProbabilityMeasure μ]
    (hprefix :
      ∀ (n : ℕ) (xs : Fin n → Bool),
        μ {ω | ∀ i : Fin n, ω i = xs i} =
          ENNReal.ofReal (M.μ (List.ofFn xs))) :
    ∃! ν : Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
      RepresentsLatentTheta (X := fun i ω => ω i) (μ := μ) ν := by
  have hX :
      ∀ i : ℕ, Measurable
        (fun ω : Mettapedia.Logic.SolomonoffPrior.InfBinString => ω i) := by
    intro i
    simpa using (measurable_pi_apply (a := i))
  have hexch :
      Mettapedia.Logic.Exchangeability.InfiniteExchangeable (fun i ω => ω i) μ :=
    Mettapedia.Logic.SolomonoffExchangeable.restrictedSolomonoff_infiniteExchangeable_of_prefixLaw
      (M := M) (μ := μ) (hμprob := inferInstance) hprefix
  exact deFinettiStable_existsUnique_latentThetaMeasure_of_exchangeable
    (X := fun i ω => ω i) (μ := μ) hX hexch

/-- Deprecated entrypoint: one hop from tight cylinder law.
Prefer the concrete theorem
`deFinettiExport_restrictedSolomonoff_totalOutput_and_programMassComplete_implies_nupln_master_chain_and_unique_latentThetaMediator`
when working from machine/program assumptions. This theorem remains for
compatibility at the measure-law boundary.

Recommended νPLN/categorical corollary (one hop from tight cylinder law):
the restricted Solomonoff cylinder law yields both
1. the full `nupln_master_chain` conclusion, and
2. the unique latent-`Theta` mediator conclusion. -/
theorem deFinettiExport_restrictedSolomonoff_cylinderLaw_implies_nupln_master_chain_and_unique_latentThetaMediator
    (M : Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior)
    (μ : Measure Mettapedia.Logic.SolomonoffPrior.InfBinString)
    [IsProbabilityMeasure μ]
    (hNoLeak :
      Mettapedia.Logic.NoLeakageAtCylindersLaw (U := M.U) (programs := M.programs) μ) :
    (∃ (B : Mettapedia.Logic.DeFinetti.BernoulliMixture),
      Mettapedia.Logic.DeFinetti.Represents B (fun i ω => ω i) μ ∧
      (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
        Mettapedia.Logic.Exchangeability.countTrue xs₁ =
          Mettapedia.Logic.Exchangeability.countTrue xs₂ →
          B.prob xs₁ = B.prob xs₂)) ∧
    (∃! ν : Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
      RepresentsLatentTheta (X := fun i ω => ω i) (μ := μ) ν) := by
  have hX :
      ∀ i : ℕ, Measurable
        (fun ω : Mettapedia.Logic.SolomonoffPrior.InfBinString => ω i) := by
    intro i
    simpa using (measurable_pi_apply (a := i))
  have hexch :
      Mettapedia.Logic.Exchangeability.InfiniteExchangeable (fun i ω => ω i) μ :=
    Mettapedia.Logic.SolomonoffExchangeable.restrictedSolomonoff_infiniteExchangeable_of_noLeakageAtCylindersLaw
      (M := M) (μ := μ) (hμprob := inferInstance) hNoLeak
  have hmaster := Mettapedia.Logic.DeFinetti.nupln_master_chain
      (X := fun i ω => ω i) (μ := μ) hX hexch
  rcases hmaster with ⟨B, hrep, hsuff, _hevidence, _hconv⟩
  refine ⟨?_, ?_⟩
  · exact ⟨B, hrep, hsuff⟩
  · exact deFinettiStable_existsUnique_latentThetaMeasure_of_exchangeable
      (X := fun i ω => ω i) (μ := μ) hX hexch

/-- Recommended νPLN/categorical corollary from a concrete machine criterion:
if selected programs are total-output and root mass is normalized, the canonical
machine-induced measure yields both `nupln_master_chain` and unique latent-`Theta`
mediation, with no external cylinder-law witness required. -/
theorem deFinettiExport_restrictedSolomonoff_totalOutput_implies_nupln_master_chain_and_unique_latentThetaMediator
    (M : Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior)
    (htot : Mettapedia.Logic.TotalOutputOnPrograms (U := M.U) M.programs)
    (hroot : M.μ [] = 1) :
    let μ := Mettapedia.Logic.totalOutputProgramMeasure
      (U := M.U) (programs := M.programs) htot
    (∃ (B : Mettapedia.Logic.DeFinetti.BernoulliMixture),
      Mettapedia.Logic.DeFinetti.Represents B (fun i ω => ω i) μ ∧
      (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
        Mettapedia.Logic.Exchangeability.countTrue xs₁ =
          Mettapedia.Logic.Exchangeability.countTrue xs₂ →
          B.prob xs₁ = B.prob xs₂)) ∧
    (∃! ν : Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
      RepresentsLatentTheta (X := fun i ω => ω i) (μ := μ) ν) := by
  let μ : Measure Mettapedia.Logic.SolomonoffPrior.InfBinString :=
    Mettapedia.Logic.totalOutputProgramMeasure (U := M.U) (programs := M.programs) htot
  have hμprob : IsProbabilityMeasure μ := by
    simpa [μ, Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior.μ] using
      (Mettapedia.Logic.isProbabilityMeasure_totalOutputProgramMeasure_of_root_one
        (U := M.U) (programs := M.programs) (htot := htot) hroot)
  letI : IsProbabilityMeasure μ := hμprob
  have hNoLeak :
      Mettapedia.Logic.NoLeakageAtCylindersLaw (U := M.U) (programs := M.programs) μ := by
    simpa [μ] using
      (Mettapedia.Logic.noLeakageAtCylindersLaw_totalOutputProgramMeasure
        (U := M.U) (programs := M.programs) htot)
  simpa [μ] using
    (deFinettiExport_restrictedSolomonoff_cylinderLaw_implies_nupln_master_chain_and_unique_latentThetaMediator
      (M := M) (μ := μ) hNoLeak)

/-- Recommended concrete end-to-end νPLN/categorical corollary:
assume total-output on the selected program family plus concrete program-mass
completeness (`kraftSum = 1`), then derive the same
`nupln_master_chain + unique latent-Theta mediator` conclusion with no explicit
`hroot` argument. -/
theorem deFinettiExport_restrictedSolomonoff_totalOutput_and_programMassComplete_implies_nupln_master_chain_and_unique_latentThetaMediator
    (M : Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior)
    (htot : Mettapedia.Logic.TotalOutputOnPrograms (U := M.U) M.programs)
    (hcomplete : Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior.ProgramMassComplete M) :
    let μ := Mettapedia.Logic.totalOutputProgramMeasure
      (U := M.U) (programs := M.programs) htot
    (∃ (B : Mettapedia.Logic.DeFinetti.BernoulliMixture),
      Mettapedia.Logic.DeFinetti.Represents B (fun i ω => ω i) μ ∧
      (∀ (n : ℕ) (xs₁ xs₂ : Fin n → Bool),
        Mettapedia.Logic.Exchangeability.countTrue xs₁ =
          Mettapedia.Logic.Exchangeability.countTrue xs₂ →
          B.prob xs₁ = B.prob xs₂)) ∧
    (∃! ν : Measure Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
      RepresentsLatentTheta (X := fun i ω => ω i) (μ := μ) ν) := by
  exact deFinettiExport_restrictedSolomonoff_totalOutput_implies_nupln_master_chain_and_unique_latentThetaMediator
    (M := M) (htot := htot)
    (hroot :=
      Mettapedia.Logic.SolomonoffExchangeable.RestrictedSolomonoffPrior.mu_nil_eq_one_of_programMassComplete
        (M := M) hcomplete)

/-- Recommended export: explicit true `LimitCone` for each per-`n` diagram. -/
def deFinettiExport_limitCone_perN (n : ℕ) :
    CategoryTheory.Limits.LimitCone (perNPrefixDiagramFunctor n) :=
  deFinettiStable_perNPrefixDiagramLimitCone (n := n)

end Mettapedia.CategoryTheory
