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
13. `deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel` (canonical)
14. `deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted` (adapter)
15. `deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted` (adapter)
16. `deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel` (adapter)
17. `deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals` (adapter)
18. ~~`deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_strengthening`~~ (DEAD PATH — strengthening proven false)
19. `deFinettiExport_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted`
20. `deFinettiExport_restrictedSolomonoff_prefixLaw_implies_unique_latentThetaMediator`
21. `deFinettiExport_restrictedSolomonoff_totalOutput_implies_nupln_master_chain_and_unique_latentThetaMediator`
22. `deFinettiExport_restrictedSolomonoff_totalOutput_and_programMassComplete_implies_nupln_master_chain_and_unique_latentThetaMediator`

## Markov-Core Route (Recommended)
1. Use `deFinettiExport_markovCoreUniversal_iff_crossNPackageFamily` to align
   Markov-core universality with the cross-`n` package family.
2. Use `deFinettiExport_markovCore_to_kleisliRoute` to obtain the concrete
   Kleisli(Giry) `IsLimit`-ready witness bundle.
3. Canonical endpoint:
   `deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`.
4. Use unrestricted/full-`IsLimit` theorems only as adapters when you have an
   explicit commutes-to-Markov bridge (`CommutesToMarkovBridge`).
5. Structural boundaries (proven negative results):
   - `deFinettiExport_not_commutesToMarkovBridge_unrestricted`: the commutes-to-Markov
     bridge is not derivable in unrestricted `Kleisli(MeasCat.Giry)`.
   - `deFinettiExport_not_allSourcesKleisli_unrestricted`: the unrestricted all-sources
     Kleisli mediator property is FALSE (counting-measure counterexample).
   - `deFinettiExport_not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening`:
     the unrestricted strengthening hypothesis is also false.
6. Finite-mass equivalence (corrected strengthening):
   `deFinettiExport_allSourcesKleisli_finiteMass_iff_markovOnly` proves that
   finite-mass universality is equivalent to Markov-only universality.
   The fully unrestricted version is false (counting-measure counterexample),
   but the finite-mass restriction is the maximal correct strengthening.

## Migration Map (Legacy -> Canonical/Adapter)
- `deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted`
  -> `deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted`
- `deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted`
  -> `deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted`
- `deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel`
  -> `deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel`
- `deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals`
  -> `deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals`
- Legacy full-target route names:
  -> `deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`
     when the markov-only endpoint is sufficient.
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
finitary invariance imply canonical Markov-only Kleisli(Giry)
mediator-uniqueness for `iidSequenceKernelTheta`, using the default all-sources
kernel witness internally. This route avoids the unrestricted
commutes-to-Markov bridge assumption. -/
theorem deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      GlobalIIDConeMediatorUnique_markovOnly
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) := by
  exact
    deFinettiStable_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
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

/-- Recommended alias theorem (full-target route): Markov-core universal
mediation plus global finitary invariance and unrestricted all-sources Kleisli
universality yield a concrete global Kleisli(Giry) `IsLimit` witness for
`iidSequenceKernelTheta`, without a separate mediator-uniqueness hypothesis. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal huniv

/-- Explicit adapter alias for the unrestricted all-sources Kleisli full-target
route.

Prefer the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal huniv

/-- Recommended alias theorem (full-target route): same as above but taking an
unrestricted all-sources kernel-level factorization witness directly. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv :
      KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal huniv

/-- Explicit adapter alias for the unrestricted all-sources
kernel-factorization full-target route.

Prefer the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv :
      KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal huniv

/-- Assumption-bearing adapter (full-target route): compose all-sources
kernel mediation with an explicit commutes-to-Markov bridge, then discharge the
global Kleisli(Giry) `IsLimit` goal in one hop.

Canonical endpoint remains the Markov-only theorem
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`.
The bridge assumption is not derivable in unrestricted `Kleisli(MeasCat.Giry)`;
see `deFinettiExport_not_commutesToMarkovBridge_unrestricted`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel
      (Y := Y) (Ω := Ω) X hcore hglobal huniv hmarkov_of_commutes

/-- Explicit adapter alias for the all-sources-kernel full-target route.

Prefer the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel
      (Y := Y) (Ω := Ω) X hcore hglobal huniv hmarkov_of_commutes

/-- Compatibility wrapper retaining an explicit iid-prefix-law input.
Prefer
`deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel`.
-/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel_and_prefixLaw
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal huniv hmarkov_of_commutes

/-- Structural boundary: in unrestricted `Kleisli(MeasCat.Giry)`, raw
permutation-commutation does not imply Markovness of source kernels. -/
theorem deFinettiExport_not_commutesToMarkovBridge_unrestricted :
    ¬ CommutesToMarkovBridge :=
  not_commutesToMarkovBridge_unrestricted

/-- Structural boundary: the unrestricted all-sources Kleisli mediator property
is FALSE. The counting measure on `ℕ → Bool` from PUnit commutes with all
permutations but admits no mediator through iid(θ), because every singleton
has iid-measure 0 for all θ while counting measure assigns mass 1. -/
theorem deFinettiExport_not_allSourcesKleisli_unrestricted :
    ¬ KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
  deFinettiStable_not_allSourcesKleisli_unrestricted

/-- Structural boundary: the unrestricted strengthening hypothesis is also false
(it implies the unrestricted universality refuted above). The correct
strengthening is the finite-mass version; see
`deFinettiExport_allSourcesKleisli_finiteMass_iff_markovOnly`. -/
theorem deFinettiExport_not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    ¬ DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening :=
  deFinettiStable_not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening
    hglobal hunivDefault

/-- Canonical export theorem (full-target route, crux-isolated):
compose
1. default all-sources qualitative de Finetti,
2. a measurable embedding of latent moments (`thetaMomentSeq`),
3. kernel-level prefix law for `iidSequenceKernelTheta`, and
4. a commutes⇒Markov bridge for source kernels,
then discharge the global Kleisli(Giry) `IsLimit` goal in one hop. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (_hEmb : MeasurableEmbedding latentThetaMomentSeq)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  have hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) :=
    iidSequenceKernelTheta_represents_latentDirac (hprefix := hprefix)
  have huniv :
      KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := hrepDirac)
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      (hmarkov_of_commutes := hmarkov_of_commutes)
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal huniv

/-- Compatibility alias of the embedding-driven prefix-law endpoint.
Prefer the latent-Dirac canonical theorem
`deFinettiExport_markovCore_to_kleisliIsLimit_canonical`, which no longer
threads explicit prefix-law/moment-embedding hypotheses through the API. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_canonical_of_prefixLaw_and_thetaMomentEmbedding
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (_hEmb : MeasurableEmbedding latentThetaMomentSeq)
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  have hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) :=
    iidSequenceKernelTheta_represents_latentDirac (hprefix := hprefix)
  have huniv :
      KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := hrepDirac)
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      (hmarkov_of_commutes := hmarkov_of_commutes)
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal huniv

/-- Preferred export theorem from an explicit latent-Dirac witness.

This canonical route avoids an external strict-prefix-law hypothesis and
dispatches through the latent-Dirac all-sources bridge.
-/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_canonical
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  have huniv :
      KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
    allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := hrepDirac)
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      (hmarkov_of_commutes := hmarkov_of_commutes)
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal huniv

/-- Compatibility wrapper (full-target route, no explicit all-sources mediator
input) from an explicit latent-Dirac witness. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_canonical
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hrepDirac hmarkov_of_commutes

/-- Preferred wrapper from default all-sources qualitative de Finetti with no
external strict-prefix-law hypothesis. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_canonical
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal
      iidSequenceKernelTheta_represents_latentDirac_unconditional
      hmarkov_of_commutes

/-- **DEAD PATH**: The `hstrength` hypothesis
(`DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening`) is
proven false — see `deFinettiExport_not_allSourcesKleisli_unrestricted`.
This theorem is vacuously true and retained only for backward compatibility.

Use the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly`
or the equivalent finite-mass version
`deFinettiExport_allSourcesKleisli_finiteMass_iff_markovOnly` instead. -/
@[deprecated
  deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
  (since := "2026-02-23")]
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_strengthening
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hstrength : DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_strengthening
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      hstrength

/-- Compatibility wrapper retaining explicit strict iid-prefix equations. Prefer
`deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`.
-/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hmarkov_of_commutes

/-- Preferred compatibility wrapper if your local context already carries
`StandardBorelSpace (ProbabilityMeasure LatentTheta)`, without requiring an
explicit strict-prefix-law hypothesis. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_standardBorelProbabilityMeasure
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    [StandardBorelSpace (ProbabilityMeasure LatentTheta)]
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hmarkov_of_commutes

/-- Preferred compatibility fallback when only `BorelSpace (FiniteMeasure LatentTheta)`
is available, without requiring an explicit strict-prefix-law hypothesis. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_finiteMeasureBorel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    [BorelSpace (FiniteMeasure LatentTheta)]
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  letI : BorelSpace (FiniteMeasure LatentTheta) := inferInstance
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hmarkov_of_commutes

/-- Compatibility middle-strength wrapper:
if finite-prefix marginals of `iidSequenceKernelTheta` are Bernoulli product
measures, derive the latent-Dirac witness internally and dispatch to the
canonical no-explicit-prefix-law endpoint.

Prefer
`deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals`
or the canonical markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefixPi :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal hprefixPi
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      hmarkov_of_commutes

/-- Explicit adapter alias for the default-all-sources prefix-`π`
middle-strength route.

Prefer the canonical Markov-only endpoint
`deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefixPi :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ))
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
      (Y := Y) (Ω := Ω) (X := X) hcore hglobal hprefixPi
      (hunivDefault := fun (Y' : Type) _ =>
        kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))
      hmarkov_of_commutes

/-- Deprecated compatibility wrapper (full-target route, standard-Borel probability-measure
upgrade): use when you want to thread an explicit
`StandardBorelSpace (ProbabilityMeasure LatentTheta)` assumption. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_standardBorelProbabilityMeasure
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    [StandardBorelSpace (ProbabilityMeasure LatentTheta)]
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_standardBorelProbabilityMeasure
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal iidSequenceKernelTheta_represents_latentDirac_unconditional
      hmarkov_of_commutes

/-- Deprecated convenience fallback wrapper (full-target route, finite-measure bridge path):
use this only when the preferred
`deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw`
(`ProbabilityMeasure`-Borel route) is not
available in the local environment.

This fallback is intentionally explicit and retained for compatibility; the
preferred route no longer requires explicit Borel assumptions at call sites. -/
theorem deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_finiteMeasureBorel
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    [BorelSpace (FiniteMeasure LatentTheta)]
    (hmarkov_of_commutes : CommutesToMarkovBridge) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  letI : BorelSpace (FiniteMeasure LatentTheta) := inferInstance
  exact
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_finiteMeasureBorel
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal iidSequenceKernelTheta_represents_latentDirac_unconditional
      hmarkov_of_commutes

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel_and_prefixLaw

attribute
  [deprecated
    deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_adapter_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_prefixPiMarginals

attribute
  [deprecated
    deFinettiExport_markovCore_to_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-20")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_thetaMomentEmbedding

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_canonical_of_prefixLaw_and_thetaMomentEmbedding

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_canonical

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_standardBorelProbabilityMeasure
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_standardBorelProbabilityMeasure

attribute
  [deprecated
    deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_of_finiteMeasureBorel
    (since := "2026-02-19")]
  deFinettiExport_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw_of_finiteMeasureBorel

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

/-- Recommended export: on discrete source measurable spaces, the default
qualitative all-sources witness upgrades to a measurable latent kernel
mediator. -/
theorem deFinettiExport_allSourcesKernel_discrete_of_allSourcesDefault
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (Y : Type) [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hκexch : KernelExchangeable (X := coordProcess) κ) :
    ∃! L : ProbabilityTheory.Kernel Y LatentTheta,
      KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) (fun y => L y) :=
  deFinettiStable_allSourcesKernel_discrete_of_allSourcesDefault
    (hunivDefault := hunivDefault) Y κ hκexch

/-- Recommended export: all-sources Markov-only Kleisli mediator property
implies Markov-only global mediator uniqueness for `iidSequenceKernelTheta`. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_allSourcesKleisli
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly) :
    GlobalIIDConeMediatorUnique_markovOnly (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_allSourcesKleisli
    (hcommutes := hcommutes) huniv

/-- Recommended canonical Markov-only one-hop route (no commutes⇒Markov
adapter): global finitary invariance implies Markov-only global mediator
uniqueness for the canonical `iidSequenceKernelTheta` cone, using the default
all-sources qualitative de Finetti witness and the canonical moment-embedding
bridge. The latent-Dirac witness is supplied internally. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    GlobalIIDConeMediatorUnique_markovOnly
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal := hglobal)
    (hunivDefault := fun (Y' : Type) _ =>
      kernelLatentThetaUniversalMediator_default_typeFamily (Y' := Y'))

/-- Compatibility wrapper retaining an explicit latent-Dirac witness.
Prefer
`deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel`.
-/
@[deprecated
  deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
  (since := "2026-02-20")]
theorem deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (_hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta))) :
    GlobalIIDConeMediatorUnique_markovOnly
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  deFinettiExport_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal := hglobal)

/-- Recommended export: strict iid prefix law + all-sources kernel-level latent
mediation imply all-sources Markov-only Kleisli universality directly. -/
theorem deFinettiExport_allSourcesKleisli_markovOnly_of_allSourcesKernel_and_prefixLaw
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly :=
  deFinettiStable_allSourcesKleisli_markovOnly_of_allSourcesKernel_and_prefixLaw
    (hprefix := hprefix) huniv

/-- Recommended export: unrestricted all-sources Kleisli mediator property
implies full global mediator uniqueness for `iidSequenceKernelTheta`. -/
theorem deFinettiExport_globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
    (hcommutes := hcommutes) huniv

/-- Recommended export: unrestricted all-sources kernel-level factorization
implies unrestricted all-sources Kleisli universality. -/
theorem deFinettiExport_allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted
    (huniv :
      KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
  deFinettiStable_allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted
    huniv

/-- Recommended export (converse direction): full global mediator uniqueness
for `iidSequenceKernelTheta` implies unrestricted all-sources Kleisli
universality. -/
theorem deFinettiExport_allSourcesKleisli_unrestricted_of_globalIIDConeMediatorUnique
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (hmed : GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
  deFinettiStable_allSourcesKleisli_unrestricted_of_globalIIDConeMediatorUnique
    (hcommutes := hcommutes) hmed

/-- Recommended export: unrestricted all-sources Kleisli universality is
equivalent to full global mediator uniqueness for `iidSequenceKernelTheta`. -/
theorem deFinettiExport_allSourcesKleisli_unrestricted_iff_globalIIDConeMediatorUnique
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted ↔
      GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  deFinettiStable_allSourcesKleisli_unrestricted_iff_globalIIDConeMediatorUnique
    (hcommutes := hcommutes)

/-- Recommended export (full target shape): unrestricted all-sources Kleisli
mediator property yields a concrete `IsLimit` witness for the
`iidSequenceKernelTheta` cone. -/
theorem deFinettiExport_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) :=
  deFinettiStable_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted
    (hcommutes := hcommutes) huniv

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

/-- Public API: finite-mass universality is equivalent to Markov-only
universality (given global finitary invariance).

This is the corrected strengthening: the fully unrestricted version is false
(counting-measure counterexample at `not_commutesToMarkovBridge_unrestricted`),
but finite-mass is proven equivalent to the Markov-only version. -/
theorem deFinettiExport_allSourcesKleisli_finiteMass_iff_markovOnly
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass ↔
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly :=
  deFinettiStable_allSourcesKleisli_finiteMass_iff_markovOnly hglobal

/-- Public API: finite-mass universality from global finitary invariance and
default all-sources qualitative witness. Fully proven, no hypotheses needed
beyond the standard de Finetti infrastructure. -/
theorem deFinettiExport_allSourcesKleisli_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_finiteMass :=
  deFinettiStable_allSourcesKleisli_finiteMass_of_globalFinitaryInvariance_and_defaultAllSourcesKernel
    hglobal hunivDefault

end Mettapedia.CategoryTheory
