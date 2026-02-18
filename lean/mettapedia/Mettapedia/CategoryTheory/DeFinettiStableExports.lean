import Mettapedia.CategoryTheory.DeFinettiPerNDiagram
import Mettapedia.CategoryTheory.DeFinettiGlobalFinitaryDiagram
import Mettapedia.CategoryTheory.DeFinettiKleisliGirySkeleton
import Mettapedia.CategoryTheory.DeFinettiSequenceKernelCone
import Mettapedia.CategoryTheory.DeFinettiMarkovCategoryBridge

/-!
# Stable Export Surface for Categorical de Finetti

This file is an internal stable alias layer.
Downstream modules should prefer importing
`Mettapedia.CategoryTheory.DeFinettiExports`.

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

/-- Stable alias: explicit iid-prefix factorization form at kernel level.
From a sequence-kernel cone object, obtain a unique latent `Theta` family with
both representation and finite-prefix iid-mixture equations. -/
theorem deFinettiStable_existsUnique_latentThetaKernel_with_iidPrefixFactorization_coord
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
  existsUnique_latentThetaKernel_with_iidPrefixFactorization_of_sequenceKernelConeObj
    (κ := κ)

/-- Stable alias: unique sequence-level mediator record packaging finite-prefix
iid factorization equations. -/
theorem deFinettiStable_existsUnique_kernelIIDPrefixMediator_of_sequenceKernelConeObj
    (κ : ProbabilityTheory.Kernel Y (ℕ → Bool))
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ →
      ∃! M : KernelIIDPrefixMediator (κ := κ),
        KernelRepresentsLatentTheta (X := coordProcess) κ M.latent :=
  existsUnique_kernelIIDPrefixMediator_of_sequenceKernelConeObj (κ := κ)

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

/-- Stable export: global finitary-permutation lifted commutation is equivalent
to `IsPrefixLawCone`. -/
theorem deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    IsPrefixLawCone (Ω := Ω) X μ ↔
      GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ :=
  isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes (Ω := Ω) X μ

/-- Stable export: one-hop bridge from global-lifted commutation to cross-`n`
mediator uniqueness packaging. -/
theorem deFinettiStable_globalLiftedPrefixLawConeCommutes_to_crossNPackage
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hglobal : GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ) :
    Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) := by
  refine ⟨exchangeableCrossNLimitPackage_of_isPrefixLawCone
    (Ω := Ω) X μ ?_⟩
  exact (deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
    (Ω := Ω) X μ).2 hglobal

/-- Stable export: for a fixed law `μ`, global finitary lifted commutation is
equivalent to having both:
1. the prefix-law cone predicate, and
2. a concrete cross-`n` mediator package witness. -/
theorem deFinettiStable_globalLiftedPrefixLawConeCommutes_iff_prefixCone_and_crossNPackage
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ ↔
      (IsPrefixLawCone (Ω := Ω) X μ ∧
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ)) := by
  constructor
  · intro hglobal
    refine ⟨?_, ?_⟩
    · exact (deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
        (Ω := Ω) X μ).2 hglobal
    · exact deFinettiStable_globalLiftedPrefixLawConeCommutes_to_crossNPackage
        (Ω := Ω) X μ hglobal
  · intro h
    exact (deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
      (Ω := Ω) X μ).1 h.1

/-- Stable export: true global Kleisli(Giry) `IsLimit` packaging is equivalent
to the global mediator uniqueness property for an iid-cone skeleton. -/
theorem deFinettiStable_isLimit_iff_globalIIDConeMediatorUnique
    (cone : KleisliGiryIIDConeSkeleton) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUnique cone :=
  isLimit_iff_globalIIDConeMediatorUnique cone

/-- Stable export: any true `IsLimit` witness implies the Markov-only
mediator-uniqueness property for the same cone. -/
theorem deFinettiStable_isLimit_implies_globalIIDConeMediatorUnique_markovOnly
    (cone : KleisliGiryIIDConeSkeleton)
    (hlim : CategoryTheory.Limits.IsLimit (cone.toCone)) :
    GlobalIIDConeMediatorUnique_markovOnly cone :=
  isLimit_implies_globalIIDConeMediatorUnique_markovOnly cone hlim

/-- Stable export: canonical all-sources strengthening of the kernel universal
mediator API. -/
theorem deFinettiStable_kernelUniversalMediator_allSources_default
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator_allSources (Ω := Ω) X :=
  kernelLatentThetaUniversalMediator_allSources_default (Ω := Ω) X

/-- Stable export: specialized `P Bool` form of the true global Kleisli(Giry)
`IsLimit` equivalence. -/
theorem deFinettiStable_isLimit_iff_globalIIDConeMediatorUniqueProbBool
    (cone : KleisliGiryProbBoolIIDCone) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUniqueProbBool cone :=
  isLimit_iff_globalIIDConeMediatorUniqueProbBool cone

/-- Stable export: horizon-`n` cylinder evaluation for `iidSequenceKernelTheta`,
assuming the canonical Dirac latent mediator interface. -/
theorem deFinettiStable_iidSequenceKernelTheta_prefix_apply_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) :=
  iidSequenceKernelTheta_prefix_apply_of_latentDirac hrep θ n xs

/-- Stable export: for the cone built from `iidSequenceKernelTheta`, true
`IsLimit` is equivalent to global mediator uniqueness. -/
theorem deFinettiStable_isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
      GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta hcommutes

/-- Stable export: derive the `iidSequenceKleisliHomTheta` commutation witness
from global finitary invariance of `iidSequenceKernelTheta`. -/
theorem deFinettiStable_iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta :=
  iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal

/-- Stable export: unconditional horizon-`n` prefix evaluation for
`iidSequenceKernelTheta` from global finitary invariance, via the canonical
latent-kernel extracted by the mediator chain. -/
theorem deFinettiStable_iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
        (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ) :=
  iidSequenceKernelTheta_prefix_apply_of_globalFinitaryInvariance hglobal θ n xs

/-- Stable export: no-extra-hypothesis (beyond global finitary invariance)
IsLimit-ready bundle for `iidSequenceKernelTheta`. -/
theorem deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance
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
  iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance hglobal

/-- Stable export: concrete `IsLimit` witness for the global Kleisli(Giry)
cone built from `iidSequenceKernelTheta`, assuming:
1. global finitary invariance, and
2. global mediator uniqueness for the induced cone. -/
theorem deFinettiStable_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmed :
      GlobalIIDConeMediatorUnique
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal))) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    ⟨(iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).isLimitOfMediatorUnique
      hmed⟩

/-- Stable export (Path-B): if finite-prefix marginals of `iidSequenceKernelTheta`
match Bernoulli product marginals, then the full Kleisli(Giry) IsLimit-ready
bundle follows in one hop. -/
theorem deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals
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
  iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals hprefix

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

/-- Stable export: exchangeability-induced per-`n` cone factorization through
the fixed-point limit object. -/
theorem deFinettiStable_exchangeablePerNLimitMediator_fac
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ)
    (j : PerNPermIndex n) :
    CategoryTheory.CategoryStruct.comp
      (exchangeablePerNLimitMediator (Ω := Ω) X μ n hcone)
      ((perNPrefixFixedPointsCone n).π.app j) =
    (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone).π.app j :=
  exchangeablePerNLimitMediator_fac (Ω := Ω) X μ n hcone j

/-- Stable export: uniqueness of the exchangeability-induced mediator via
`IsLimit.lift` uniqueness. -/
theorem deFinettiStable_exchangeablePerNLimitMediator_unique
    (X : ℕ → Ω → Bool) (μ : Measure Ω) (n : ℕ)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ)
    (m : PUnit ⟶ PerNPrefixFixedPoints n)
    (hm :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n hcone).π.app j) :
    m = exchangeablePerNLimitMediator (Ω := Ω) X μ n hcone :=
  exchangeablePerNLimitMediator_unique (Ω := Ω) X μ n hcone m hm

/-- Stable export: single rewrite bridge connecting kernel-level universal
mediator API to per-`n` limit-mediator uniqueness packaging. -/
theorem deFinettiStable_kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ExchangeablePerNLimitMediatorUnique (Ω := Ω) X :=
  kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique (Y := Y) (Ω := Ω) X

/-- Stable export: one-hop bridge from kernel-level universal mediator API to the
global cross-`n` package family. -/
theorem deFinettiStable_kernelLatentThetaUniversalMediator_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  kernelLatentThetaUniversalMediator_iff_crossNPackageFamily (Y := Y) (Ω := Ω) X

/-- Stable export: full practical qualitative chain in one theorem.
This packages:
1. kernel-level universal mediator API,
2. per-`n` mediator uniqueness package,
3. global lifted commutation → cross-`n` package witnesses. -/
theorem deFinettiStable_kernelUniversalMediator_endToEnd_globalChain
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      (ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ∧
        (∀ μ : Measure Ω, GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ →
          Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ))) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact
        (deFinettiStable_kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
          (Y := Y) (Ω := Ω) X).1 h
    · intro μ hglobal
      exact deFinettiStable_globalLiftedPrefixLawConeCommutes_to_crossNPackage
        (Ω := Ω) X μ hglobal
  · intro h
    exact
      (deFinettiStable_kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
        (Y := Y) (Ω := Ω) X).2 h.1

/-- Stable export: Markov-core universal mediation plus global finitary
invariance gives the practical Kleisli(Giry) `IsLimit`-ready route. -/
theorem deFinettiStable_markovCore_to_kleisliRoute
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
  refine ⟨?_, ?_⟩
  · exact
      (kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
        (Y := Y) (Ω := Ω) X).1 hcore
  · exact
      deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance
        hglobal

/-- Stable export: Markov-core universal mediation plus global finitary
invariance and mediator uniqueness yield a concrete global Kleisli(Giry)
`IsLimit` witness for the `iidSequenceKernelTheta` cone. -/
theorem deFinettiStable_markovCore_to_kleisliIsLimit
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
  refine ⟨?_, ?_⟩
  · exact
      (kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
        (Y := Y) (Ω := Ω) X).1 hcore
  · exact
      deFinettiStable_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique
        (hglobal := hglobal) hmed

/-- Stable export: global cross-`n` categorical package from prefix-law
exchangeability. -/
def deFinettiStable_exchangeableCrossNLimitPackage_of_isPrefixLawCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ) :
    ExchangeableCrossNLimitPackage (Ω := Ω) X μ :=
  exchangeableCrossNLimitPackage_of_isPrefixLawCone (Ω := Ω) X μ hcone

/-- Stable export: substantive equivalence between the per-`n` uniqueness package
and the global cross-`n` package family. -/
theorem deFinettiStable_perNUnique_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  exchangeablePerNLimitMediatorUnique_iff_crossNPackageFamily (Ω := Ω) X

/-- Stable export: non-essential check theorem using cross-`n` uniqueness. -/
theorem deFinettiStable_exchangeableCrossNLimitPackage_mediator_eq_of_fac
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (pkg : ExchangeableCrossNLimitPackage (Ω := Ω) X μ)
    (n : ℕ) (m : PUnit ⟶ PerNPrefixFixedPoints n)
    (hm :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n pkg.hcone).π.app j) :
    m = pkg.mediator n :=
  exchangeableCrossNLimitPackage_mediator_eq_of_fac (Ω := Ω) X μ pkg n m hm

/-- Stable export: uniqueness check between any two mediators satisfying the same
cross-`n` factorization equations. -/
theorem deFinettiStable_exchangeableCrossNLimitPackage_mediators_eq_of_fac
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
  exchangeableCrossNLimitPackage_mediators_eq_of_fac
    (Ω := Ω) X μ pkg n m₁ m₂ hm₁ hm₂

end Mettapedia.CategoryTheory
