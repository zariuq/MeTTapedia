import Mettapedia.Logic.ConceptOntology.ConstructionBase
import Mettapedia.Logic.DeFinettiProjectiveCredalBridge
import Mettapedia.Logic.StoneGunkDuality

/-!
# Construction-Base Predictive Bridge

This module repackages the existing de Finetti/projective finite-prefix
predictive layer in the same `That’s All` / `Open World` vocabulary used by the
construction-base API.

It introduces no new probability semantics. It gives names to two exact,
already-proved situations:

* `...ThatsAll` = every relevant finite-prefix predictive interval has width `0`,
* `...OpenWorld` = some relevant finite-prefix predictive interval has positive
  width.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic
open Mettapedia.Logic.DeFinetti
open Mettapedia.Logic.DeFinettiProjectiveCredalBridge
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

/-- A singleton external process-law family is predictively "that's all" when
every finite-prefix envelope has already collapsed to width `0`. -/
def externalPredictiveThatsAll
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Set (ExternalBoolProcessLaw Ω)) : Prop :=
  ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    externalPathLawPrefixEnvelopeWidth C n X = 0

/-- A compact bounded-measurable predictive carrier is predictively "that's
all" when every finite-prefix bounded-measurable envelope has width `0`. -/
def compactPredictiveThatsAll
    (C : BoundedMeasurableCredalSet (ℕ → Bool)) : Prop :=
  ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    boundedMeasurableEnvelopeWidth C
      (externalPathLawPrefixBoundedMeasurableGamble n X) = 0

/-- A Bernoulli-mixture family is predictively "that's all" when every
finite-prefix imprecise de Finetti interval has already collapsed to width
`0`. -/
def mixturePredictiveThatsAll
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n) : Prop :=
  ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    impreciseDeFinettiPrefixEnvelopeWidth C n
      (bernoulliMixturePrefixLawAt C hLaw n) X = 0

/-- A Bernoulli-mixture family is predictively open-world when some
finite-prefix predictive interval still has positive width. -/
def mixturePredictiveOpenWorld
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n) : Prop :=
  ∃ (n : ℕ) (X : Gamble (Fin n → Bool)),
    0 < impreciseDeFinettiPrefixEnvelopeWidth C n
      (bernoulliMixturePrefixLawAt C hLaw n) X

/-- A posterior external process law is a principal shadow when every
finite-prefix PLN midpoint/confidence coordinate has already collapsed to the
analytic posterior point. -/
def posteriorExternalPredictivePrincipalShadow
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω) : Prop :=
  ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
    ( externalPathLawPrefixEnvelopeMidpoint
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X
    , externalPathLawPrefixEnvelopeWidthComplement
        ({A} : Set (ExternalBoolProcessLaw Ω)) n X ) =
      ( (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
      , (1 : ℝ) )

/-- Compact bounded-measurable version of the same principal-shadow readout:
every finite-prefix midpoint/confidence coordinate has already collapsed to the
analytic posterior point on the shared compact carrier. -/
def posteriorCompactPredictivePrincipalShadow
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (A : ExternalBoolProcessLaw Ω) : Prop :=
  ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
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
      , (1 : ℝ) )

theorem externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A) :
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw Ω)) := by
  intro n X
  simpa using hCrown.prefixEnvelopeWidth_eq_zero n X

theorem compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureExternalCarrierCrown M k l hZ A) :
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw Ω))) := by
  intro n X
  simpa using hCrown.compactPrefixWidth_eq_zero n X

theorem posteriorExternalPredictivePrincipalShadow_of_posteriorSharedEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A) :
    posteriorExternalPredictivePrincipalShadow M k l hZ A := by
  intro n X
  simpa using
    posteriorBernoulliMixture_sharedEnvelopeCrown_prefixPLNCoordinates_eq_posterior
      hCrown n X

theorem posteriorCompactPredictivePrincipalShadow_of_posteriorSharedEnvelopeCrown
    {Ω : Type*} [MeasurableSpace Ω]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω}
    (hCrown : PosteriorBernoulliMixtureSharedEnvelopeCrown M k l hZ A) :
    posteriorCompactPredictivePrincipalShadow M k l hZ A := by
  intro n X
  simpa using
    posteriorBernoulliMixture_sharedEnvelopeCrown_compactPLNCoordinates_eq_posterior
      hCrown n X

theorem posteriorBernoulliMixture_canonical_externalPredictivePrincipalShadow
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    posteriorExternalPredictivePrincipalShadow M k l hZ A := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  exact
    posteriorExternalPredictivePrincipalShadow_of_posteriorSharedEnvelopeCrown
      (posteriorBernoulliMixture_canonicalSharedEnvelopeCrown M k l hZ)

theorem posteriorBernoulliMixture_canonical_compactPredictivePrincipalShadow
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    posteriorCompactPredictivePrincipalShadow M k l hZ A := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  exact
    posteriorCompactPredictivePrincipalShadow_of_posteriorSharedEnvelopeCrown
      (posteriorBernoulliMixture_canonicalSharedEnvelopeCrown M k l hZ)

theorem posteriorBernoulliMixture_canonical_externalPredictiveThatsAll
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  have hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A := by
    exact externalBoolProcessLawOf_realizes_bernoulliMixture_of_represents
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
      (M.posteriorBernoulliMixture k l hZ)
      (bernoulliMixtureCanonicalProcessMeasure_represents
        (M.posteriorBernoulliMixture k l hZ))
  exact externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown
    (posteriorBernoulliMixture_sharedEnvelopeCrown M k l hZ A hRealize)

theorem posteriorBernoulliMixture_canonical_compactPredictiveThatsAll
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  have hRealize :
      BernoulliMixtureExternalProcessRealization
        (M.posteriorBernoulliMixture k l hZ) A := by
    exact externalBoolProcessLawOf_realizes_bernoulliMixture_of_represents
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
      (M.posteriorBernoulliMixture k l hZ)
      (bernoulliMixtureCanonicalProcessMeasure_represents
        (M.posteriorBernoulliMixture k l hZ))
  exact compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
    (posteriorBernoulliMixture_externalCarrierCrown M k l hZ A hRealize)

theorem posteriorBernoulliMixture_canonical_externalPredictiveThatsAll_and_prefixWitness_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      (posteriorBernoulliMixturePrefixProcessWitness M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  rcases
      posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_prefixWitness_iff_zeroInteriorMixingMass
        M k l hZ with
    ⟨hCrown, hIff⟩
  exact
    ⟨externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown hCrown, hIff⟩

theorem posteriorBernoulliMixture_canonical_externalPredictiveThatsAll_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      ((∃ carrier : CredalPrevisionSet (ℕ → Bool),
          posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier) ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  rcases
      posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
        M k l hZ with
    ⟨hCrown, hIff⟩
  exact
    ⟨externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown hCrown, hIff⟩

theorem posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_prefixWitness_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) ∧
      (posteriorBernoulliMixturePrefixProcessWitness M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  rcases
      posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_prefixWitness_iff_zeroInteriorMixingMass
        M k l hZ with
    ⟨hCrown, hIff⟩
  have hCompact :
      compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) := by
    exact
      compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
        hCrown.processEnvelopeCrown.externalCarrierCrown
  exact
    ⟨hCompact, hIff⟩

theorem posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) ∧
      ((∃ carrier : CredalPrevisionSet (ℕ → Bool),
          posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier) ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  rcases
      posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
        M k l hZ with
    ⟨hCrown, hIff⟩
  have hCompact :
      compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) := by
    exact
      compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
        hCrown.processEnvelopeCrown.externalCarrierCrown
  exact
    ⟨hCompact, hIff⟩

theorem posteriorBernoulliMixture_canonical_externalPredictiveThatsAll_and_processLawCrown_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      (PosteriorBernoulliMixtureProcessLawCrown M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_canonical_externalPredictiveThatsAll M k l hZ,
      posteriorBernoulliMixture_processLawCrown_iff_zeroInteriorMixingMass M k l hZ⟩

theorem posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_processLawCrown_iff_zeroInteriorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) ∧
      (PosteriorBernoulliMixtureProcessLawCrown M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_canonical_compactPredictiveThatsAll M k l hZ,
      posteriorBernoulliMixture_processLawCrown_iff_zeroInteriorMixingMass M k l hZ⟩

theorem posteriorBernoulliMixture_canonical_externalPredictiveThatsAll_and_noPrefixCarrierWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      ∀ carrier : CredalPrevisionSet (ℕ → Bool),
        ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  rcases
      posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_noPrefixCarrierWitness_of_interiorMixingMass
        M k l hZ hInterior with
    ⟨hCrown, hNoWitness⟩
  exact
    ⟨externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown hCrown,
      hNoWitness⟩

theorem posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_noPrefixCarrierWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) ∧
      ∀ carrier : CredalPrevisionSet (ℕ → Bool),
        ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness M k l hZ carrier := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  rcases
      posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_noPrefixCarrierWitness_of_interiorMixingMass
        M k l hZ hInterior with
    ⟨hCrown, hNoWitness⟩
  have hCompact :
      compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) := by
    exact
      compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
        hCrown.processEnvelopeCrown.externalCarrierCrown
  exact
    ⟨hCompact, hNoWitness⟩

theorem posteriorBernoulliMixture_canonical_externalPredictiveThatsAll_and_noPrefixWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  rcases
      posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_noPrefixWitness_of_interiorMixingMass
        M k l hZ hInterior with
    ⟨hCrown, hNoWitness⟩
  exact
    ⟨externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown hCrown,
      hNoWitness⟩

theorem posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_noPrefixWitness_of_interiorMixingMass
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  rcases
      posteriorBernoulliMixture_canonicalSharedEnvelopeCrown_and_noPrefixWitness_of_interiorMixingMass
        M k l hZ hInterior with
    ⟨hCrown, hNoWitness⟩
  have hCompact :
      compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) := by
    exact
      compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
        hCrown.processEnvelopeCrown.externalCarrierCrown
  exact
    ⟨hCompact, hNoWitness⟩

theorem posteriorBernoulliMixture_canonical_externalPredictiveThatsAll_and_noPrefixWitness_of_mixedEvidence
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hk : 0 < k) (hl : 0 < l) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  exact
    ⟨posteriorBernoulliMixture_canonical_externalPredictiveThatsAll M k l hZ,
      not_posteriorBernoulliMixturePrefixProcessWitness_of_mixedEvidence
        M k l hZ hk hl⟩

theorem posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_noPrefixWitness_of_mixedEvidence
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (hk : 0 < k) (hl : 0 < l) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool)))) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness M k l hZ := by
  let hcoord : ∀ i : ℕ, Measurable (CategoryTheory.coordProcess i) := by
    intro i
    exact measurable_pi_apply i
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure
        (M.posteriorBernoulliMixture k l hZ))
      CategoryTheory.coordProcess
      hcoord
  exact
    ⟨posteriorBernoulliMixture_canonical_compactPredictiveThatsAll M k l hZ,
      not_posteriorBernoulliMixturePrefixProcessWitness_of_mixedEvidence
        M k l hZ hk hl⟩

theorem posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    externalPredictiveThatsAll
      ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
        Set (ExternalBoolProcessLaw Ω)) := by
  exact externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown
    (posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
      M X μ hX hrep obs hZ)

theorem posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω))) := by
  exact compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
    (posteriorBernoulliMixture_conditionedTail_externalCarrierCrown
      M X μ hX hrep obs hZ)

theorem posteriorBernoulliMixture_conditionedTail_externalPredictivePrincipalShadow
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    posteriorExternalPredictivePrincipalShadow
      M
      (Mettapedia.Logic.Exchangeability.countTrue obs)
      (Mettapedia.Logic.Exchangeability.countFalse obs)
      hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) := by
  exact
    posteriorExternalPredictivePrincipalShadow_of_posteriorSharedEnvelopeCrown
      (posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
        M X μ hX hrep obs hZ)

theorem posteriorBernoulliMixture_conditionedTail_compactPredictivePrincipalShadow
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    posteriorCompactPredictivePrincipalShadow
      M
      (Mettapedia.Logic.Exchangeability.countTrue obs)
      (Mettapedia.Logic.Exchangeability.countFalse obs)
      hZ
      (conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ) := by
  exact
    posteriorCompactPredictivePrincipalShadow_of_posteriorSharedEnvelopeCrown
      (posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown
        M X μ hX hrep obs hZ)

theorem posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll_and_prefixWitness_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    externalPredictiveThatsAll
      ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
        Set (ExternalBoolProcessLaw Ω)) ∧
      (posteriorBernoulliMixturePrefixProcessWitness
          M
          (Mettapedia.Logic.Exchangeability.countTrue obs)
          (Mettapedia.Logic.Exchangeability.countFalse obs)
          hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  rcases
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_prefixWitness_iff_zeroInteriorMixingMass
        M X μ hX hrep obs hZ with
    ⟨hCrown, hIff⟩
  exact
    ⟨externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown hCrown, hIff⟩

theorem posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    externalPredictiveThatsAll
      ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
        Set (ExternalBoolProcessLaw Ω)) ∧
      ((∃ carrier : CredalPrevisionSet (ℕ → Bool),
          posteriorBernoulliMixturePrefixProcessCarrierWitness
            M
            (Mettapedia.Logic.Exchangeability.countTrue obs)
            (Mettapedia.Logic.Exchangeability.countFalse obs)
            hZ carrier) ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  rcases
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
        M X μ hX hrep obs hZ with
    ⟨hCrown, hIff⟩
  exact
    ⟨externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown hCrown, hIff⟩

theorem posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll_and_prefixWitness_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω))) ∧
      (posteriorBernoulliMixturePrefixProcessWitness
          M
          (Mettapedia.Logic.Exchangeability.countTrue obs)
          (Mettapedia.Logic.Exchangeability.countFalse obs)
          hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  rcases
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_prefixWitness_iff_zeroInteriorMixingMass
        M X μ hX hrep obs hZ with
    ⟨hCrown, hIff⟩
  have hCompact :
      compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
            Set (ExternalBoolProcessLaw Ω))) := by
    exact
      compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
        hCrown.processEnvelopeCrown.externalCarrierCrown
  exact
    ⟨hCompact, hIff⟩

theorem posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω))) ∧
      ((∃ carrier : CredalPrevisionSet (ℕ → Bool),
          posteriorBernoulliMixturePrefixProcessCarrierWitness
            M
            (Mettapedia.Logic.Exchangeability.countTrue obs)
            (Mettapedia.Logic.Exchangeability.countFalse obs)
            hZ carrier) ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  rcases
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_prefixCarrierWitness_exists_iff_zeroInteriorMixingMass
        M X μ hX hrep obs hZ with
    ⟨hCrown, hIff⟩
  have hCompact :
      compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
            Set (ExternalBoolProcessLaw Ω))) := by
    exact
      compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
        hCrown.processEnvelopeCrown.externalCarrierCrown
  exact
    ⟨hCompact, hIff⟩

theorem posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll_and_processCarrierCrown_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    externalPredictiveThatsAll
      ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
        Set (ExternalBoolProcessLaw Ω)) ∧
      (PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
          M obs hZ μ X hX hrep ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll
        M X μ hX hrep obs hZ,
      posteriorBernoulliMixture_conditionedTail_processCarrierCrown_iff_zeroInteriorMixingMass
        M X μ hX hrep obs hZ⟩

theorem posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll_and_processCarrierCrown_iff_zeroInteriorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0) :
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω))) ∧
      (PosteriorBernoulliMixtureConditionedTailProcessCarrierCrown
          M obs hZ μ X hX hrep ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    ⟨posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll
        M X μ hX hrep obs hZ,
      posteriorBernoulliMixture_conditionedTail_processCarrierCrown_iff_zeroInteriorMixingMass
        M X μ hX hrep obs hZ⟩

theorem posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll_and_noPrefixCarrierWitness_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    externalPredictiveThatsAll
      ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
        Set (ExternalBoolProcessLaw Ω)) ∧
      ∀ carrier : CredalPrevisionSet (ℕ → Bool),
        ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness
          M
          (Mettapedia.Logic.Exchangeability.countTrue obs)
          (Mettapedia.Logic.Exchangeability.countFalse obs)
          hZ
          carrier := by
  rcases
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_noPrefixCarrierWitness_of_interiorMixingMass
        M X μ hX hrep obs hZ hInterior with
    ⟨hCrown, hNoWitness⟩
  exact
    ⟨externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown hCrown,
      hNoWitness⟩

theorem posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll_and_noPrefixCarrierWitness_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω))) ∧
      ∀ carrier : CredalPrevisionSet (ℕ → Bool),
        ¬ posteriorBernoulliMixturePrefixProcessCarrierWitness
          M
          (Mettapedia.Logic.Exchangeability.countTrue obs)
          (Mettapedia.Logic.Exchangeability.countFalse obs)
          hZ
          carrier := by
  rcases
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_noPrefixCarrierWitness_of_interiorMixingMass
        M X μ hX hrep obs hZ hInterior with
    ⟨hCrown, hNoWitness⟩
  have hCompact :
      compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
            Set (ExternalBoolProcessLaw Ω))) := by
    exact
      compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
        hCrown.processEnvelopeCrown.externalCarrierCrown
  exact
    ⟨hCompact, hNoWitness⟩

theorem posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll_and_noPrefixWitness_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    externalPredictiveThatsAll
      ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
        Set (ExternalBoolProcessLaw Ω)) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness
          M
          (Mettapedia.Logic.Exchangeability.countTrue obs)
          (Mettapedia.Logic.Exchangeability.countFalse obs)
          hZ := by
  rcases
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_noPrefixWitness_of_interiorMixingMass
        M X μ hX hrep obs hZ hInterior with
    ⟨hCrown, hNoWitness⟩
  exact
    ⟨externalPredictiveThatsAll_of_posteriorSharedEnvelopeCrown hCrown,
      hNoWitness⟩

theorem posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll_and_noPrefixWitness_of_interiorMixingMass
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (hInterior : 0 < M.mixingMeasure (Set.Ioo (0 : ℝ) 1)) :
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω))) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness
          M
          (Mettapedia.Logic.Exchangeability.countTrue obs)
          (Mettapedia.Logic.Exchangeability.countFalse obs)
          hZ := by
  rcases
      posteriorBernoulliMixture_conditionedTail_sharedEnvelopeCrown_and_noPrefixWitness_of_interiorMixingMass
        M X μ hX hrep obs hZ hInterior with
    ⟨hCrown, hNoWitness⟩
  have hCompact :
      compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
            Set (ExternalBoolProcessLaw Ω))) := by
    exact
      compactPredictiveThatsAll_of_posteriorExternalCarrierCrown
        hCrown.processEnvelopeCrown.externalCarrierCrown
  exact
    ⟨hCompact, hNoWitness⟩

theorem posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll_and_noPrefixWitness_of_mixedEvidence
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (hk : 0 < Mettapedia.Logic.Exchangeability.countTrue obs)
    (hl : 0 < Mettapedia.Logic.Exchangeability.countFalse obs) :
    externalPredictiveThatsAll
      ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
        Set (ExternalBoolProcessLaw Ω)) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness
          M
          (Mettapedia.Logic.Exchangeability.countTrue obs)
          (Mettapedia.Logic.Exchangeability.countFalse obs)
          hZ := by
  exact
    ⟨posteriorBernoulliMixture_conditionedTail_externalPredictiveThatsAll
        M X μ hX hrep obs hZ,
      not_posteriorBernoulliMixturePrefixProcessWitness_of_mixedEvidence
        M
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs)
        hZ hk hl⟩

theorem posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll_and_noPrefixWitness_of_mixedEvidence
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (hk : 0 < Mettapedia.Logic.Exchangeability.countTrue obs)
    (hl : 0 < Mettapedia.Logic.Exchangeability.countFalse obs) :
    compactPredictiveThatsAll
      (externalPathLawBoundedMeasurableCompactCredalSet
        ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
          Set (ExternalBoolProcessLaw Ω))) ∧
      ¬ posteriorBernoulliMixturePrefixProcessWitness
          M
          (Mettapedia.Logic.Exchangeability.countTrue obs)
          (Mettapedia.Logic.Exchangeability.countFalse obs)
          hZ := by
  exact
    ⟨posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll
        M X μ hX hrep obs hZ,
      not_posteriorBernoulliMixturePrefixProcessWitness_of_mixedEvidence
        M
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs)
        hZ hk hl⟩

theorem externalPredictiveThatsAll_singleton
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ExternalBoolProcessLaw Ω) :
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw Ω)) := by
  intro n X
  unfold externalPathLawPrefixEnvelopeWidth credalEnvelopeWidth
  have hSingleton :
      externalPathLawPrefixCredalSet ({A} : Set (ExternalBoolProcessLaw Ω)) n =
        ({A.prefixPrevision n} : CredalPrevisionSet (Fin n → Bool)) := by
    ext P
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hBA : B = A := by
        simpa using hB
      subst B
      simp
    · intro hP
      exact ⟨A, by simp, by simpa using hP⟩
  rw [hSingleton, lowerEnvelope_singleton, upperEnvelope_singleton]
  ring

theorem bernoulliMixture_canonical_externalPredictiveThatsAll_and_realization
    (M : BernoulliMixture) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure M)
        CategoryTheory.coordProcess
        bernoulliMixtureCanonical_coordProcess_measurable
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      BernoulliMixtureExternalProcessRealization M A := by
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure M)
      CategoryTheory.coordProcess
      bernoulliMixtureCanonical_coordProcess_measurable
  exact
    ⟨externalPredictiveThatsAll_singleton A,
      bernoulliMixtureCanonicalExternalProcessRealization M⟩

theorem bernoulliMixture_singletonExternalPredictors_agree_of_realizations
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {M : BernoulliMixture}
    {A : ExternalBoolProcessLaw Ω₁} {B : ExternalBoolProcessLaw Ω₂}
    (hA : BernoulliMixtureExternalProcessRealization M A)
    (hB : BernoulliMixtureExternalProcessRealization M B) :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      A.prefixPrevision n X = B.prefixPrevision n X := by
  intro n X
  rw [hA n X, hB n X]

theorem posteriorBernoulliMixture_singletonExternalPredictors_agree_of_externalCarrierCrowns
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {M : BernoulliMixture} {k l : ℕ}
    {hZ : M.countEvidenceMass k l ≠ 0}
    {A : ExternalBoolProcessLaw Ω₁} {B : ExternalBoolProcessLaw Ω₂}
    (hA : PosteriorBernoulliMixtureExternalCarrierCrown M k l hZ A)
    (hB : PosteriorBernoulliMixtureExternalCarrierCrown M k l hZ B) :
    ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      A.prefixPrevision n X = B.prefixPrevision n X := by
  intro n X
  rw [hA.prefixPrevision_eq_posterior n X, hB.prefixPrevision_eq_posterior n X]

theorem exchangeable_exists_singletonExternalPredictor
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hμ : MeasureTheory.IsProbabilityMeasure μ)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : Mettapedia.Logic.Exchangeability.InfiniteExchangeable X μ) :
    ∃ (M : BernoulliMixture) (A : ExternalBoolProcessLaw (ℕ → Bool)),
      DeFinetti.Represents M X μ ∧
      externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
        BernoulliMixtureExternalProcessRealization M A := by
  letI : MeasureTheory.IsProbabilityMeasure μ := hμ
  rcases (exchangeable_iff_bernoulliMixture X μ hX).1 hexch with ⟨M, hRep⟩
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure M)
      CategoryTheory.coordProcess
      (by
        intro i
        exact measurable_pi_apply i)
  refine ⟨M, A, hRep, ?_⟩
  simpa [A] using bernoulliMixture_canonical_externalPredictiveThatsAll_and_realization M

theorem mixturePredictiveThatsAll_of_prefixAgreement
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (hC : C.Nonempty)
    (hAgree : ∀ (n : ℕ) (X : Gamble (Fin n → Bool)),
      ∀ M : BernoulliMixture, ∀ hM : M ∈ C,
      ∀ N : BernoulliMixture, ∀ hN : N ∈ C,
        ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X =
          ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) :
    mixturePredictiveThatsAll C hLaw := by
  intro n X
  exact
    impreciseDeFinettiPrefixEnvelopeWidth_eq_zero_of_mixtureAgreement
      C n (bernoulliMixturePrefixLawAt C hLaw n) hC X (hAgree n X)

theorem mixturePredictiveOpenWorld_of_prefixDisagreement
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (n : ℕ) (X : Gamble (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X <
        ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) :
    mixturePredictiveOpenWorld C hLaw := by
  exact ⟨n, X,
    impreciseDeFinetti_prefixDisagreement_envelopeWidth_pos
      C hLaw n X hM hN hlt⟩

theorem predictiveEvidenceAlgebra_isGunky :
    Mettapedia.Foundations.Gunk.IsGunky (TopologicalSpace.Clopens (ℕ → Bool)) :=
  Mettapedia.Foundations.Gunk.isGunky_clopens_cantor

theorem predictiveEvidenceStoneSpace_perfect :
    PerfectSpace
      (Mettapedia.Foundations.Gunk.StoneSpace
        (TopologicalSpace.Clopens (ℕ → Bool))) := by
  exact
    (Mettapedia.Foundations.Gunk.isGunky_iff_perfect_stoneSpace).1
      predictiveEvidenceAlgebra_isGunky

theorem bernoulliMixture_canonical_externalPredictiveThatsAll_on_gunkyPerfectEvidenceAlgebra
    (M : BernoulliMixture) :
    let A : ExternalBoolProcessLaw (ℕ → Bool) :=
      ExternalBoolProcessLaw.ofProcess
        (bernoulliMixtureCanonicalProcessMeasure M)
        CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply i)
    externalPredictiveThatsAll ({A} : Set (ExternalBoolProcessLaw (ℕ → Bool))) ∧
      BernoulliMixtureExternalProcessRealization M A ∧
      Mettapedia.Foundations.Gunk.IsGunky
        (TopologicalSpace.Clopens (ℕ → Bool)) ∧
      PerfectSpace
        (Mettapedia.Foundations.Gunk.StoneSpace
          (TopologicalSpace.Clopens (ℕ → Bool))) := by
  let A : ExternalBoolProcessLaw (ℕ → Bool) :=
    ExternalBoolProcessLaw.ofProcess
      (bernoulliMixtureCanonicalProcessMeasure M)
      CategoryTheory.coordProcess
      (by
        intro i
        exact measurable_pi_apply i)
  refine ⟨?_, ?_, predictiveEvidenceAlgebra_isGunky, predictiveEvidenceStoneSpace_perfect⟩
  · exact externalPredictiveThatsAll_singleton A
  · exact bernoulliMixtureCanonicalExternalProcessRealization M

theorem mixturePredictiveOpenWorld_on_gunkyPerfectEvidenceAlgebra_of_prefixDisagreement
    (C : Set BernoulliMixture)
    (hLaw : ∀ M : BernoulliMixture, M ∈ C → ∀ n : ℕ,
      BernoulliMixturePrefixLaw M n)
    (n : ℕ) (X : Gamble (Fin n → Bool))
    {M N : BernoulliMixture} (hM : M ∈ C) (hN : N ∈ C)
    (hlt :
      ((bernoulliMixturePrefixLawAt C hLaw n) M hM).toPrecisePrevision X <
        ((bernoulliMixturePrefixLawAt C hLaw n) N hN).toPrecisePrevision X) :
    mixturePredictiveOpenWorld C hLaw ∧
      Mettapedia.Foundations.Gunk.IsGunky
        (TopologicalSpace.Clopens (ℕ → Bool)) ∧
      PerfectSpace
        (Mettapedia.Foundations.Gunk.StoneSpace
          (TopologicalSpace.Clopens (ℕ → Bool))) := by
  refine ⟨?_, predictiveEvidenceAlgebra_isGunky, predictiveEvidenceStoneSpace_perfect⟩
  exact mixturePredictiveOpenWorld_of_prefixDisagreement C hLaw n X hM hN hlt

end Mettapedia.Logic.ConceptOntology
