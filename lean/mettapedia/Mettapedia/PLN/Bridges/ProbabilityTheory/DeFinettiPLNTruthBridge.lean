import Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mettapedia.PLN.TruthValues.PLNTruthTower

/-!
# Posterior de Finetti Prefix Envelopes as PLN Width-Complement ITVs

This file gives the narrowest typed-PLN bridge for Crown 2 that stays honest
about the current mathematical boundary.

For each finite posterior prefix gamble in the unit interval, the already
proved singleton posterior projective spec yields a width-complement ITV source
and therefore a typed ITV.  Since the prefix credal set is singleton, the ITV
collapses exactly to the analytic posterior prefix prevision with width `0` and
credibility `1`.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.DeFinettiPLNTruthBridge

open scoped ENNReal
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

/-- The one-bit true indicator gamble is a unit gamble. -/
theorem oneBitTrueGamble_mem_unit :
    ∀ ω : Fin 1 → Bool, oneBitTrueGamble ω ∈ Set.Icc (0 : ℝ) 1 := by
  intro ω
  unfold oneBitTrueGamble PrecisePrevision.FiniteWeights.atomGamble
  by_cases h : ω = oneBitTruePrefix
  · simp [h]
  · simp [h]

/-- The one-bit false indicator gamble is a unit gamble. -/
theorem oneBitFalseGamble_mem_unit :
    ∀ ω : Fin 1 → Bool, oneBitFalseGamble ω ∈ Set.Icc (0 : ℝ) 1 := by
  intro ω
  unfold oneBitFalseGamble PrecisePrevision.FiniteWeights.atomGamble
  by_cases h : ω = oneBitFalsePrefix
  · simp [h]
  · simp [h]

/-- The posterior singleton finite-prefix credal set is literally the singleton
analytic posterior prefix prevision. -/
@[simp] theorem posteriorBernoulliMixturePrefixCredalSet_eq_singleton
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    bernoulliMixturePrefixCredalSet
        (posteriorBernoulliMixtureSet M k l hZ) n
        (posteriorBernoulliMixturePrefixLawAt M k l hZ n) =
      ({(bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision} :
        CredalPrevisionSet (Fin n → Bool)) := by
  ext P
  constructor
  · rintro ⟨Q, hQ, hP⟩
    have hQEq : Q = M.posteriorBernoulliMixture k l hZ := by
      simpa [posteriorBernoulliMixtureSet] using hQ
    subst Q
    simpa using hP
  · intro hP
    have hPEq :
        P =
          (bernoulliMixturePrefixLaw_analytic
            (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision := by
      simpa using hP
    subst P
    refine ⟨M.posteriorBernoulliMixture k l hZ, rfl, ?_⟩
    rfl

/-- The lower envelope of the posterior singleton finite-prefix credal set is
the analytic posterior prefix prevision itself. -/
@[simp] theorem posteriorBernoulliMixturePrefixLowerEnvelope_eq_posterior
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool)) :
    impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureSet M k l hZ) n
        (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold impreciseDeFinettiPrefixLowerEnvelope
  rw [posteriorBernoulliMixturePrefixCredalSet_eq_singleton M k l n hZ,
    lowerEnvelope_singleton]

/-- The upper envelope of the posterior singleton finite-prefix credal set is
the analytic posterior prefix prevision itself. -/
@[simp] theorem posteriorBernoulliMixturePrefixUpperEnvelope_eq_posterior
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool)) :
    impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureSet M k l hZ) n
        (posteriorBernoulliMixturePrefixLawAt M k l hZ n) X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold impreciseDeFinettiPrefixUpperEnvelope
  rw [posteriorBernoulliMixturePrefixCredalSet_eq_singleton M k l n hZ,
    upperEnvelope_singleton]

/-- Source data for viewing a posterior singleton finite-prefix credal envelope
as a PLN ITV whose credibility is the complement of credal width. -/
noncomputable def posteriorBernoulliMixturePrefixWidthComplementITVSource
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    ProjectiveCredalWidthComplementITVSource.{0, 0} PUnit (Fin n → Bool) :=
  ProjectiveCredalWidthComplementITVSource.finite
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n))
    (posteriorBernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
      M k l hZ n)
    X hX

/-- The untyped PLN ITV associated with a posterior singleton finite-prefix
credal envelope under the width-complement convention. -/
noncomputable def posteriorBernoulliMixturePrefixWidthComplementITV
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) : ITV :=
  projectiveCredalWidthComplementITV
    (posteriorBernoulliMixturePrefixWidthComplementITVSource M k l n hZ X hX)

/-- The typed PLN ITV associated with a posterior singleton finite-prefix
credal envelope under the width-complement convention. -/
noncomputable def posteriorBernoulliMixturePrefixTypedWidthComplementITV
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    TypedITV (projectiveCredalWidthComplementITVSemantics.{0, 0} PUnit
      (Fin n → Bool)) :=
  TypedITV.fromProjectiveCredalWidthComplement
    (posteriorBernoulliMixturePrefixWidthComplementITVSource M k l n hZ X hX)

/-- Source data for the PLN width-complement ITV obtained from a general
posterior de-Finetti family, rather than a singleton posterior mixture.  The
nonempty-family hypothesis is the honest compatibility gate. -/
noncomputable def posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    ProjectiveCredalWidthComplementITVSource.{0, 0} PUnit (Fin n → Bool) :=
  ProjectiveCredalWidthComplementITVSource.finite
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n))
    (bernoulliMixturePrefixProjectiveSpec_hasCompatibleCompletion
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)
      (posteriorBernoulliMixtureFamilySet_nonempty C k l hZ hC))
    X hX

/-- The untyped PLN ITV associated with a general posterior de-Finetti family
under the width-complement convention. -/
noncomputable def posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) : ITV :=
  projectiveCredalWidthComplementITV
    (posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
      C k l n hZ hC X hX)

/-- The typed PLN ITV associated with a general posterior de-Finetti family
under the width-complement convention. -/
noncomputable def posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    TypedITV (projectiveCredalWidthComplementITVSemantics.{0, 0} PUnit
      (Fin n → Bool)) :=
  TypedITV.fromProjectiveCredalWidthComplement
    (posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
      C k l n hZ hC X hX)

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_lower
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
      C k l n hZ hC X hX).lower =
      impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
    projectiveCredalWidthComplementITV
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).globalNaturalExtension X =
      impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_upper
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
      C k l n hZ hC X hX).upper =
      impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
    projectiveCredalWidthComplementITV
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    upperEnvelope
      (bernoulliMixturePrefixProjectiveSpec
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).projectiveLimitCredalSet X =
      impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_upperEnvelope]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_width
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
      C k l n hZ hC X hX).width =
      impreciseDeFinettiPrefixEnvelopeWidth
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
    projectiveCredalWidthComplementITV ITV.width
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).globalEnvelopeWidth X =
      impreciseDeFinettiPrefixEnvelopeWidth
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_credibility
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
      C k l n hZ hC X hX).credibility =
      impreciseDeFinettiPrefixEnvelopeWidthComplement
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
    projectiveCredalWidthComplementITV
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).globalEnvelopeWidthComplement X =
      impreciseDeFinettiPrefixEnvelopeWidthComplement
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_strength
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
      C k l n hZ hC X hX).strength =
      impreciseDeFinettiPrefixEnvelopeMidpoint
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITV
    projectiveCredalWidthComplementITV
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).globalEnvelopeMidpoint X =
      impreciseDeFinettiPrefixEnvelopeMidpoint
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_lower
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
      C k l n hZ hC X hX).lower =
      impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_lower]
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).globalNaturalExtension X =
      impreciseDeFinettiPrefixLowerEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_upper
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
      C k l n hZ hC X hX).upper =
      impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_upper]
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    upperEnvelope
      (bernoulliMixturePrefixProjectiveSpec
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).projectiveLimitCredalSet X =
      impreciseDeFinettiPrefixUpperEnvelope
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_upperEnvelope]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_width
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
      C k l n hZ hC X hX).width =
      impreciseDeFinettiPrefixEnvelopeWidth
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_width]
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).globalEnvelopeWidth X =
      impreciseDeFinettiPrefixEnvelopeWidth
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_credibility
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
      C k l n hZ hC X hX).credibility =
      impreciseDeFinettiPrefixEnvelopeWidthComplement
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_credibility]
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).globalEnvelopeWidthComplement X =
      impreciseDeFinettiPrefixEnvelopeWidthComplement
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement]

@[simp] theorem posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_midpoint
    (C : Set BernoulliMixture) (k l n : ℕ)
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass k l ≠ 0)
    (hC : C.Nonempty)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
      C k l n hZ hC X hX).midpoint =
      impreciseDeFinettiPrefixEnvelopeMidpoint
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X := by
  unfold posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_midpoint]
  unfold posteriorBernoulliMixtureFamilyPrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureFamilySet C k l hZ) n
      (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n)).globalEnvelopeMidpoint X =
      impreciseDeFinettiPrefixEnvelopeMidpoint
        (posteriorBernoulliMixtureFamilySet C k l hZ) n
        (posteriorBernoulliMixtureFamilyPrefixLawAt C k l hZ n) X
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeMidpoint]

@[simp] theorem posteriorBernoulliMixturePrefixWidthComplementITV_lower
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixWidthComplementITV M k l n hZ X hX).lower =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold posteriorBernoulliMixturePrefixWidthComplementITV
    projectiveCredalWidthComplementITV
  unfold posteriorBernoulliMixturePrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).globalNaturalExtension X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  rw [bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension]
  exact posteriorBernoulliMixturePrefixLowerEnvelope_eq_posterior M k l n hZ X

@[simp] theorem posteriorBernoulliMixturePrefixWidthComplementITV_upper
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixWidthComplementITV M k l n hZ X hX).upper =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold posteriorBernoulliMixturePrefixWidthComplementITV
    projectiveCredalWidthComplementITV
  unfold posteriorBernoulliMixturePrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    upperEnvelope
      (bernoulliMixturePrefixProjectiveSpec
        (posteriorBernoulliMixtureSet M k l hZ) n
        (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).projectiveLimitCredalSet X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  rw [bernoulliMixturePrefixProjectiveSpec_upperEnvelope]
  exact posteriorBernoulliMixturePrefixUpperEnvelope_eq_posterior M k l n hZ X

@[simp] theorem posteriorBernoulliMixturePrefixWidthComplementITV_width
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixWidthComplementITV M k l n hZ X hX).width = 0 := by
  unfold posteriorBernoulliMixturePrefixWidthComplementITV
    projectiveCredalWidthComplementITV ITV.width
  unfold posteriorBernoulliMixturePrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).globalEnvelopeWidth X = 0
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth]
  exact posteriorBernoulliMixturePrefixEnvelopeWidth_eq_zero M k l hZ n X

@[simp] theorem posteriorBernoulliMixturePrefixWidthComplementITV_credibility
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixWidthComplementITV M k l n hZ X hX).credibility = 1 := by
  unfold posteriorBernoulliMixturePrefixWidthComplementITV
    projectiveCredalWidthComplementITV
  unfold posteriorBernoulliMixturePrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).globalEnvelopeWidthComplement X = 1
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement]
  exact posteriorBernoulliMixturePrefixEnvelopeWidthComplement_eq_one M k l hZ n X

@[simp] theorem posteriorBernoulliMixturePrefixWidthComplementITV_strength
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixWidthComplementITV M k l n hZ X hX).strength =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold ITV.strength
  rw [posteriorBernoulliMixturePrefixWidthComplementITV_lower M k l n hZ X hX,
    posteriorBernoulliMixturePrefixWidthComplementITV_upper M k l n hZ X hX]
  ring

@[simp] theorem posteriorBernoulliMixturePrefixTypedWidthComplementITV_lower
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixTypedWidthComplementITV M k l n hZ X hX).lower =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold posteriorBernoulliMixturePrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_lower]
  unfold posteriorBernoulliMixturePrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).globalNaturalExtension X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  rw [bernoulliMixturePrefixProjectiveSpec_globalNaturalExtension]
  exact posteriorBernoulliMixturePrefixLowerEnvelope_eq_posterior M k l n hZ X

@[simp] theorem posteriorBernoulliMixturePrefixTypedWidthComplementITV_upper
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixTypedWidthComplementITV M k l n hZ X hX).upper =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold posteriorBernoulliMixturePrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_upper]
  unfold posteriorBernoulliMixturePrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    upperEnvelope
      (bernoulliMixturePrefixProjectiveSpec
        (posteriorBernoulliMixtureSet M k l hZ) n
        (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).projectiveLimitCredalSet X =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X
  rw [bernoulliMixturePrefixProjectiveSpec_upperEnvelope]
  exact posteriorBernoulliMixturePrefixUpperEnvelope_eq_posterior M k l n hZ X

@[simp] theorem posteriorBernoulliMixturePrefixTypedWidthComplementITV_width
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixTypedWidthComplementITV M k l n hZ X hX).width = 0 := by
  unfold posteriorBernoulliMixturePrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_width]
  unfold posteriorBernoulliMixturePrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).globalEnvelopeWidth X = 0
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidth]
  exact posteriorBernoulliMixturePrefixEnvelopeWidth_eq_zero M k l hZ n X

@[simp] theorem posteriorBernoulliMixturePrefixTypedWidthComplementITV_credibility
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixTypedWidthComplementITV M k l n hZ X hX).credibility = 1 := by
  unfold posteriorBernoulliMixturePrefixTypedWidthComplementITV
  rw [TypedITV.fromProjectiveCredalWidthComplement_credibility]
  unfold posteriorBernoulliMixturePrefixWidthComplementITVSource
    ProjectiveCredalWidthComplementITVSource.finite
  change
    (bernoulliMixturePrefixProjectiveSpec
      (posteriorBernoulliMixtureSet M k l hZ) n
      (posteriorBernoulliMixturePrefixLawAt M k l hZ n)).globalEnvelopeWidthComplement X = 1
  rw [bernoulliMixturePrefixProjectiveSpec_globalEnvelopeWidthComplement]
  exact posteriorBernoulliMixturePrefixEnvelopeWidthComplement_eq_one M k l hZ n X

@[simp] theorem posteriorBernoulliMixturePrefixTypedWidthComplementITV_midpoint
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (posteriorBernoulliMixturePrefixTypedWidthComplementITV M k l n hZ X hX).midpoint =
      (bernoulliMixturePrefixLaw_analytic
        (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision X := by
  unfold TypedITV.midpoint TypedITV.value projectiveCredalWidthComplementITVSemantics
  exact posteriorBernoulliMixturePrefixWidthComplementITV_strength M k l n hZ X hX

/-- Finite-source Revision count packets supply the same positive/negative
count ledger used by the posterior de Finetti singleton ITV.  The posterior
ITV therefore has the existing exact singleton readout: lower, upper, and
strength are the analytic posterior prefix prevision, width is `0`, and
credibility is `1`.

This is intentionally a finite-batch/conjugate-subfamily bridge: the theorem
does not say that arbitrary exchangeable second-order truth values are Beta,
nor that every credal family collapses to a singleton. -/
theorem revisionMany_countPairEvidence_posteriorPrefixWidthComplementITV_readout
    (M : BernoulliMixture) (xs : List (ℕ × ℕ)) (n : ℕ)
    (hZ : M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).pos =
        (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
      (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).neg =
        (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
      (posteriorBernoulliMixturePrefixWidthComplementITV M
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX).lower =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n).toPrecisePrevision X ∧
      (posteriorBernoulliMixturePrefixWidthComplementITV M
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX).upper =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n).toPrecisePrevision X ∧
      (posteriorBernoulliMixturePrefixWidthComplementITV M
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX).width = 0 ∧
      (posteriorBernoulliMixturePrefixWidthComplementITV M
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX).credibility = 1 ∧
      (posteriorBernoulliMixturePrefixWidthComplementITV M
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX).strength =
        (bernoulliMixturePrefixLaw_analytic
          (M.posteriorBernoulliMixture
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n).toPrecisePrevision X := by
  exact ⟨revisionMany_countPairEvidence_pos xs,
    revisionMany_countPairEvidence_neg xs,
    posteriorBernoulliMixturePrefixWidthComplementITV_lower M
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX,
    posteriorBernoulliMixturePrefixWidthComplementITV_upper M
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX,
    posteriorBernoulliMixturePrefixWidthComplementITV_width M
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX,
    posteriorBernoulliMixturePrefixWidthComplementITV_credibility M
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX,
    posteriorBernoulliMixturePrefixWidthComplementITV_strength M
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ X hX⟩

/-- Finite-source Revision count packets also feed the general posterior
de-Finetti credal-family envelope.  For any prior mixture in the family, its
memberwise next-success and next-failure Bayes ratios lie inside the updated
one-bit lower/upper envelopes.

This is the imprecise-probability Revision reading: the finite count ledger is
shared with `revisionMany`, while the conclusion remains an envelope
membership statement over the whole posterior family, not a singleton or
endpoint-tightness claim. -/
theorem revisionMany_countPairEvidence_posteriorFamilyRatio_mem_prefixEnvelopes
    (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0)
    {M : BernoulliMixture} (hM : M ∈ C) :
    (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).pos =
        (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
      (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).neg =
        (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
      impreciseDeFinettiPrefixLowerEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ 1)
          oneBitTrueGamble ≤
        M.countEvidenceMass ((xs.map Prod.fst).sum + 1) (xs.map Prod.snd).sum /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ∧
      M.countEvidenceMass ((xs.map Prod.fst).sum + 1) (xs.map Prod.snd).sum /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≤
        impreciseDeFinettiPrefixUpperEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ 1)
          oneBitTrueGamble ∧
      impreciseDeFinettiPrefixLowerEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ 1)
          oneBitFalseGamble ≤
        M.countEvidenceMass (xs.map Prod.fst).sum ((xs.map Prod.snd).sum + 1) /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ∧
      M.countEvidenceMass (xs.map Prod.fst).sum ((xs.map Prod.snd).sum + 1) /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≤
        impreciseDeFinettiPrefixUpperEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ 1)
          oneBitFalseGamble := by
  exact ⟨revisionMany_countPairEvidence_pos xs,
    revisionMany_countPairEvidence_neg xs,
    (posteriorBernoulliMixtureFamily_trueRatio_mem_prefixEnvelope C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ hM).1,
    (posteriorBernoulliMixtureFamily_trueRatio_mem_prefixEnvelope C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ hM).2,
    (posteriorBernoulliMixtureFamily_falseRatio_mem_prefixEnvelope C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ hM).1,
    (posteriorBernoulliMixtureFamily_falseRatio_mem_prefixEnvelope C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ hM).2⟩

/-- Finite-source Revision count packets inherit the Walley GLB/LUB endpoint
reading of the general posterior de-Finetti family.  Any scalar lower bound on
all memberwise true/false posterior Bayes ratios is below the corresponding
lower envelope, and any scalar upper bound is above the corresponding upper
envelope.

This packages the existing semantic family endpoint theorems with the finite
`revisionMany` count ledger.  It is not a proof-theoretic tightness claim about
a HOL cut, and it does not assert that the family collapses to a singleton. -/
theorem revisionMany_countPairEvidence_posteriorFamilyRatio_envelope_glb_lub
    (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0)
    (hC : C.Nonempty)
    {aTrueLower aTrueUpper aFalseLower aFalseUpper : ℝ}
    (haTrueLower : ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
      aTrueLower ≤
        M.countEvidenceMass ((xs.map Prod.fst).sum + 1) (xs.map Prod.snd).sum /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum)
    (haTrueUpper : ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
      M.countEvidenceMass ((xs.map Prod.fst).sum + 1) (xs.map Prod.snd).sum /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≤
        aTrueUpper)
    (haFalseLower : ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
      aFalseLower ≤
        M.countEvidenceMass (xs.map Prod.fst).sum ((xs.map Prod.snd).sum + 1) /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum)
    (haFalseUpper : ∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
      M.countEvidenceMass (xs.map Prod.fst).sum ((xs.map Prod.snd).sum + 1) /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≤
        aFalseUpper) :
    (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).pos =
        (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
      (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).neg =
        (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
      aTrueLower ≤
        impreciseDeFinettiPrefixLowerEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ 1)
          oneBitTrueGamble ∧
      impreciseDeFinettiPrefixUpperEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ 1)
          oneBitTrueGamble ≤
        aTrueUpper ∧
      aFalseLower ≤
        impreciseDeFinettiPrefixLowerEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ 1)
          oneBitFalseGamble ∧
      impreciseDeFinettiPrefixUpperEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) 1
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ 1)
          oneBitFalseGamble ≤
        aFalseUpper := by
  exact ⟨revisionMany_countPairEvidence_pos xs,
    revisionMany_countPairEvidence_neg xs,
    posteriorBernoulliMixtureFamily_trueRatio_lowerEnvelope_greatestLowerBound C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ hC haTrueLower,
    posteriorBernoulliMixtureFamily_trueRatio_upperEnvelope_leastUpperBound C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ hC haTrueUpper,
    posteriorBernoulliMixtureFamily_falseRatio_lowerEnvelope_greatestLowerBound C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ hC haFalseLower,
    posteriorBernoulliMixtureFamily_falseRatio_upperEnvelope_leastUpperBound C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ hC haFalseUpper⟩

/-- Finite-source Revision count packets feed a genuine non-singleton PLN ITV
source for the posterior de-Finetti family.  The ITV readouts are exactly the
Walley lower/upper envelope, width, width-complement credibility, and midpoint
of the posterior family for the supplied finite-prefix gamble.

This is the real family-level ITV bridge for Revision.  It keeps the same
finite count ledger as `revisionMany`, but it intentionally preserves the
credal width of the posterior family instead of collapsing it. -/
theorem revisionMany_countPairEvidence_posteriorFamilyWidthComplementITV_readout
    (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0)
    (hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).pos =
        (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
      (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).neg =
        (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
      (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).lower =
        impreciseDeFinettiPrefixLowerEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X ∧
      (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).upper =
        impreciseDeFinettiPrefixUpperEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X ∧
      (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).width =
        impreciseDeFinettiPrefixEnvelopeWidth
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X ∧
      (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).credibility =
        impreciseDeFinettiPrefixEnvelopeWidthComplement
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X ∧
      (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).strength =
        impreciseDeFinettiPrefixEnvelopeMidpoint
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X := by
  exact ⟨revisionMany_countPairEvidence_pos xs,
    revisionMany_countPairEvidence_neg xs,
    posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_lower C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX,
    posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_upper C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX,
    posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_width C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX,
    posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_credibility C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX,
    posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_strength C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX⟩

/-- Finite-source Revision count packets also feed the typed posterior-family
width-complement ITV.  The typed readouts are the same Walley family-envelope
readouts as the untyped ITV, with `midpoint` as the typed strength coordinate.

This is the typed non-singleton Revision surface: it preserves the posterior
family's credal width and records the projective-credal semantics in the
`TypedITV` index. -/
theorem revisionMany_countPairEvidence_posteriorFamilyTypedWidthComplementITV_readout
    (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0)
    (hC : C.Nonempty) (n : ℕ)
    (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).pos =
        (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
      (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).neg =
        (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
      (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).lower =
        impreciseDeFinettiPrefixLowerEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X ∧
      (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).upper =
        impreciseDeFinettiPrefixUpperEnvelope
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X ∧
      (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).width =
        impreciseDeFinettiPrefixEnvelopeWidth
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X ∧
      (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).credibility =
        impreciseDeFinettiPrefixEnvelopeWidthComplement
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X ∧
      (posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX).midpoint =
        impreciseDeFinettiPrefixEnvelopeMidpoint
          (posteriorBernoulliMixtureFamilySet C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ) n
          (posteriorBernoulliMixtureFamilyPrefixLawAt C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X := by
  exact ⟨revisionMany_countPairEvidence_pos xs,
    revisionMany_countPairEvidence_neg xs,
    posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_lower C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX,
    posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_upper C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX,
    posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_width C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX,
    posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_credibility C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX,
    posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV_midpoint C
      (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZ hC X hX⟩

/-- Finite-source Revision count packets feed posterior-family ITVs whose
one-bit true/false intervals contain every updated family member's Bayes ratio.

This is the consumer-facing membership theorem for Revision's family-level ITV:
the same finite count ledger supplies `revisionMany`, and the
width-complement intervals keep the whole posterior family visible instead of
silently replacing it by a singleton point estimate. -/
theorem revisionMany_countPairEvidence_posteriorFamilyRatio_mem_widthComplementITVs
    (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
    (hZ : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0)
    (hC : C.Nonempty)
    {M : BernoulliMixture} (hM : M ∈ C) :
    (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).pos =
        (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
      (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence)).neg =
        (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
      (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum 1 hZ hC
          oneBitTrueGamble oneBitTrueGamble_mem_unit).lower ≤
        M.countEvidenceMass ((xs.map Prod.fst).sum + 1) (xs.map Prod.snd).sum /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ∧
      M.countEvidenceMass ((xs.map Prod.fst).sum + 1) (xs.map Prod.snd).sum /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≤
        (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum 1 hZ hC
          oneBitTrueGamble oneBitTrueGamble_mem_unit).upper ∧
      (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum 1 hZ hC
          oneBitFalseGamble oneBitFalseGamble_mem_unit).lower ≤
        M.countEvidenceMass (xs.map Prod.fst).sum ((xs.map Prod.snd).sum + 1) /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ∧
      M.countEvidenceMass (xs.map Prod.fst).sum ((xs.map Prod.snd).sum + 1) /
          M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≤
        (posteriorBernoulliMixtureFamilyPrefixWidthComplementITV C
          (xs.map Prod.fst).sum (xs.map Prod.snd).sum 1 hZ hC
          oneBitFalseGamble oneBitFalseGamble_mem_unit).upper := by
  have hMem :=
    revisionMany_countPairEvidence_posteriorFamilyRatio_mem_prefixEnvelopes
      C xs hZ hM
  refine ⟨hMem.1, hMem.2.1, ?_, ?_, ?_, ?_⟩
  · simpa [posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_lower]
      using hMem.2.2.1
  · simpa [posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_upper]
      using hMem.2.2.2.1
  · simpa [posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_lower]
      using hMem.2.2.2.2.1
  · simpa [posteriorBernoulliMixtureFamilyPrefixWidthComplementITV_upper]
      using hMem.2.2.2.2.2

end Mettapedia.PLN.Bridges.ProbabilityTheory.DeFinettiPLNTruthBridge
