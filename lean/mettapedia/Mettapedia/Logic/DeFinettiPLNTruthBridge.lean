import Mettapedia.Logic.DeFinettiProjectiveCredalBridge
import Mettapedia.Logic.PLNTruthTower

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

namespace Mettapedia.Logic.DeFinettiPLNTruthBridge

open Mettapedia.Logic.DeFinetti
open Mettapedia.Logic.DeFinettiProjectiveCredalBridge
open Mettapedia.Logic.PLNIndefiniteTruth
open Mettapedia.Logic.PLNTruthTower
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

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

end Mettapedia.Logic.DeFinettiPLNTruthBridge
