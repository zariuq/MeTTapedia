import Mettapedia.Logic.ConceptOntology.ConstructionBasePredictive
import Mettapedia.Logic.DeFinettiPLNTruthBridge

/-!
# Construction-Base Predictive ITV Bridge

This module isolates the exact typed-ITV readout layer for the posterior
de Finetti predictive surface.

It does not add new probability semantics. It packages the already-proved
posterior prefix ITV collapse so downstream consumers can cite one small leaf
module instead of reopening the heavier predictive bridge.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic
open Mettapedia.Logic.DeFinetti
open Mettapedia.Logic.DeFinettiProjectiveCredalBridge
open Mettapedia.Logic.DeFinettiPLNTruthBridge
open Mettapedia.ProbabilityTheory.ImpreciseProbability

/-- The coordinate process on `Bool^ℕ` is measurable. Hoisted here so the
canonical posterior law is a named object rather than an embedded tactic block
inside theorem statements. -/
theorem posteriorCanonical_coordProcess_measurable (i : ℕ) :
    Measurable (CategoryTheory.coordProcess i) := by
  exact measurable_pi_apply (a := i)

/-- The canonical external posterior process law on `Bool^ℕ`. -/
noncomputable def posteriorCanonicalExternalBoolProcessLaw
    (M : BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    ExternalBoolProcessLaw (ℕ → Bool) :=
  ExternalBoolProcessLaw.ofProcess
    (bernoulliMixtureCanonicalProcessMeasure
      (M.posteriorBernoulliMixture k l hZ))
    CategoryTheory.coordProcess
    (fun i => posteriorCanonical_coordProcess_measurable i)

/-- The exact typed posterior prefix ITV readout for a finite gamble. -/
noncomputable def posteriorPrefixTypedReadoutITV
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (G : Gamble (Fin n → Bool))
    (hG : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1) :=
  posteriorBernoulliMixturePrefixTypedWidthComplementITV M k l n hZ G hG

/-- The exact analytic posterior prefix prevision for the same finite gamble. -/
noncomputable def posteriorPrefixReadoutPrevision
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (G : Gamble (Fin n → Bool)) : ℝ :=
  (bernoulliMixturePrefixLaw_analytic
    (M.posteriorBernoulliMixture k l hZ) n).toPrecisePrevision G

/-- The exact typed posterior prefix ITV readout for a conditioned-tail finite
gamble. -/
noncomputable def posteriorConditionedTailPrefixTypedReadoutITV
    (M : BernoulliMixture) {m : ℕ} (obs : Fin m → Bool) (n : ℕ)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (G : Gamble (Fin n → Bool))
    (hG : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1) :=
  posteriorBernoulliMixturePrefixTypedWidthComplementITV
    M
    (Mettapedia.Logic.Exchangeability.countTrue obs)
    (Mettapedia.Logic.Exchangeability.countFalse obs)
    n hZ G hG

/-- The exact analytic posterior prefix prevision for the same conditioned-tail
finite gamble. -/
noncomputable def posteriorConditionedTailPrefixReadoutPrevision
    (M : BernoulliMixture) {m : ℕ} (obs : Fin m → Bool) (n : ℕ)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (G : Gamble (Fin n → Bool)) : ℝ :=
  (bernoulliMixturePrefixLaw_analytic
    (M.posteriorBernoulliMixture
      (Mettapedia.Logic.Exchangeability.countTrue obs)
      (Mettapedia.Logic.Exchangeability.countFalse obs)
      hZ) n).toPrecisePrevision G

/-- Construction-base-facing exact typed ITV package for the canonical
posterior predictive object. -/
theorem posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_prefixTypedWidthComplementITV_exact
    (M : BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (G : Gamble (Fin n → Bool))
    (hG : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1) :
    compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({posteriorCanonicalExternalBoolProcessLaw M k l hZ} :
            Set (ExternalBoolProcessLaw (ℕ → Bool)))) ∧
      (posteriorPrefixTypedReadoutITV M k l n hZ G hG).lower =
        posteriorPrefixReadoutPrevision M k l n hZ G ∧
      (posteriorPrefixTypedReadoutITV M k l n hZ G hG).upper =
        posteriorPrefixReadoutPrevision M k l n hZ G ∧
      (posteriorPrefixTypedReadoutITV M k l n hZ G hG).width = 0 ∧
      (posteriorPrefixTypedReadoutITV M k l n hZ G hG).credibility = 1 ∧
      (posteriorPrefixTypedReadoutITV M k l n hZ G hG).midpoint =
        posteriorPrefixReadoutPrevision M k l n hZ G := by
  refine ⟨posteriorBernoulliMixture_canonical_compactPredictiveThatsAll M k l hZ, ?_, ?_, ?_, ?_, ?_⟩
  · exact posteriorBernoulliMixturePrefixTypedWidthComplementITV_lower M k l n hZ G hG
  · exact posteriorBernoulliMixturePrefixTypedWidthComplementITV_upper M k l n hZ G hG
  · exact posteriorBernoulliMixturePrefixTypedWidthComplementITV_width M k l n hZ G hG
  · exact posteriorBernoulliMixturePrefixTypedWidthComplementITV_credibility M k l n hZ G hG
  · exact posteriorBernoulliMixturePrefixTypedWidthComplementITV_midpoint M k l n hZ G hG

/-- Construction-base-facing exact typed ITV package for the conditioned-tail
posterior predictive object. -/
theorem posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll_and_prefixTypedWidthComplementITV_exact
    {Ω : Type*} [MeasurableSpace Ω]
    (M : BernoulliMixture) (X : ℕ → Ω → Bool) (μ : MeasureTheory.Measure Ω)
    (hX : ∀ i : ℕ, Measurable (X i))
    (hrep : DeFinetti.Represents M X μ) {m : ℕ}
    (obs : Fin m → Bool)
    (hZ :
      M.countEvidenceMass
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs) ≠ 0)
    (n : ℕ)
    (G : Gamble (Fin n → Bool))
    (hG : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1) :
    compactPredictiveThatsAll
        (externalPathLawBoundedMeasurableCompactCredalSet
          ({conditionedTailExternalBoolProcessLaw M X μ hX hrep obs hZ} :
            Set (ExternalBoolProcessLaw Ω))) ∧
      (posteriorConditionedTailPrefixTypedReadoutITV M obs n hZ G hG).lower =
        posteriorConditionedTailPrefixReadoutPrevision M obs n hZ G ∧
      (posteriorConditionedTailPrefixTypedReadoutITV M obs n hZ G hG).upper =
        posteriorConditionedTailPrefixReadoutPrevision M obs n hZ G ∧
      (posteriorConditionedTailPrefixTypedReadoutITV M obs n hZ G hG).width = 0 ∧
      (posteriorConditionedTailPrefixTypedReadoutITV M obs n hZ G hG).credibility = 1 ∧
      (posteriorConditionedTailPrefixTypedReadoutITV M obs n hZ G hG).midpoint =
        posteriorConditionedTailPrefixReadoutPrevision M obs n hZ G := by
  refine ⟨posteriorBernoulliMixture_conditionedTail_compactPredictiveThatsAll
      M X μ hX hrep obs hZ, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      posteriorBernoulliMixturePrefixTypedWidthComplementITV_lower
        M
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs)
        n hZ G hG
  · exact
      posteriorBernoulliMixturePrefixTypedWidthComplementITV_upper
        M
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs)
        n hZ G hG
  · exact
      posteriorBernoulliMixturePrefixTypedWidthComplementITV_width
        M
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs)
        n hZ G hG
  · exact
      posteriorBernoulliMixturePrefixTypedWidthComplementITV_credibility
        M
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs)
        n hZ G hG
  · exact
      posteriorBernoulliMixturePrefixTypedWidthComplementITV_midpoint
        M
        (Mettapedia.Logic.Exchangeability.countTrue obs)
        (Mettapedia.Logic.Exchangeability.countFalse obs)
        n hZ G hG

end Mettapedia.Logic.ConceptOntology
