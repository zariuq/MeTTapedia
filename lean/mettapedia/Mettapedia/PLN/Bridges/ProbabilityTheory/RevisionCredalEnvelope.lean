import Mettapedia.PLN.Bridges.ProbabilityTheory.DeFinettiPLNTruthBridge
import Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionBayesianGrounding

/-!
# Revision Credal-Envelope Profile

This file packages the existing family-level de-Finetti / Walley envelope
surface for PLN Revision.

The profile deliberately separates the finite Beta-conjugate subfamily from the
general posterior-family envelope: the former gives a point-valued sufficient
statistic update, while the latter preserves the lower/upper credal width when
the admissible de-Finetti mixing family is not a singleton.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionCredalEnvelope

open scoped ENNReal
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
open Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.PLN.Bridges.ProbabilityTheory.DeFinettiPLNTruthBridge
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
open Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionBayesianGrounding

/-- Reader-facing profile for the credal-envelope side of Revision.

The fields are existing theorems, collected so the public PLN package exposes
both sides of the honest Revision story:

* finite raw evidence revises by Beta-Bernoulli sufficient statistics; and
* a non-singleton de-Finetti posterior family revises to a Walley lower/upper
  envelope, not to an unearned point value.
-/
structure RevisionCredalEnvelopeProfile where
  finiteBayesianGrounding : RevisionBayesianGroundingProfile
  posteriorFamilyRatioMembership :
    ∀ (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
      (hZ : ∀ M : BernoulliMixture, M ∈ C →
        M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0)
      {M : BernoulliMixture}, M ∈ C →
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
            oneBitFalseGamble
  posteriorFamilyRatioGLBLUB :
    ∀ (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
      (hZ : ∀ M : BernoulliMixture, M ∈ C →
        M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0),
      C.Nonempty →
      ∀ {aTrueLower aTrueUpper aFalseLower aFalseUpper : ℝ},
      (∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
        aTrueLower ≤
          M.countEvidenceMass ((xs.map Prod.fst).sum + 1) (xs.map Prod.snd).sum /
            M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum) →
      (∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
        M.countEvidenceMass ((xs.map Prod.fst).sum + 1) (xs.map Prod.snd).sum /
            M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≤
          aTrueUpper) →
      (∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
        aFalseLower ≤
          M.countEvidenceMass (xs.map Prod.fst).sum ((xs.map Prod.snd).sum + 1) /
            M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum) →
      (∀ M : BernoulliMixture, ∀ _hM : M ∈ C,
        M.countEvidenceMass (xs.map Prod.fst).sum ((xs.map Prod.snd).sum + 1) /
            M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≤
          aFalseUpper) →
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
          aFalseUpper
  posteriorFamilyTypedITVReadout :
    ∀ (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
      (hZ : ∀ M : BernoulliMixture, M ∈ C →
        M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0),
      ∀ (hC : C.Nonempty) (n : ℕ) (X : Gamble (Fin n → Bool))
      (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1),
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
              (xs.map Prod.fst).sum (xs.map Prod.snd).sum hZ n) X
  posteriorFamilyTypedITVOrderInvariant :
    ∀ (C : Set BernoulliMixture) {xs ys : List (ℕ × ℕ)}, xs.Perm ys →
      (hZxs : ∀ M : BernoulliMixture, M ∈ C →
        M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0) →
      (hZys : ∀ M : BernoulliMixture, M ∈ C →
        M.countEvidenceMass (ys.map Prod.fst).sum (ys.map Prod.snd).sum ≠ 0) →
      ∀ (hC : C.Nonempty) (n : ℕ) (X : Gamble (Fin n → Bool))
      (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1),
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
          (xs.map countPairEvidence) =
        Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
          (ys.map countPairEvidence) ∧
        posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
            (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZxs hC X hX =
          posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
            (ys.map Prod.fst).sum (ys.map Prod.snd).sum n hZys hC X hX
  posteriorFamilyRatioITVMembership :
    ∀ (C : Set BernoulliMixture) (xs : List (ℕ × ℕ))
      (hZ : ∀ M : BernoulliMixture, M ∈ C →
        M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0),
      ∀ (hC : C.Nonempty) {M : BernoulliMixture}, M ∈ C →
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
            oneBitFalseGamble oneBitFalseGamble_mem_unit).upper

/-- Permuting finite Revision count packets preserves both the raw PLN
Revision aggregate and the general posterior-family typed ITV.  The theorem is
sum-based: it reuses the existing de-Finetti/Walley posterior family rather
than adding a new order-sensitive revision semantics. -/
theorem revisionMany_countPairEvidence_posteriorFamilyTypedWidthComplementITV_perm
    (C : Set BernoulliMixture) {xs ys : List (ℕ × ℕ)} (h : xs.Perm ys)
    (hZxs : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass (xs.map Prod.fst).sum (xs.map Prod.snd).sum ≠ 0)
    (hZys : ∀ M : BernoulliMixture, M ∈ C →
      M.countEvidenceMass (ys.map Prod.fst).sum (ys.map Prod.snd).sum ≠ 0)
    (hC : C.Nonempty) (n : ℕ) (X : Gamble (Fin n → Bool))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (xs.map countPairEvidence) =
      Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision.revisionMany
        (ys.map countPairEvidence) ∧
    posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
        (xs.map Prod.fst).sum (xs.map Prod.snd).sum n hZxs hC X hX =
      posteriorBernoulliMixtureFamilyPrefixTypedWidthComplementITV C
        (ys.map Prod.fst).sum (ys.map Prod.snd).sum n hZys hC X hX := by
  have hpos : (xs.map Prod.fst).sum = (ys.map Prod.fst).sum :=
    (h.map Prod.fst).sum_eq
  have hneg : (xs.map Prod.snd).sum = (ys.map Prod.snd).sum :=
    (h.map Prod.snd).sum_eq
  constructor
  · exact revisionMany_countPairEvidence_perm h
  · simp [hpos, hneg]

/-- Compact public handle for Revision's family-level Walley envelope. -/
noncomputable def revisionCredalEnvelopeProfile :
    RevisionCredalEnvelopeProfile where
  finiteBayesianGrounding := revisionBayesianGroundingProfile
  posteriorFamilyRatioMembership :=
    revisionMany_countPairEvidence_posteriorFamilyRatio_mem_prefixEnvelopes
  posteriorFamilyRatioGLBLUB :=
    revisionMany_countPairEvidence_posteriorFamilyRatio_envelope_glb_lub
  posteriorFamilyTypedITVReadout :=
    revisionMany_countPairEvidence_posteriorFamilyTypedWidthComplementITV_readout
  posteriorFamilyTypedITVOrderInvariant :=
    revisionMany_countPairEvidence_posteriorFamilyTypedWidthComplementITV_perm
  posteriorFamilyRatioITVMembership :=
    revisionMany_countPairEvidence_posteriorFamilyRatio_mem_widthComplementITVs

end Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionCredalEnvelope
