import Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel
import Mettapedia.PLN.WorldModel.SufficientStatisticSurface
import Mettapedia.Logic.WMMarkov

/-!
# Finite Hidden Markov Complete-Data Statistics as a WM Bridge

This file packages the honest additive WM seam for finite HMMs.

We stay on the complete-data side:

* additive latent evidence = row-wise latent transition counts;
* additive emission evidence = row-wise observation counts indexed by latent state;
* observed-only hidden-state inference is deliberately not claimed here.

Positive example:
* for a paired latent/observation trajectory, we can extract latent transition
  row evidence and emission row evidence exactly.

Negative example:
* this does not recover hidden-state posteriors from observation sequences
  alone, so it is not a Baum-Welch layer.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.WMFiniteHiddenMarkov

open Mettapedia.Logic
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.ProbabilityTheory.HiddenMarkovModels.FiniteHiddenMarkovModel
open Mettapedia.PLN.WorldModel.PLNWorldModelAdditive
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.SufficientStatisticSurface
open Mettapedia.UniversalAI.UniversalPrediction

open scoped ENNReal

variable {latent obs : ℕ}

/-- One complete-data HMM emission observation: latent state together with the
emitted observation. -/
abbrev EmissionObservation (latent obs : ℕ) := PairState latent obs

/-- Row evidence for emission counts from a fixed latent state. -/
def emissionRowEvidenceOfWord : List (EmissionObservation latent obs) → Fin latent → MultiEvidence obs
  | [], _ => 0
  | z :: zs, q =>
      (if z.1 = q then categoricalObservation (k := obs) z.2 else 0) +
        emissionRowEvidenceOfWord zs q

@[simp] theorem emissionRowEvidenceOfWord_nil (q : Fin latent) :
    emissionRowEvidenceOfWord (latent := latent) (obs := obs) [] q = 0 := rfl

@[simp] theorem emissionRowEvidenceOfWord_cons
    (z : EmissionObservation latent obs) (zs : List (EmissionObservation latent obs)) (q : Fin latent) :
    emissionRowEvidenceOfWord (latent := latent) (obs := obs) (z :: zs) q =
      (if z.1 = q then categoricalObservation (k := obs) z.2 else 0) +
        emissionRowEvidenceOfWord (latent := latent) (obs := obs) zs q := rfl

/-- Atomic emission observation encoder for the additive WM surface. -/
def emissionObservationEvidence
    (z : EmissionObservation latent obs) (q : Fin latent) : MultiEvidence obs :=
  if z.1 = q then categoricalObservation (k := obs) z.2 else 0

@[simp] theorem emissionObservationEvidence_eq_zero_of_ne
    (z : EmissionObservation latent obs) (q : Fin latent) (h : z.1 ≠ q) :
    emissionObservationEvidence (latent := latent) (obs := obs) z q = 0 := by
  simp [emissionObservationEvidence, h]

@[simp] theorem emissionObservationEvidence_eq_categoricalObservation_of_eq
    (z : EmissionObservation latent obs) (q : Fin latent) (h : z.1 = q) :
    emissionObservationEvidence (latent := latent) (obs := obs) z q =
      categoricalObservation (k := obs) z.2 := by
  simp [emissionObservationEvidence, h]

/-- Query-indexed emission row statistic for complete-data HMM observations. -/
def emissionRowStatistic :
    SufficientStatisticSurface (EmissionObservation latent obs) (Fin latent) (MultiEvidence obs) where
  observe z q := emissionObservationEvidence (latent := latent) (obs := obs) z q

/-- The canonical multiset of complete-data emission observations is just the
paired word itself, viewed additively. -/
def emissionMultiset : List (EmissionObservation latent obs) → Multiset (EmissionObservation latent obs)
  | [] => 0
  | z :: zs => ({z} : Multiset (EmissionObservation latent obs)) + emissionMultiset zs

@[simp] theorem emissionMultiset_nil :
    emissionMultiset (latent := latent) (obs := obs) [] = 0 := rfl

@[simp] theorem emissionMultiset_cons
    (z : EmissionObservation latent obs) (zs : List (EmissionObservation latent obs)) :
    emissionMultiset (latent := latent) (obs := obs) (z :: zs) =
      ({z} : Multiset (EmissionObservation latent obs)) +
        emissionMultiset (latent := latent) (obs := obs) zs := rfl

/-- Aggregating the complete-data emission observations recovers exactly the
row-wise emission count evidence. -/
theorem aggregate_emissionMultiset_eq_emissionRowEvidenceOfWord
    (zs : List (EmissionObservation latent obs)) (q : Fin latent) :
    aggregate (emissionRowStatistic (latent := latent) (obs := obs))
      (emissionMultiset (latent := latent) (obs := obs) zs) q =
      emissionRowEvidenceOfWord (latent := latent) (obs := obs) zs q := by
  induction zs with
  | nil =>
      simp [emissionRowStatistic]
  | cons z zs ih =>
      rw [emissionMultiset_cons, aggregate_add, aggregate_singleton]
      simpa [emissionRowStatistic, emissionObservationEvidence,
        emissionRowEvidenceOfWord_cons] using congrArg
        (fun e => emissionObservationEvidence (latent := latent) (obs := obs) z q + e) ih

instance instEvidenceTypeEmissionWMState :
    EvidenceType (Multiset (EmissionObservation latent obs)) :=
  multisetEvidenceType (EmissionObservation latent obs)

noncomputable instance instAdditiveWorldModelEmissionWMState :
    AdditiveWorldModel (Multiset (EmissionObservation latent obs)) (Fin latent) (MultiEvidence obs) :=
  (emissionRowStatistic (latent := latent) (obs := obs)).inducedWorldModel

/-- The induced WM extractor for complete-data HMM emission observations. -/
noncomputable def emissionRowExtract
    (W : Multiset (EmissionObservation latent obs)) (q : Fin latent) : MultiEvidence obs :=
  AdditiveWorldModel.extract W q

@[simp] theorem emissionRowExtract_eq_aggregate
    (W : Multiset (EmissionObservation latent obs)) (q : Fin latent) :
    emissionRowExtract (latent := latent) (obs := obs) W q =
      aggregate (emissionRowStatistic (latent := latent) (obs := obs)) W q := by
  rw [emissionRowExtract, SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate]

/-- The WM emission-row extractor on a paired word is exactly the complete-data
emission count surface. -/
theorem emissionRowExtract_emissionMultiset_eq_emissionRowEvidenceOfWord
    (zs : List (EmissionObservation latent obs)) (q : Fin latent) :
    emissionRowExtract (latent := latent) (obs := obs)
      (emissionMultiset (latent := latent) (obs := obs) zs) q =
      emissionRowEvidenceOfWord (latent := latent) (obs := obs) zs q := by
  rw [emissionRowExtract_eq_aggregate]
  exact aggregate_emissionMultiset_eq_emissionRowEvidenceOfWord
    (latent := latent) (obs := obs) zs q

/-- Project the latent-state word out of a paired latent/observation word. -/
def latentWordOfPairedWord : List (EmissionObservation latent obs) → List (Fin latent)
  | [] => []
  | z :: zs => z.1 :: latentWordOfPairedWord zs

@[simp] theorem latentWordOfPairedWord_nil :
    latentWordOfPairedWord (latent := latent) (obs := obs) [] = [] := rfl

@[simp] theorem latentWordOfPairedWord_cons
    (z : EmissionObservation latent obs) (zs : List (EmissionObservation latent obs)) :
    latentWordOfPairedWord (latent := latent) (obs := obs) (z :: zs) =
      z.1 :: latentWordOfPairedWord (latent := latent) (obs := obs) zs := rfl

/-- Latent transition multiset read directly from a paired word. -/
def latentTransitionMultiset : List (EmissionObservation latent obs) → Multiset (TransitionObservation latent)
  | [] => 0
  | [_] => 0
  | z₀ :: z₁ :: zs =>
      ({(z₀.1, z₁.1)} : Multiset (TransitionObservation latent)) +
        latentTransitionMultiset (z₁ :: zs)

@[simp] theorem latentTransitionMultiset_nil :
    latentTransitionMultiset (latent := latent) (obs := obs) [] = 0 := rfl

@[simp] theorem latentTransitionMultiset_singleton
    (z : EmissionObservation latent obs) :
    latentTransitionMultiset (latent := latent) (obs := obs) [z] = 0 := rfl

@[simp] theorem latentTransitionMultiset_cons_cons
    (z₀ z₁ : EmissionObservation latent obs) (zs : List (EmissionObservation latent obs)) :
    latentTransitionMultiset (latent := latent) (obs := obs) (z₀ :: z₁ :: zs) =
      ({(z₀.1, z₁.1)} : Multiset (TransitionObservation latent)) +
        latentTransitionMultiset (latent := latent) (obs := obs) (z₁ :: zs) := rfl

/-- The direct latent-transition multiset of a paired word agrees with the
first-order Markov transition multiset of its latent projection. -/
theorem latentTransitionMultiset_eq_transitionMultiset_latentWord :
    ∀ zs : List (EmissionObservation latent obs),
      latentTransitionMultiset (latent := latent) (obs := obs) zs =
        transitionMultiset (k := latent)
          (latentWordOfPairedWord (latent := latent) (obs := obs) zs)
  | [] => by simp [latentTransitionMultiset, transitionMultiset, latentWordOfPairedWord]
  | [z] => by simp [latentTransitionMultiset, transitionMultiset, latentWordOfPairedWord]
  | z₀ :: z₁ :: zs => by
      simp [latentTransitionMultiset, latentWordOfPairedWord,
        transitionMultiset, transitionMultisetAux,
        latentTransitionMultiset_eq_transitionMultiset_latentWord (z₁ :: zs)]

/-- The latent transition WM surface of a paired word factors through the
ordinary first-order Markov WM bridge on the latent projection. -/
theorem latentRowEvidence_of_pairedWord_summary
    {zs : List (EmissionObservation latent obs)}
    {c : TransCounts latent} {last : Fin latent}
    (hsum : TransCounts.summary (k := latent)
      (latentWordOfPairedWord (latent := latent) (obs := obs) zs) = some (c, last))
    (q : Fin latent) :
    aggregate (markovRowStatistic (k := latent))
      (latentTransitionMultiset (latent := latent) (obs := obs) zs) q =
      rowEvidence c q := by
  rw [latentTransitionMultiset_eq_transitionMultiset_latentWord]
  exact aggregate_transitionMultiset_eq_rowEvidence_of_summary (k := latent) hsum q

section Examples

open scoped BigOperators

/-- Positive example: two emitted `0`s from latent state `0` accumulate two
units of row evidence in the `0` coordinate. -/
example :
    emissionRowEvidenceOfWord (latent := 2) (obs := 2)
      ([(0, 0), (0, 0)] : List (EmissionObservation 2 2)) 0 =
      (categoricalObservation (k := 2) 0 : MultiEvidence 2) +
        categoricalObservation (k := 2) 0 := by
  simp [emissionRowEvidenceOfWord]

/-- Negative example: the same complete-data emission word contributes zero
evidence to the unused latent row `1`. -/
example :
    emissionRowEvidenceOfWord (latent := 2) (obs := 2)
      ([(0, 0), (0, 0)] : List (EmissionObservation 2 2)) 1 = 0 := by
  simp [emissionRowEvidenceOfWord]

end Examples

end Mettapedia.Logic.WMFiniteHiddenMarkov
