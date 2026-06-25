import Mettapedia.Logic.WMMarkov
import Mettapedia.PLN.WorldModel.WorldModel

/-!
# Canonical Markov WM Endpoints

Small public surface for the Markov row-conditioned sufficient-statistic bridge.

This file intentionally stays narrow:

* observation carrier: adjacent transitions,
* additive evidence: outgoing transition counts for the queried row,
* posterior family: Dirichlet row posteriors,
* key theorem surface: WM extraction and posterior means match the
  Markov-Dirichlet summary semantics.
-/

namespace Mettapedia.Logic.WMMarkovCanonical

open Mettapedia.Logic
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelAdditive
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open scoped BigOperators ENNReal

abbrev MarkovTransitionObservation :=
  Mettapedia.UniversalAI.UniversalPrediction.TransitionObservation

abbrev MarkovTransitionWMState (k : ℕ) :=
  Multiset (MarkovTransitionObservation k)

abbrev MarkovTransitionQuery (k : ℕ) :=
  AtomQuery (Fin k)

abbrev MarkovRowStatistic :=
  @Mettapedia.UniversalAI.UniversalPrediction.markovRowStatistic

abbrev markov_transitionMultiset :=
  @Mettapedia.UniversalAI.UniversalPrediction.transitionMultiset

abbrev markov_rowEvidence :=
  @Mettapedia.UniversalAI.UniversalPrediction.rowEvidence

abbrev markov_rowEvidence_counts :=
  @Mettapedia.UniversalAI.UniversalPrediction.rowEvidence_counts

abbrev markov_transitionObservation :=
  @Mettapedia.UniversalAI.UniversalPrediction.transitionObservation

/-- The source state selected by a Markov transition query.

For the XiPLN transition-facing surface, `.link i j` is the intended query form.
The `.prop` / `.linkCond` cases are totalized by reusing the target atom as the
default row anchor so the adapter remains a genuine `AtomQuery` consumer. -/
def markov_transitionQuerySource {k : ℕ} :
    MarkovTransitionQuery k → Fin k
  | .prop a => a
  | .link a _ => a
  | .linkCond as b => as.headD b

/-- The target state selected by a Markov transition query. -/
def markov_transitionQueryTarget {k : ℕ} :
    MarkovTransitionQuery k → Fin k
  | .prop a => a
  | .link _ b => b
  | .linkCond _ b => b

/-- Binary "target vs all other outcomes" projection of row-conditioned
categorical evidence. Positive evidence counts the queried next state; negative
evidence counts the alternatives in the same row. -/
noncomputable def markov_binaryEvidenceOfRowEvidence {k : ℕ}
    (e : MultiEvidence k) (target : Fin k) : BinaryEvidence :=
  { pos := (e.counts target : ℝ≥0∞)
    neg := ∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else (e.counts a : ℝ≥0∞) }

@[simp] theorem markov_binaryEvidenceOfRowEvidence_pos {k : ℕ}
    (e : MultiEvidence k) (target : Fin k) :
    (markov_binaryEvidenceOfRowEvidence e target).pos = (e.counts target : ℝ≥0∞) :=
  rfl

@[simp] theorem markov_binaryEvidenceOfRowEvidence_neg {k : ℕ}
    (e : MultiEvidence k) (target : Fin k) :
    (markov_binaryEvidenceOfRowEvidence e target).neg =
      ∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else (e.counts a : ℝ≥0∞) :=
  rfl

@[simp] theorem markov_binaryEvidenceOfRowEvidence_zero {k : ℕ}
    (target : Fin k) :
    markov_binaryEvidenceOfRowEvidence (0 : MultiEvidence k) target = 0 := by
  ext
  · change (((0 : MultiEvidence k).counts target : ℕ) : ℝ≥0∞) = 0
    simp
  · change (∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else (((0 : MultiEvidence k).counts a : ℕ) : ℝ≥0∞)) = 0
    simp

theorem markov_binaryEvidenceOfRowEvidence_add {k : ℕ}
    (e₁ e₂ : MultiEvidence k) (target : Fin k) :
    markov_binaryEvidenceOfRowEvidence (e₁ + e₂) target =
      markov_binaryEvidenceOfRowEvidence e₁ target +
        markov_binaryEvidenceOfRowEvidence e₂ target := by
  ext
  · change ((((e₁ + e₂).counts target : ℕ) : ℝ≥0∞) =
      (e₁.counts target : ℝ≥0∞) + (e₂.counts target : ℝ≥0∞))
    rw [show (e₁ + e₂).counts target = e₁.counts target + e₂.counts target by rfl, Nat.cast_add]
  · change
      (∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else ((((e₁ + e₂).counts a : ℕ) : ℝ≥0∞))) =
        (∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else (e₁.counts a : ℝ≥0∞)) +
        (∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else (e₂.counts a : ℝ≥0∞))
    have hsplit :
        ∀ a : Fin k,
          (if a = target then (0 : ℝ≥0∞) else
              ((((e₁ + e₂).counts a : ℕ) : ℝ≥0∞))) =
            (if a = target then (0 : ℝ≥0∞) else (e₁.counts a : ℝ≥0∞)) +
            (if a = target then (0 : ℝ≥0∞) else (e₂.counts a : ℝ≥0∞)) := by
      intro a
      by_cases h : a = target
      · simp [h]
      · rw [if_neg h, if_neg h, if_neg h]
        rw [show (e₁ + e₂).counts a = e₁.counts a + e₂.counts a by rfl, Nat.cast_add]
    calc
      (∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else ((((e₁ + e₂).counts a : ℕ) : ℝ≥0∞))) =
          ∑ a : Fin k,
            ((if a = target then (0 : ℝ≥0∞) else (e₁.counts a : ℝ≥0∞)) +
              (if a = target then (0 : ℝ≥0∞) else (e₂.counts a : ℝ≥0∞))) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact hsplit a
      _ =
          (∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else (e₁.counts a : ℝ≥0∞)) +
          (∑ a : Fin k, if a = target then (0 : ℝ≥0∞) else (e₂.counts a : ℝ≥0∞)) := by
            rw [Finset.sum_add_distrib]

instance instEvidenceTypeMarkovTransitionWMState {k : ℕ} :
    EvidenceType (MarkovTransitionWMState k) :=
  multisetEvidenceType (MarkovTransitionObservation k)

noncomputable instance instAdditiveWorldModelMarkovTransitionWMState {k : ℕ} :
    AdditiveWorldModel (MarkovTransitionWMState k) (Fin k) (MultiEvidence k) :=
  (MarkovRowStatistic (k := k)).inducedWorldModel

/-- Extract the row-conditioned Markov categorical evidence from the multiset
state underlying the additive WM bridge. -/
noncomputable def markov_rowExtract {k : ℕ}
    (W : MarkovTransitionWMState k) (prev : Fin k) : MultiEvidence k :=
  AdditiveWorldModel.extract W prev

@[simp] theorem markov_rowExtract_add {k : ℕ}
    (W₁ W₂ : MarkovTransitionWMState k) (prev : Fin k) :
    markov_rowExtract (W₁ + W₂) prev =
      markov_rowExtract W₁ prev + markov_rowExtract W₂ prev := by
  unfold markov_rowExtract
  exact AdditiveWorldModel.extract_add'
    (State := MarkovTransitionWMState k) (Query := Fin k) (Ev := MultiEvidence k) W₁ W₂ prev

@[simp] theorem markov_rowExtract_zero {k : ℕ}
    (prev : Fin k) :
    markov_rowExtract (0 : MarkovTransitionWMState k) prev = 0 := by
  rw [markov_rowExtract, SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate]
  exact SufficientStatisticSurface.aggregate_zero (S := MarkovRowStatistic (k := k)) prev

/-- Query-indexed binary projection of the Markov row evidence. -/
noncomputable def markov_queryBinaryProjection {k : ℕ}
    (q : MarkovTransitionQuery k) (e : MultiEvidence k) : BinaryEvidence :=
  markov_binaryEvidenceOfRowEvidence e (markov_transitionQueryTarget q)

/-- Binary transition evidence for a Markov transition query, read off from the
row evidence of the query's source state. -/
noncomputable def markov_queryBinaryEvidence {k : ℕ}
    (W : MarkovTransitionWMState k) (q : MarkovTransitionQuery k) : BinaryEvidence :=
  markov_queryBinaryProjection q (markov_rowExtract W (markov_transitionQuerySource q))

/-- The Markov transition-multiset state admits a binary WM view for transition
queries by projecting the row-conditioned categorical evidence to
"target transition vs all other outcomes". -/
noncomputable instance instBinaryWorldModelMarkovTransitionQuery {k : ℕ} :
    BinaryWorldModel (MarkovTransitionWMState k) (MarkovTransitionQuery k) where
  evidence := markov_queryBinaryEvidence
  evidence_add W₁ W₂ q := by
    change markov_binaryEvidenceOfRowEvidence
        (markov_rowExtract (W₁ + W₂) (markov_transitionQuerySource q))
        (markov_transitionQueryTarget q) =
      markov_binaryEvidenceOfRowEvidence
        (markov_rowExtract W₁ (markov_transitionQuerySource q))
        (markov_transitionQueryTarget q) +
      markov_binaryEvidenceOfRowEvidence
        (markov_rowExtract W₂ (markov_transitionQuerySource q))
        (markov_transitionQueryTarget q)
    rw [markov_rowExtract_add]
    exact markov_binaryEvidenceOfRowEvidence_add _ _ _
  evidence_zero q := by
    change markov_binaryEvidenceOfRowEvidence
        (markov_rowExtract (0 : MarkovTransitionWMState k) (markov_transitionQuerySource q))
        (markov_transitionQueryTarget q) = 0
    rw [markov_rowExtract_zero]
    exact markov_binaryEvidenceOfRowEvidence_zero (markov_transitionQueryTarget q)

abbrev markov_transitionMultiset_aggregate_eq_rowEvidence_of_summary :=
  @Mettapedia.UniversalAI.UniversalPrediction.aggregate_transitionMultiset_eq_rowEvidence_of_summary

abbrev markov_inducedWorldModel_extract_transitionMultiset_eq_rowEvidence_of_summary :=
  @Mettapedia.UniversalAI.UniversalPrediction.inducedWorldModel_extract_transitionMultiset_eq_rowEvidence_of_summary

abbrev markov_inducedWorldModel_queryObservationCount_transitionMultiset_eq_rowTotal_of_summary :=
  @Mettapedia.UniversalAI.UniversalPrediction.inducedWorldModel_queryObservationCount_transitionMultiset_eq_rowTotal_of_summary

/-- The multiset of adjacent transitions in a word yields exactly the row
evidence selected by the transition summary. -/
theorem markov_rowExtract_transitionMultiset_eq_rowEvidence_of_summary
    {k : ℕ} {xs : List (Fin k)} {c : Mettapedia.UniversalAI.UniversalPrediction.TransCounts k}
    {last : Fin k}
    (hsum : Mettapedia.UniversalAI.UniversalPrediction.TransCounts.summary (k := k) xs = some (c, last))
    (prev : Fin k) :
    markov_rowExtract (k := k) (markov_transitionMultiset (k := k) xs) prev =
      markov_rowEvidence c prev := by
  simpa [markov_rowExtract] using
    (markov_inducedWorldModel_extract_transitionMultiset_eq_rowEvidence_of_summary
      (k := k) hsum prev)

/-- Binary transition evidence extracted from the Markov multiset WM agrees
with the corresponding row-conditioned categorical evidence from the summary. -/
theorem markov_queryBinaryEvidence_transitionMultiset_eq_of_summary
    {k : ℕ} {xs : List (Fin k)} {c : Mettapedia.UniversalAI.UniversalPrediction.TransCounts k}
    {last : Fin k}
    (hsum : Mettapedia.UniversalAI.UniversalPrediction.TransCounts.summary (k := k) xs = some (c, last))
    (q : MarkovTransitionQuery k) :
    markov_queryBinaryEvidence (k := k) (markov_transitionMultiset (k := k) xs) q =
      markov_queryBinaryProjection q (markov_rowEvidence c (markov_transitionQuerySource q)) := by
  rw [markov_queryBinaryEvidence, markov_rowExtract_transitionMultiset_eq_rowEvidence_of_summary
    (k := k) hsum (markov_transitionQuerySource q)]

/-- Link-query specialization of the summary theorem: `i → j` is read from the
`i`-row evidence and then projected to "j vs not-j". -/
theorem markov_linkEvidence_transitionMultiset_eq_of_summary
    {k : ℕ} {xs : List (Fin k)} {c : Mettapedia.UniversalAI.UniversalPrediction.TransCounts k}
    {last : Fin k}
    (hsum : Mettapedia.UniversalAI.UniversalPrediction.TransCounts.summary (k := k) xs = some (c, last))
    (prev next : Fin k) :
    BinaryWorldModel.evidence
        (State := MarkovTransitionWMState k)
        (Query := MarkovTransitionQuery k)
        (markov_transitionMultiset (k := k) xs)
        (.link prev next) =
      markov_binaryEvidenceOfRowEvidence (markov_rowEvidence c prev) next := by
  change markov_queryBinaryEvidence (k := k) (markov_transitionMultiset (k := k) xs)
      (.link prev next) =
    markov_binaryEvidenceOfRowEvidence (markov_rowEvidence c prev) next
  simpa [markov_queryBinaryEvidence, markov_queryBinaryProjection,
    markov_transitionQuerySource, markov_transitionQueryTarget] using
    markov_queryBinaryEvidence_transitionMultiset_eq_of_summary (k := k) hsum (.link prev next)

noncomputable abbrev MarkovRowConjugatePosteriorSurface :=
  @Mettapedia.UniversalAI.UniversalPrediction.markovRowConjugatePosteriorSurface

abbrev markov_rowConjugatePosteriorSurface_evidence_eq_rowEvidence_of_summary :=
  @Mettapedia.UniversalAI.UniversalPrediction.markovRowConjugatePosteriorSurface_evidence_eq_rowEvidence_of_summary

abbrev markov_rowConjugatePosteriorSurface_posteriorMean_eq_stepProb_of_summary :=
  @Mettapedia.UniversalAI.UniversalPrediction.markovRowConjugatePosteriorSurface_posteriorMean_eq_stepProb_of_summary

end Mettapedia.Logic.WMMarkovCanonical
