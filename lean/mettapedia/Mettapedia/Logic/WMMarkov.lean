import Mettapedia.Logic.SufficientStatisticSurface
import Mettapedia.Logic.UniversalPrediction.MarkovDirichletPredictor

/-!
# Markov Transition Summaries as WM/PLN Sufficient Statistics

This file connects the Markov transition-summary state used by
`MarkovDirichletPredictor` to the generic additive WM/PLN sufficient-statistic
layer.

The key design choice is to keep the additive carrier honest:

* additive evidence = row-wise transition counts (`MultiEvidence k`);
* non-additive boundary data = the current/last state, passed explicitly as the
  query index.

So the reusable WM object is not the full Markov summary `(counts,last)`, but
the row-conditioned evidence extractor

`(multiset of transitions, current state) ↦ outgoing-count evidence`.

Positive example:
* if the current state is `q`, the extracted evidence counts how many times
  `q → a` occurred for each `a`.

Negative example:
* the last state itself is not encoded in the additive carrier, because that
  boundary datum is not additive under multiset union.
-/

namespace Mettapedia.Logic.UniversalPrediction

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.SufficientStatisticSurface

open scoped ENNReal

variable {k : ℕ}

/-- A single observed Markov transition `prev → next`. -/
abbrev TransitionObservation (k : ℕ) := Fin k × Fin k

/-- Row evidence read off from a transition-count matrix. -/
def rowEvidence (c : TransCounts k) (prev : Fin k) : MultiEvidence k :=
  ⟨fun next => c.counts prev next⟩

@[simp] theorem rowEvidence_counts (c : TransCounts k) (prev next : Fin k) :
    (rowEvidence c prev).counts next = c.counts prev next :=
  rfl

@[simp] theorem rowEvidence_zero (prev : Fin k) :
    rowEvidence (0 : TransCounts k) prev = 0 := by
  ext next
  rfl

@[simp] theorem rowEvidence_total_eq_rowTotal (c : TransCounts k) (prev : Fin k) :
    (rowEvidence c prev).total = c.rowTotal prev := by
  simp [rowEvidence, MultiEvidence.total, TransCounts.rowTotal]

/-- One transition contributes one categorical count to the queried row, and
zero evidence to every other row. -/
def transitionObservation
    (obs : TransitionObservation k) (q : Fin k) : MultiEvidence k :=
  if obs.1 = q then categoricalObservation (k := k) obs.2 else 0

@[simp] theorem transitionObservation_eq_zero_of_ne
    (obs : TransitionObservation k) (q : Fin k) (h : obs.1 ≠ q) :
    transitionObservation obs q = 0 := by
  simp [transitionObservation, h]

@[simp] theorem transitionObservation_eq_categoricalObservation_of_eq
    (obs : TransitionObservation k) (q : Fin k) (h : obs.1 = q) :
    transitionObservation obs q = categoricalObservation (k := k) obs.2 := by
  simp [transitionObservation, h]

@[simp] theorem transitionObservation_counts
    (obs : TransitionObservation k) (q a : Fin k) :
    (transitionObservation obs q).counts a =
      if obs.1 = q ∧ a = obs.2 then 1 else 0 := by
  by_cases hq : obs.1 = q
  · simp [transitionObservation, hq, categoricalObservation]
  · simp [transitionObservation, hq]
    rfl

/-- The query-indexed Markov row statistic: extract outgoing categorical
evidence for the queried current state. -/
def markovRowStatistic :
    SufficientStatisticSurface (TransitionObservation k) (Fin k) (MultiEvidence k) where
  observe obs q := transitionObservation (k := k) obs q

/-- Recursively collect the transitions in a word tail, given the previous
symbol. -/
def transitionMultisetAux (prev : Fin k) : List (Fin k) → Multiset (TransitionObservation k)
  | [] => 0
  | b :: xs => ({(prev, b)} : Multiset (TransitionObservation k)) + transitionMultisetAux b xs

/-- Multiset of adjacent transitions in a finite word. -/
def transitionMultiset : List (Fin k) → Multiset (TransitionObservation k)
  | [] => 0
  | b :: xs => transitionMultisetAux (k := k) b xs

@[simp] theorem transitionMultisetAux_nil (prev : Fin k) :
    transitionMultisetAux (k := k) prev [] = 0 := rfl

@[simp] theorem transitionMultisetAux_cons (prev b : Fin k) (xs : List (Fin k)) :
    transitionMultisetAux (k := k) prev (b :: xs) =
      ({(prev, b)} : Multiset (TransitionObservation k)) + transitionMultisetAux (k := k) b xs := rfl

@[simp] theorem transitionMultiset_nil :
    transitionMultiset (k := k) [] = 0 := rfl

@[simp] theorem transitionMultiset_cons (b : Fin k) (xs : List (Fin k)) :
    transitionMultiset (k := k) (b :: xs) = transitionMultisetAux (k := k) b xs := rfl

/-- Bumping one matrix entry adds exactly one categorical count to the matching
row-evidence view. -/
theorem rowEvidence_bump_eq_add_transitionObservation
    (c : TransCounts k) (prev next q : Fin k) :
    rowEvidence (TransCounts.bump c prev next) q =
      rowEvidence c q + transitionObservation (k := k) (prev, next) q := by
  ext a
  by_cases hq : prev = q
  · subst hq
    change (rowEvidence (TransCounts.bump c prev next) prev).counts a =
      (MultiEvidence.hplus (rowEvidence c prev)
        (transitionObservation (k := k) (prev, next) prev)).counts a
    by_cases ha : a = next
    · subst ha
      simp [rowEvidence, transitionObservation, categoricalObservation, TransCounts.bump,
        MultiEvidence.hplus]
    · simp [rowEvidence, transitionObservation, categoricalObservation, TransCounts.bump,
        MultiEvidence.hplus, ha]
  · have hpair : ¬(prev = q ∧ a = next) := by
      intro h
      exact hq h.1
    change (rowEvidence (TransCounts.bump c prev next) q).counts a =
      (MultiEvidence.hplus (rowEvidence c q)
        (transitionObservation (k := k) (prev, next) q)).counts a
    have hpair' : ¬(q = prev ∧ a = next) := by
      intro h
      exact hq h.1.symm
    simp [rowEvidence, transitionObservation, TransCounts.bump, MultiEvidence.hplus, hq, hpair']
    rfl

/-- Aggregating transition observations recovers exactly the row-evidence view
of the transition counts accumulated by `summaryAux`. -/
theorem aggregate_transitionMultisetAux_eq_rowEvidence_summaryAux
    (prev : Fin k) (c : TransCounts k) (xs : List (Fin k)) (q : Fin k) :
    rowEvidence c q +
        aggregate (markovRowStatistic (k := k)) (transitionMultisetAux (k := k) prev xs) q =
      rowEvidence (TransCounts.summaryAux prev c xs).1 q := by
  induction xs generalizing prev c with
  | nil =>
      simp [transitionMultisetAux, TransCounts.summaryAux]
  | cons b xs ih =>
      calc
        rowEvidence c q +
            aggregate (markovRowStatistic (k := k))
              (transitionMultisetAux (k := k) prev (b :: xs)) q
            =
          rowEvidence c q +
            (aggregate (markovRowStatistic (k := k))
                ({(prev, b)} : Multiset (TransitionObservation k)) q +
              aggregate (markovRowStatistic (k := k))
                (transitionMultisetAux (k := k) b xs) q) := by
              rw [transitionMultisetAux_cons, aggregate_add]
        _ =
          (rowEvidence c q +
              aggregate (markovRowStatistic (k := k))
                ({(prev, b)} : Multiset (TransitionObservation k)) q) +
            aggregate (markovRowStatistic (k := k))
              (transitionMultisetAux (k := k) b xs) q := by
              ac_rfl
        _ =
          rowEvidence (TransCounts.bump c prev b) q +
            aggregate (markovRowStatistic (k := k))
              (transitionMultisetAux (k := k) b xs) q := by
              rw [aggregate_singleton]
              simp [markovRowStatistic, rowEvidence_bump_eq_add_transitionObservation]
        _ = rowEvidence (TransCounts.summaryAux b (TransCounts.bump c prev b) xs).1 q := by
              simpa [add_comm] using ih b (TransCounts.bump c prev b)
        _ = rowEvidence (TransCounts.summaryAux prev c (b :: xs)).1 q := by
              simp [TransCounts.summaryAux]

/-- The induced WM extraction on the multiset of transitions in a word recovers
the corresponding row of the Markov transition-count matrix. -/
theorem aggregate_transitionMultiset_eq_rowEvidence_of_summary
    {xs : List (Fin k)} {c : TransCounts k} {last : Fin k}
    (hsum : TransCounts.summary (k := k) xs = some (c, last))
    (q : Fin k) :
    aggregate (markovRowStatistic (k := k)) (transitionMultiset (k := k) xs) q =
      rowEvidence c q := by
  cases xs with
  | nil =>
      simp [TransCounts.summary] at hsum
  | cons b xs =>
      have haux : TransCounts.summaryAux b TransCounts.zero xs = (c, last) := by
        simpa [TransCounts.summary] using Option.some.inj hsum
      have hagg :=
        aggregate_transitionMultisetAux_eq_rowEvidence_summaryAux
          (k := k) b (TransCounts.zero : TransCounts k) xs q
      have hzero : rowEvidence (TransCounts.zero : TransCounts k) q = 0 := by
        ext a
        rfl
      have hagg' :
          aggregate (markovRowStatistic (k := k)) (transitionMultisetAux (k := k) b xs) q =
            rowEvidence (TransCounts.summaryAux b TransCounts.zero xs).1 q := by
        simpa [hzero] using hagg
      simpa [transitionMultiset, haux] using hagg'

/-- The additive WM extractor for Markov transition observations matches the
transition-count row selected by the query state. -/
theorem inducedWorldModel_extract_transitionMultiset_eq_rowEvidence_of_summary
    {xs : List (Fin k)} {c : TransCounts k} {last : Fin k}
    (hsum : TransCounts.summary (k := k) xs = some (c, last))
    (q : Fin k) :
    letI : EvidenceClass.EvidenceType (Multiset (TransitionObservation k)) :=
      PLNWorldModelAdditive.multisetEvidenceType (TransitionObservation k)
    letI : PLNWorldModelGeneric.AdditiveWorldModel
      (Multiset (TransitionObservation k)) (Fin k) (MultiEvidence k) :=
      (markovRowStatistic (k := k)).inducedWorldModel
    PLNWorldModelGeneric.AdditiveWorldModel.extract
        (State := Multiset (TransitionObservation k))
        (Query := Fin k)
        (Ev := MultiEvidence k)
        (transitionMultiset (k := k) xs) q =
      rowEvidence c q := by
  letI : EvidenceClass.EvidenceType (Multiset (TransitionObservation k)) :=
    PLNWorldModelAdditive.multisetEvidenceType (TransitionObservation k)
  letI : PLNWorldModelGeneric.AdditiveWorldModel
    (Multiset (TransitionObservation k)) (Fin k) (MultiEvidence k) :=
    (markovRowStatistic (k := k)).inducedWorldModel
  simpa [SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate] using
    aggregate_transitionMultiset_eq_rowEvidence_of_summary (k := k) hsum q

/-- The count view of the induced WM extractor is exactly the row total of the
transition-count matrix. -/
theorem inducedWorldModel_queryObservationCount_transitionMultiset_eq_rowTotal_of_summary
    {xs : List (Fin k)} {c : TransCounts k} {last : Fin k}
    (hsum : TransCounts.summary (k := k) xs = some (c, last))
    (q : Fin k) :
    letI : EvidenceClass.EvidenceType (Multiset (TransitionObservation k)) :=
      PLNWorldModelAdditive.multisetEvidenceType (TransitionObservation k)
    letI : PLNWorldModelGeneric.AdditiveWorldModel
      (Multiset (TransitionObservation k)) (Fin k) (MultiEvidence k) :=
      (markovRowStatistic (k := k)).inducedWorldModel
    PLNWorldModelGeneric.AdditiveWorldModel.queryObservationCount
        (State := Multiset (TransitionObservation k))
        (Query := Fin k)
        (Ev := MultiEvidence k)
        (transitionMultiset (k := k) xs) q =
      c.rowTotal q := by
  letI : EvidenceClass.EvidenceType (Multiset (TransitionObservation k)) :=
    PLNWorldModelAdditive.multisetEvidenceType (TransitionObservation k)
  letI : PLNWorldModelGeneric.AdditiveWorldModel
    (Multiset (TransitionObservation k)) (Fin k) (MultiEvidence k) :=
    (markovRowStatistic (k := k)).inducedWorldModel
  rw [SufficientStatisticSurface.queryObservationCount_inducedWorldModel_eq_aggregate_observationCount
    (S := markovRowStatistic (k := k))]
  rw [aggregate_transitionMultiset_eq_rowEvidence_of_summary (k := k) hsum q]
  change ((rowEvidence c q).total : ℝ≥0∞) = c.rowTotal q
  exact_mod_cast rowEvidence_total_eq_rowTotal (k := k) c q

/-- Dirichlet posterior mean computed from a row-evidence view is exactly the
Markov-Dirichlet one-step predictive probability for that row. -/
theorem rowEvidence_posteriorMean_eq_stepProb
    (hk : 0 < k)
    (prior : Fin k → DirichletParams k) (c : TransCounts k)
    (prev next : Fin k) :
    (⟨prior prev, rowEvidence c prev⟩ : EvidenceDirichletParams k).posteriorMean hk next =
      MarkovDirichlet.stepProb prior c prev next := by
  unfold EvidenceDirichletParams.posteriorMean EvidenceDirichletParams.toPosterior
    EvidenceDirichletParams.posteriorParam MarkovDirichlet.stepProb
    MarkovDirichlet.stepDenom DirichletParams.totalConcentration
  rw [Finset.sum_add_distrib]
  simp [rowEvidence, TransCounts.rowTotal, Nat.cast_sum, add_comm]

/-- A Markov row posterior surface: batches of observed transitions update the
Dirichlet evidence of the queried current-state row. -/
noncomputable def markovRowConjugatePosteriorSurface :
    ConjugatePosteriorSurface
      (TransitionObservation k) (Fin k) (MultiEvidence k) (EvidenceDirichletParams k) where
  stat := markovRowStatistic (k := k)
  posterior params σ q :=
    { prior := params.prior
      evidence := params.evidence + aggregate (markovRowStatistic (k := k)) σ q }
  posterior_zero params q := by
    cases params
    simp
  posterior_add params σ₁ σ₂ q := by
    cases params
    rw [aggregate_add]
    simp [add_assoc]

/-- Under the WM-side Markov row posterior surface, observing the transitions
of a word updates the queried row to exactly the Markov summary row. -/
theorem markovRowConjugatePosteriorSurface_evidence_eq_rowEvidence_of_summary
    {xs : List (Fin k)} {c : TransCounts k} {last : Fin k}
    (hsum : TransCounts.summary (k := k) xs = some (c, last))
    (prior : DirichletParams k) (q : Fin k) :
    ((markovRowConjugatePosteriorSurface (k := k)).posterior
      ⟨prior, (0 : MultiEvidence k)⟩
      (transitionMultiset (k := k) xs) q).evidence =
      rowEvidence c q := by
  have hagg :=
    aggregate_transitionMultiset_eq_rowEvidence_of_summary (k := k) hsum q
  change (0 : MultiEvidence k) + aggregate (markovRowStatistic (k := k))
      (transitionMultiset (k := k) xs) q = rowEvidence c q
  rw [zero_add, hagg]

/-- The WM/PLN-side posterior mean for the queried active row matches the
Markov-Dirichlet one-step predictive probability selected by the Markov
summary `(counts,last)`. -/
theorem markovRowConjugatePosteriorSurface_posteriorMean_eq_stepProb_of_summary
    (hk : 0 < k)
    {xs : List (Fin k)} {c : TransCounts k} {last : Fin k}
    (hsum : TransCounts.summary (k := k) xs = some (c, last))
    (prior : Fin k → DirichletParams k) (next : Fin k) :
    let params :=
      (markovRowConjugatePosteriorSurface (k := k)).posterior
        ⟨prior last, (0 : MultiEvidence k)⟩
        (transitionMultiset (k := k) xs) last
    params.posteriorMean hk next = MarkovDirichlet.stepProb prior c last next := by
  dsimp [markovRowConjugatePosteriorSurface]
  change
    (⟨prior last,
        (0 : MultiEvidence k) +
          aggregate (markovRowStatistic (k := k)) (transitionMultiset (k := k) xs) last⟩ :
        EvidenceDirichletParams k).posteriorMean hk next =
      MarkovDirichlet.stepProb prior c last next
  rw [zero_add, aggregate_transitionMultiset_eq_rowEvidence_of_summary (k := k) hsum last]
  exact rowEvidence_posteriorMean_eq_stepProb (k := k) hk prior c last next

end Mettapedia.Logic.UniversalPrediction
