import Mettapedia.Logic.MarkovDeFinettiHigherOrder
import Mettapedia.Logic.WMMarkov

/-!
# Higher-Order Markov Summaries as a WM Sufficient-Statistic Bridge

This file threads the higher-order `(m+1)`-gram summary into the same additive
WM sufficient-statistic layer used for the first-order Markov bridge.

The design stays honest:

* additive evidence = context-conditioned next-symbol counts;
* query index = the exposed context state;
* non-additive boundary data = the final context, still carried separately by
  the summary and not forced into the additive carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.WMHigherOrderMarkov

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceDirichlet
open Mettapedia.Logic.MarkovDeFinettiHigherOrder
open Mettapedia.Logic.PLNWorldModelAdditive
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.SufficientStatisticSurface

open scoped ENNReal

variable {k m : ℕ}

/-- A single higher-order Markov observation: current context together with the
next emitted symbol. -/
abbrev HigherOrderObservation (k m : ℕ) := Context k m × Fin k

/-- Row evidence read off from an `(m+1)`-gram count table. -/
def rowEvidence (c : GramCounts k m) (ctx : Context k m) : MultiEvidence k :=
  ⟨fun a => c.counts ctx a⟩

@[simp] theorem rowEvidence_counts
    (c : GramCounts k m) (ctx : Context k m) (a : Fin k) :
    (rowEvidence (k := k) (m := m) c ctx).counts a = c.counts ctx a :=
  rfl

@[simp] theorem rowEvidence_zero (ctx : Context k m) :
    rowEvidence (k := k) (m := m) (0 : GramCounts k m) ctx = 0 := by
  ext a
  rfl

/-- Total outgoing `(m+1)`-gram count from a fixed context. -/
def rowTotal (c : GramCounts k m) (ctx : Context k m) : ℕ :=
  ∑ a : Fin k, c.counts ctx a

@[simp] theorem rowEvidence_total_eq_rowTotal
    (c : GramCounts k m) (ctx : Context k m) :
    (rowEvidence (k := k) (m := m) c ctx).total = rowTotal (k := k) (m := m) c ctx := by
  simp [rowEvidence, rowTotal, MultiEvidence.total]

/-- One higher-order observation contributes one categorical count to the
queried context row, and zero evidence to all other contexts. -/
def higherOrderObservationEvidence
    (obs : HigherOrderObservation k m) (q : Context k m) : MultiEvidence k :=
  if obs.1 = q then categoricalObservation (k := k) obs.2 else 0

@[simp] theorem higherOrderObservationEvidence_eq_zero_of_ne
    (obs : HigherOrderObservation k m) (q : Context k m) (h : obs.1 ≠ q) :
    higherOrderObservationEvidence (k := k) (m := m) obs q = 0 := by
  simp [higherOrderObservationEvidence, h]

@[simp] theorem higherOrderObservationEvidence_eq_categoricalObservation_of_eq
    (obs : HigherOrderObservation k m) (q : Context k m) (h : obs.1 = q) :
    higherOrderObservationEvidence (k := k) (m := m) obs q =
      categoricalObservation (k := k) obs.2 := by
  simp [higherOrderObservationEvidence, h]

@[simp] theorem higherOrderObservationEvidence_counts
    (obs : HigherOrderObservation k m) (q : Context k m) (a : Fin k) :
    (higherOrderObservationEvidence (k := k) (m := m) obs q).counts a =
      if obs.1 = q ∧ a = obs.2 then 1 else 0 := by
  by_cases hq : obs.1 = q
  · simp [higherOrderObservationEvidence, hq, categoricalObservation]
  · simp [higherOrderObservationEvidence, hq]
    rfl

/-- Query-indexed higher-order row statistic. -/
def higherOrderRowStatistic :
    SufficientStatisticSurface (HigherOrderObservation k m) (Context k m) (MultiEvidence k) where
  observe obs q := higherOrderObservationEvidence (k := k) (m := m) obs q

/-- Recursively collect higher-order observations from the future symbol tail
once the initial context is exposed. -/
def observationMultisetAux (ctx : Context k m) : List (Fin k) → Multiset (HigherOrderObservation k m)
  | [] => 0
  | a :: xs =>
      ({(ctx, a)} : Multiset (HigherOrderObservation k m)) +
        observationMultisetAux (shift (k := k) (m := m) ctx a) xs

/-- Multiset of higher-order observations extracted from a raw word. Short
words expose no complete context, so they contribute no additive evidence. -/
def observationMultiset (xs : List (Fin k)) : Multiset (HigherOrderObservation k m) :=
  if hxs : m ≤ xs.length then
    observationMultisetAux (k := k) (m := m)
      (contextOfList (k := k) (m := m) (xs.take m) (by
        rw [List.length_take]
        omega))
      (xs.drop m)
  else
    0

@[simp] theorem observationMultisetAux_nil (ctx : Context k m) :
    observationMultisetAux (k := k) (m := m) ctx [] = 0 := rfl

@[simp] theorem observationMultisetAux_cons
    (ctx : Context k m) (a : Fin k) (xs : List (Fin k)) :
    observationMultisetAux (k := k) (m := m) ctx (a :: xs) =
      ({(ctx, a)} : Multiset (HigherOrderObservation k m)) +
        observationMultisetAux (k := k) (m := m) (shift (k := k) (m := m) ctx a) xs := rfl

/-- Bumping one `(m+1)`-gram entry adds exactly one categorical count to the
matching context row-evidence view. -/
theorem rowEvidence_bump_eq_add_higherOrderObservation
    (c : GramCounts k m) (ctx : Context k m) (a : Fin k) (q : Context k m) :
    rowEvidence (k := k) (m := m) (GramCounts.bump (k := k) (m := m) c ctx a) q =
      rowEvidence (k := k) (m := m) c q +
        higherOrderObservationEvidence (k := k) (m := m) (ctx, a) q := by
  ext b
  by_cases hq : ctx = q
  · subst hq
    change
      (rowEvidence (k := k) (m := m)
        (GramCounts.bump (k := k) (m := m) c ctx a) ctx).counts b =
      (MultiEvidence.hplus
        (rowEvidence (k := k) (m := m) c ctx)
        (higherOrderObservationEvidence (k := k) (m := m) (ctx, a) ctx)).counts b
    by_cases hb : b = a
    · subst hb
      simp [rowEvidence, higherOrderObservationEvidence, categoricalObservation,
        GramCounts.bump, MultiEvidence.hplus]
    · simp [rowEvidence, higherOrderObservationEvidence, categoricalObservation,
        GramCounts.bump, MultiEvidence.hplus, hb]
  · have hpair : ¬(q = ctx ∧ b = a) := by
      intro h
      exact hq h.1.symm
    change
      (rowEvidence (k := k) (m := m)
        (GramCounts.bump (k := k) (m := m) c ctx a) q).counts b =
      (MultiEvidence.hplus
        (rowEvidence (k := k) (m := m) c q)
        (higherOrderObservationEvidence (k := k) (m := m) (ctx, a) q)).counts b
    simp [rowEvidence, higherOrderObservationEvidence, GramCounts.bump,
      MultiEvidence.hplus, hq, hpair]
    rfl

variable [Fact (0 < m)]

omit [Fact (0 < m)] in
/-- Aggregating the higher-order observation multiset tail updates the queried
row exactly as `summaryAux` does. -/
theorem aggregate_observationMultisetAux_eq_rowEvidence_summaryAux
    (ctx : Context k m) (c : GramCounts k m) (xs : List (Fin k)) (q : Context k m) :
    rowEvidence (k := k) (m := m) c q +
        aggregate (higherOrderRowStatistic (k := k) (m := m))
          (observationMultisetAux (k := k) (m := m) ctx xs) q =
      rowEvidence (k := k) (m := m) (summaryAux (k := k) (m := m) ctx c xs).1 q := by
  induction xs generalizing ctx c with
  | nil =>
      simp [observationMultisetAux, summaryAux]
  | cons a xs ih =>
      calc
        rowEvidence (k := k) (m := m) c q +
            aggregate (higherOrderRowStatistic (k := k) (m := m))
              (observationMultisetAux (k := k) (m := m) ctx (a :: xs)) q
            =
          rowEvidence (k := k) (m := m) c q +
            (aggregate (higherOrderRowStatistic (k := k) (m := m))
                ({(ctx, a)} : Multiset (HigherOrderObservation k m)) q +
              aggregate (higherOrderRowStatistic (k := k) (m := m))
                (observationMultisetAux (k := k) (m := m) (shift (k := k) (m := m) ctx a) xs)
                q) := by
              rw [observationMultisetAux_cons, aggregate_add]
        _ =
          (rowEvidence (k := k) (m := m) c q +
              aggregate (higherOrderRowStatistic (k := k) (m := m))
                ({(ctx, a)} : Multiset (HigherOrderObservation k m)) q) +
            aggregate (higherOrderRowStatistic (k := k) (m := m))
              (observationMultisetAux (k := k) (m := m) (shift (k := k) (m := m) ctx a) xs) q := by
                abel_nf
        _ =
          rowEvidence (k := k) (m := m) (GramCounts.bump (k := k) (m := m) c ctx a) q +
            aggregate (higherOrderRowStatistic (k := k) (m := m))
              (observationMultisetAux (k := k) (m := m) (shift (k := k) (m := m) ctx a) xs) q := by
                simp [higherOrderRowStatistic, rowEvidence_bump_eq_add_higherOrderObservation]
        _ =
          rowEvidence (k := k) (m := m)
            (summaryAux (k := k) (m := m) (shift (k := k) (m := m) ctx a)
              (GramCounts.bump (k := k) (m := m) c ctx a) xs).1 q := by
                simpa using ih (shift (k := k) (m := m) ctx a)
                  (GramCounts.bump (k := k) (m := m) c ctx a)
        _ =
          rowEvidence (k := k) (m := m) (summaryAux (k := k) (m := m) ctx c (a :: xs)).1 q := by
                simp [summaryAux]

omit [Fact (0 < m)] in
/-- Aggregating the higher-order observation multiset of a word recovers the
row evidence of the higher-order summary. -/
theorem aggregate_observationMultiset_eq_rowEvidence_of_summary
    {xs : List (Fin k)} {c : GramCounts k m} {last : Context k m}
    (hsum : summary (k := k) (m := m) xs = some (c, last))
    (q : Context k m) :
    aggregate (higherOrderRowStatistic (k := k) (m := m))
      (observationMultiset (k := k) (m := m) xs) q =
      rowEvidence (k := k) (m := m) c q := by
  have hge : m ≤ xs.length := by
    by_contra hlt
    rw [summary_eq_none_of_lt (k := k) (m := m) (xs := xs) (lt_of_not_ge hlt)] at hsum
    simp at hsum
  rw [observationMultiset, dif_pos hge]
  have haux :
      summaryAux (k := k) (m := m)
        (contextOfList (k := k) (m := m) (xs.take m) (by
          rw [List.length_take]
          omega))
        0
        (xs.drop m) = (c, last) := by
    have hsum' := summary_eq_some_of_ge (k := k) (m := m) (xs := xs) hge
    rw [hsum] at hsum'
    exact Option.some.inj hsum'.symm
  have hagg :=
    aggregate_observationMultisetAux_eq_rowEvidence_summaryAux
      (k := k) (m := m)
      (contextOfList (k := k) (m := m) (xs.take m) (by
        rw [List.length_take]
        omega))
      (0 : GramCounts k m) (xs.drop m) q
  simpa [haux, rowEvidence_zero, add_comm] using hagg

instance instEvidenceTypeHigherOrderWMState :
    EvidenceType (Multiset (HigherOrderObservation k m)) :=
  multisetEvidenceType (HigherOrderObservation k m)

noncomputable instance instAdditiveWorldModelHigherOrderWMState :
    AdditiveWorldModel (Multiset (HigherOrderObservation k m)) (Context k m) (MultiEvidence k) :=
  (higherOrderRowStatistic (k := k) (m := m)).inducedWorldModel

/-- Extract the context-conditioned higher-order categorical evidence from the
multiset state underlying the additive WM bridge. -/
noncomputable def rowExtract
    (W : Multiset (HigherOrderObservation k m)) (ctx : Context k m) : MultiEvidence k :=
  AdditiveWorldModel.extract W ctx

omit [Fact (0 < m)] in
@[simp] theorem rowExtract_zero (ctx : Context k m) :
    rowExtract (k := k) (m := m) (0 : Multiset (HigherOrderObservation k m)) ctx = 0 := by
  rw [rowExtract, SufficientStatisticSurface.inducedWorldModel_evidence_eq_aggregate]
  exact SufficientStatisticSurface.aggregate_zero (S := higherOrderRowStatistic (k := k) (m := m)) ctx

omit [Fact (0 < m)] in
@[simp] theorem rowExtract_add
    (W₁ W₂ : Multiset (HigherOrderObservation k m)) (ctx : Context k m) :
    rowExtract (k := k) (m := m) (W₁ + W₂) ctx =
      rowExtract (k := k) (m := m) W₁ ctx +
        rowExtract (k := k) (m := m) W₂ ctx := by
  change AdditiveWorldModel.extract (W₁ + W₂) ctx =
    AdditiveWorldModel.extract W₁ ctx + AdditiveWorldModel.extract W₂ ctx
  exact AdditiveWorldModel.extract_add'
    (State := Multiset (HigherOrderObservation k m))
    (Query := Context k m) (Ev := MultiEvidence k) W₁ W₂ ctx

omit [Fact (0 < m)] in
/-- The higher-order observation multiset extracted from a word yields exactly
the context-row evidence selected by the higher-order summary. -/
theorem rowExtract_observationMultiset_eq_rowEvidence_of_summary
    {xs : List (Fin k)} {c : GramCounts k m} {last : Context k m}
    (hsum : summary (k := k) (m := m) xs = some (c, last))
    (ctx : Context k m) :
    rowExtract (k := k) (m := m) (observationMultiset (k := k) (m := m) xs) ctx =
      rowEvidence (k := k) (m := m) c ctx := by
  simpa [rowExtract] using
    aggregate_observationMultiset_eq_rowEvidence_of_summary
      (k := k) (m := m) hsum ctx

/-- Higher-order predictive probability at a queried context row, read through
the Dirichlet posterior carried by the WM-side evidence. -/
noncomputable def higherOrderStepProb
    (hk : 0 < k)
    (prior : Context k m → DirichletParams k)
    (c : GramCounts k m) (ctx : Context k m) (a : Fin k) : ℝ :=
  (⟨prior ctx, rowEvidence (k := k) (m := m) c ctx⟩ : EvidenceDirichletParams k).posteriorMean hk a

omit [Fact (0 < m)] in
@[simp] theorem rowEvidence_posteriorMean_eq_higherOrderStepProb
    (hk : 0 < k)
    (prior : Context k m → DirichletParams k)
    (c : GramCounts k m) (ctx : Context k m) (a : Fin k) :
    (⟨prior ctx, rowEvidence (k := k) (m := m) c ctx⟩ : EvidenceDirichletParams k).posteriorMean hk a =
      higherOrderStepProb (k := k) (m := m) hk prior c ctx a := rfl

/-- Higher-order row posterior surface: batches of `(m+1)`-gram observations
update the Dirichlet evidence of the queried context row. -/
noncomputable def higherOrderRowConjugatePosteriorSurface :
    ConjugatePosteriorSurface
      (HigherOrderObservation k m) (Context k m) (MultiEvidence k) (EvidenceDirichletParams k) where
  stat := higherOrderRowStatistic (k := k) (m := m)
  posterior params σ q :=
    { prior := params.prior
      evidence := params.evidence +
        aggregate (higherOrderRowStatistic (k := k) (m := m)) σ q }
  posterior_zero params q := by
    cases params
    simp
  posterior_add params σ₁ σ₂ q := by
    cases params
    rw [aggregate_add]
    simp [add_assoc]

omit [Fact (0 < m)] in
/-- Under the higher-order WM row posterior surface, observing a word updates
the queried context row to exactly the higher-order summary row. -/
theorem higherOrderRowConjugatePosteriorSurface_evidence_eq_rowEvidence_of_summary
    {xs : List (Fin k)} {c : GramCounts k m} {last : Context k m}
    (hsum : summary (k := k) (m := m) xs = some (c, last))
    (prior : DirichletParams k) (ctx : Context k m) :
    ((higherOrderRowConjugatePosteriorSurface (k := k) (m := m)).posterior
      ⟨prior, (0 : MultiEvidence k)⟩
      (observationMultiset (k := k) (m := m) xs) ctx).evidence =
      rowEvidence (k := k) (m := m) c ctx := by
  have hagg :=
    aggregate_observationMultiset_eq_rowEvidence_of_summary
      (k := k) (m := m) hsum ctx
  change (0 : MultiEvidence k) +
      aggregate (higherOrderRowStatistic (k := k) (m := m))
        (observationMultiset (k := k) (m := m) xs) ctx =
      rowEvidence (k := k) (m := m) c ctx
  rw [zero_add, hagg]

omit [Fact (0 < m)] in
/-- The WM/PLN-side posterior mean for a queried context row matches the
Dirichlet posterior predictive probability computed from the higher-order
summary. -/
theorem higherOrderRowConjugatePosteriorSurface_posteriorMean_eq_stepProb_of_summary
    (hk : 0 < k)
    {xs : List (Fin k)} {c : GramCounts k m} {last : Context k m}
    (hsum : summary (k := k) (m := m) xs = some (c, last))
    (prior : Context k m → DirichletParams k) (a : Fin k) :
    let params :=
      (higherOrderRowConjugatePosteriorSurface (k := k) (m := m)).posterior
        ⟨prior last, (0 : MultiEvidence k)⟩
        (observationMultiset (k := k) (m := m) xs) last
    params.posteriorMean hk a =
      higherOrderStepProb (k := k) (m := m) hk prior c last a := by
  dsimp [higherOrderRowConjugatePosteriorSurface]
  change
    (⟨prior last,
        (0 : MultiEvidence k) +
          aggregate (higherOrderRowStatistic (k := k) (m := m))
            (observationMultiset (k := k) (m := m) xs) last⟩ :
        EvidenceDirichletParams k).posteriorMean hk a =
      higherOrderStepProb (k := k) (m := m) hk prior c last a
  rw [zero_add,
    aggregate_observationMultiset_eq_rowEvidence_of_summary (k := k) (m := m) hsum last]
  exact rowEvidence_posteriorMean_eq_higherOrderStepProb
    (k := k) (m := m) hk prior c last a

end Mettapedia.Logic.WMHigherOrderMarkov
