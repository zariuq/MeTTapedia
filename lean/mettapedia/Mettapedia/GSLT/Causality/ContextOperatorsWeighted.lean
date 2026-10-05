import Mettapedia.GSLT.Causality.ContextOperators
import Mettapedia.GSLT.Distinction.Probabilistic.FiniteChains

/-!
# Weighted impact: interventions on a finite labelled Markov chain

A finite labelled Markov chain is a probabilistic GSLT over the discrete GSLT
of its states (`Probabilistic.stateGSLT`), and its behavioural metric is the
Kantorovich fixed point `bisimulationMetric`, which is the logical distance of
functional expressions (`Probabilistic.LogicalDistance`).  Interventions on
the chain are contexts of that GSLT: maps of states, presented by any
`ContextualRules` and restricted by any `AdmissibleClass`.

* **The weighted interventional distance** (`weightedInterventionalDistance`)
  is the supremum, over the admissible interventions, of the behavioural
  metric after the intervention: the same construction as the crisp
  interventional distance of the ladder, a supremum of pullbacks
  (`ContextOperators.supPullback`).  It dominates the metric
  (`bisimulationMetric_le_weighted`), is symmetric and satisfies the triangle
  inequality (`weighted_symm`, `weighted_triangle`), grows with the class
  (`weighted_mono`), and every admissible intervention is nonexpansive for it
  (`weighted_plug_le`).
* **Weighted impact** (`weightedImpact`): how far an intervention moves a
  state, read through one further admissible intervention.  It vanishes on
  the identity (`weightedImpact_identity`), grows with the class
  (`weightedImpact_mono`), and is subadditive under composition when the
  outer intervention belongs to the class (`weightedImpact_compose_le`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ContextOperatorsWeighted

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.GSLT.Distinction.Probabilistic (stateGSLT)
open Mettapedia.GSLT.Causality.ContextOperators

universe uA uAtom uS uContext uRule

variable {A : Type uA} {Atom : Type uAtom} {S : Type uS} [Fintype S] [Fintype Atom] [Fintype A]
  (P : LabelledMarkovChain ℝ A Atom S) {rules : ContextualRules.{uContext, uRule} (stateGSLT S)}
  (B : AdmissibleClass rules) (c : ℝ)

/-- **The weighted interventional distance**: the largest behavioural metric
after one admissible intervention. -/
noncomputable def weightedInterventionalDistance (s t : S) : ℝ :=
  supPullback (fun context : {context : rules.Context // B.Admissible context} =>
      rules.plug context.1)
    (bisimulationMetric P P c) s t

/-- **Weighted impact**: how far an intervention moves a state, as seen after
one further admissible intervention. -/
noncomputable def weightedImpact (context : rules.Context) (s : S) : ℝ :=
  weightedInterventionalDistance P B c s (rules.plug context s)

variable {c} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
include c_nonneg c_le

theorem bisimulationMetric_le_bound (s t : S) :
    bisimulationMetric P P c s t ≤ observationBound P P :=
  bisimulationMetric_le (couplingBound_const P P c_le) c_nonneg s t

omit [Fintype S] [Fintype Atom] [Fintype A] c_nonneg c_le in
/-- On the discrete GSLT of states the plug laws are equalities. -/
theorem plug_identity_eq (s : S) : rules.plug rules.identity s = s :=
  rules.plug_identity s

omit [Fintype S] [Fintype Atom] [Fintype A] c_nonneg c_le in
theorem plug_compose_eq (outer inner : rules.Context) (s : S) :
    rules.plug (rules.compose outer inner) s = rules.plug outer (rules.plug inner s) :=
  rules.plug_compose outer inner s

omit [Fintype S] [Fintype Atom] [Fintype A] c_nonneg c_le in
theorem nonempty_admissible : Nonempty {context : rules.Context // B.Admissible context} :=
  ⟨⟨rules.identity, B.identity_mem⟩⟩

/-- **The weighted interventional distance dominates the metric**: the
identity is admissible. -/
theorem bisimulationMetric_le_weighted (s t : S) :
    bisimulationMetric P P c s t ≤ weightedInterventionalDistance P B c s t := by
  have bound := le_supPullback (fun context : {context : rules.Context // B.Admissible context} =>
      rules.plug context.1) (bisimulationMetric P P c)
    (bisimulationMetric_le_bound P c_nonneg c_le) ⟨rules.identity, B.identity_mem⟩ s t
  simp only [plug_identity_eq] at bound
  exact bound

theorem weighted_symm (s t : S) :
    weightedInterventionalDistance P B c s t = weightedInterventionalDistance P B c t s :=
  supPullback_symm _ _ (fun x y => (bisimulationMetric_comm c_nonneg c_le x y).symm) s t

theorem weighted_triangle (s t u : S) :
    weightedInterventionalDistance P B c s u ≤
      weightedInterventionalDistance P B c s t + weightedInterventionalDistance P B c t u := by
  have := nonempty_admissible B
  exact supPullback_triangle _ _ (bisimulationMetric_le_bound P c_nonneg c_le)
    (fun x y z => bisimulationMetric_triangle P c_nonneg c_le x y z) s t u

theorem weighted_nonneg (s t : S) : 0 ≤ weightedInterventionalDistance P B c s t :=
  (bisimulationMetric_nonneg c_nonneg c_le s t).trans
    (bisimulationMetric_le_weighted P B c_nonneg c_le s t)

omit c_nonneg c_le in
theorem admissible_closed (inner outer : {context : rules.Context // B.Admissible context}) :
    ∃ composite : {context : rules.Context // B.Admissible context}, ∀ x y : S,
      bisimulationMetric P P c (rules.plug outer.1 (rules.plug inner.1 x))
          (rules.plug outer.1 (rules.plug inner.1 y)) =
        bisimulationMetric P P c (rules.plug composite.1 x) (rules.plug composite.1 y) :=
  ⟨⟨rules.compose outer.1 inner.1, B.compose_mem outer.2 inner.2⟩, fun x y => by
    simp only [plug_compose_eq]⟩

/-- **Every admissible intervention is nonexpansive.** -/
theorem weighted_plug_le {context : rules.Context} (admissible : B.Admissible context) (s t : S) :
    weightedInterventionalDistance P B c (rules.plug context s) (rules.plug context t) ≤
      weightedInterventionalDistance P B c s t := by
  have := nonempty_admissible B
  exact supPullback_act_le (fun context : {context : rules.Context // B.Admissible context} =>
      rules.plug context.1) _ (bisimulationMetric_le_bound P c_nonneg c_le)
    (admissible_closed P B) ⟨context, admissible⟩ s t

/-- **A larger class separates more.** -/
theorem weighted_mono {B' : AdmissibleClass rules} (le : B ≤ B') (s t : S) :
    weightedInterventionalDistance P B c s t ≤ weightedInterventionalDistance P B' c s t := by
  have := nonempty_admissible B
  exact supPullback_le_of_cover _ _ (bisimulationMetric_le_bound P c_nonneg c_le)
    (fun context => ⟨⟨context.1, le _ context.2⟩, fun _ _ => rfl⟩) s t

theorem weightedImpact_mono {B' : AdmissibleClass rules} (le : B ≤ B') (context : rules.Context)
    (s : S) : weightedImpact P B c context s ≤ weightedImpact P B' c context s :=
  weighted_mono P B c_nonneg c_le le _ _

theorem bisimulationMetric_le_weightedImpact (context : rules.Context) (s : S) :
    bisimulationMetric P P c s (rules.plug context s) ≤ weightedImpact P B c context s :=
  bisimulationMetric_le_weighted P B c_nonneg c_le _ _

/-- **Subadditivity of weighted impact under composition.**  Only the outer
intervention needs to belong to the class: it is the one whose
nonexpansiveness is used. -/
theorem weightedImpact_compose_le {outer : rules.Context} (admissible : B.Admissible outer)
    (inner : rules.Context) (s : S) :
    weightedImpact P B c (rules.compose outer inner) s ≤
      weightedImpact P B c inner s + weightedImpact P B c outer s := by
  unfold weightedImpact
  rw [plug_compose_eq]
  calc weightedInterventionalDistance P B c s (rules.plug outer (rules.plug inner s))
      ≤ weightedInterventionalDistance P B c s (rules.plug outer s) +
          weightedInterventionalDistance P B c (rules.plug outer s)
            (rules.plug outer (rules.plug inner s)) :=
        weighted_triangle P B c_nonneg c_le _ _ _
    _ ≤ weightedInterventionalDistance P B c s (rules.plug outer s) +
          weightedInterventionalDistance P B c s (rules.plug inner s) :=
        add_le_add le_rfl (weighted_plug_le P B c_nonneg c_le admissible _ _)
    _ = _ := add_comm _ _

/-- The identity intervention has no weighted impact. -/
theorem weightedImpact_identity [DecidableEq S] (c_pos : 0 < c) (s : S) :
    weightedImpact P B c rules.identity s = 0 := by
  have := nonempty_admissible B
  unfold weightedImpact weightedInterventionalDistance
  rw [plug_identity_eq]
  refine le_antisymm (supPullback_le _ _ fun _ => (bisimulationMetric_self (P := P) c_pos c_le _).le) ?_
  exact supPullback_nonneg _ _ (fun x y => bisimulationMetric_nonneg c_nonneg c_le x y)
    (bisimulationMetric_le_bound P c_nonneg c_le) s s

end Mettapedia.GSLT.Causality.ContextOperatorsWeighted
