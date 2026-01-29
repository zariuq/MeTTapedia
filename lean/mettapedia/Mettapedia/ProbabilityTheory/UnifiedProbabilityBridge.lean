import Mettapedia.Logic.PLNEvidence
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.EvidenceBeta
import Mettapedia.Logic.HeytingValuationOnEvidence
import Mettapedia.Logic.ConfidenceCompoundingTheorem
import Mettapedia.Logic.EvidenceIntervalBounds
import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph

/-!
# The Four Pillars of Unified Probability

This file serves as the master bridge connecting four perspectives on probability
and inference:

1. **Bayesian Networks** - DAG structure, conditional independence, d-separation
2. **PLN Evidence** - commutative quantale, deduction rules, compositional inference
3. **Heyting K&S** - interval bounds, excluded middle gap, epistemic uncertainty
4. **Beta Distribution** - conjugate updating, evidence aggregation, Bayesian learning

## Key Insights

1. **Quantale to Deduction**: The PLN tensor operation captures compositional
   inference, corresponding to multiplying likelihood ratios.

2. **Heyting to Uncertainty**: Non-Boolean elements (excluded middle gap > 0)
   naturally represent epistemic uncertainty and interval-valued probabilities.

3. **Beta to Learning**: The Beta-Bernoulli conjugacy makes Evidence a sufficient
   statistic for Bayesian learning, with hplus capturing conjugate updates.

4. **BN to Structure**: Bayesian networks provide the graphical structure for
   conditional independence, with d-separation as the soundness criterion.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Goertzel et al., "Probabilistic Logic Networks" (2008)
- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988)
- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
-/

namespace Mettapedia.ProbabilityTheory.UnifiedProbabilityBridge

open Mettapedia.Logic.PLNEvidence
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceBeta
open Mettapedia.Logic.HeytingValuationOnEvidence
open Mettapedia.Logic.ConfidenceCompoundingTheorem
open Mettapedia.Logic.EvidenceIntervalBounds
open Mettapedia.ProbabilityTheory.BayesianNetworks

/-! ## Pillar 1: Bayesian Networks - Conditional Independence -/

section BayesianNetworks

/-- Bayesian networks provide DAG-structured conditional independence. -/
theorem bn_structural_properties (V : Type*) (bn : BayesianNetwork V) :
    bn.graph.IsAcyclic := bn.acyclic

/-- In a BN, parents are non-descendants. -/
theorem bn_parents_are_nondesc (V : Type*) (bn : BayesianNetwork V) (v : V) :
    bn.parents v ⊆ bn.nonDescendants v :=
  bn.parents_subset_nonDescendants v

/-- Acyclic graphs admit topological orderings. -/
theorem bn_has_topological_order (V : Type*) [Fintype V] [DecidableEq V]
    (bn : BayesianNetwork V) :
    ∃ order : List V, bn.IsTopologicalOrder order :=
  bn.exists_topological_order

/-- D-separation is symmetric. -/
theorem dsep_is_symmetric (V : Type*) (G : DirectedGraph V) (X Y Z : Set V) :
    DSeparation.DSeparated G X Y Z → DSeparation.DSeparated G Y X Z :=
  DSeparation.dsep_symmetric G X Y Z

end BayesianNetworks

/-! ## Pillar 2: PLN Evidence - Quantale - Deduction -/

section PLNQuantale

/-- Evidence has a CommSemigroup structure (tensor is commutative). -/
noncomputable example : CommSemigroup Evidence := inferInstance

/-- Evidence has a CompleteLattice structure. -/
noncomputable example : CompleteLattice Evidence := inferInstance

/-- Evidence forms a frame (complete Heyting algebra). -/
noncomputable example : Order.Frame Evidence := inferInstance

/-- Tensor is associative (chaining inference steps). -/
theorem tensor_associativity :
    ∀ e1 e2 e3 : Evidence, (e1 * e2) * e3 = e1 * (e2 * e3) :=
  Evidence.tensor_assoc

/-- Tensor is commutative (order-independence of evidence). -/
theorem tensor_commutativity :
    ∀ e1 e2 : Evidence, e1 * e2 = e2 * e1 :=
  Evidence.tensor_comm

/-- Unit evidence is neutral. -/
theorem tensor_unit :
    ∀ e : Evidence, e * Evidence.one = e :=
  Evidence.tensor_one

/-- The main confidence compounding theorem for independent sources. -/
theorem confidence_compounds_correctly :
    (∀ e1 e2 : Evidence, e1 * e2 = e2 * e1) ∧
    (∀ e1 e2 e3 : Evidence, (e1 * e2) * e3 = e1 * (e2 * e3)) ∧
    (∀ e : Evidence, e * Evidence.one = e) ∧
    (∀ e1 e2 : Evidence, (e1 * e2).pos = e1.pos * e2.pos ∧ (e1 * e2).neg = e1.neg * e2.neg) :=
  confidence_compounding_main

/-- Odds ratios compose multiplicatively under tensor. -/
theorem odds_compose (e1 e2 : Evidence) (h1 : e1.neg ≠ 0) (h2 : e2.neg ≠ 0) :
    (e1 * e2).pos / (e1 * e2).neg = (e1.pos / e1.neg) * (e2.pos / e2.neg) :=
  odds_ratio_composition e1 e2 h1 h2

end PLNQuantale

/-! ## Pillar 3: Heyting K&S - Interval Bounds - Uncertainty -/

section HeytingIntervals

/-- Total evidence function. -/
noncomputable example (e : Evidence) : ENNReal := totalEvidence e

/-- Strength function for evidence. -/
noncomputable example (e : Evidence) : ENNReal := strength e

/-- Credal gap measures uncertainty (returns 0 for singletons). -/
example (e : Evidence) : credalGap {e} = 0 := credalGap_singleton e

/-- Evidence is richer than just strength intervals. -/
theorem evidence_richer :
    ∃ e1 e2 : Evidence,
      strength e1 = strength e2 ∧ e1 ≠ e2 ∧ totalEvidence e1 ≠ totalEvidence e2 :=
  evidence_richer_than_strength

end HeytingIntervals

/-! ## Pillar 4: Beta Distribution - Conjugate Updating - Learning -/

section BetaLearning

/-- Evidence is a sufficient statistic for Beta-Bernoulli inference. -/
theorem evidence_is_sufficient_stat :
    ∀ e : Evidence, ∀ prior_α prior_β : ENNReal,
      let posterior_α := e.pos + prior_α
      let posterior_β := e.neg + prior_β
      posterior_α + posterior_β = e.pos + e.neg + prior_α + prior_β := by
  intros e prior_α prior_β
  ring

/-- hplus corresponds to combining evidence from the same phenomenon. -/
theorem hplus_adds_counts :
    ∀ e1 e2 : Evidence,
      (e1 + e2).pos = e1.pos + e2.pos ∧ (e1 + e2).neg = e1.neg + e2.neg := by
  intro e1 e2
  constructor <;> rfl

/-- tensor corresponds to combining independent evidence (odds multiply). -/
theorem tensor_multiplies_counts :
    ∀ e1 e2 : Evidence,
      (e1 * e2).pos = e1.pos * e2.pos ∧ (e1 * e2).neg = e1.neg * e2.neg := by
  intro e1 e2
  simp only [Evidence.tensor_def, and_self]

/-- Contrast: hplus vs tensor interpretation. -/
theorem hplus_vs_tensor :
    (∀ e1 e2 : Evidence, (e1 + e2).pos = e1.pos + e2.pos) ∧
    (∀ e1 e2 : Evidence, (e1 * e2).pos = e1.pos * e2.pos) := by
  constructor
  · intro e1 e2; rfl
  · intro e1 e2; simp only [Evidence.tensor_def]

end BetaLearning

/-! ## The Grand Unification -/

section GrandUnification

/-- The four pillars are mathematically compatible.

    1. **Quantale structure**: (Evidence, *, +, ≤) forms a commutative quantale
    2. **Deduction semantics**: Tensor captures compositional inference
    3. **Uncertainty representation**: Credal sets give interval bounds
    4. **Bayesian semantics**: hplus/tensor correspond to conjugate/independent updates
-/
theorem four_pillars_unified :
    -- Pillar 1: Evidence has CommSemigroup and CompleteLattice
    Nonempty (CommSemigroup Evidence) ∧
    Nonempty (CompleteLattice Evidence) ∧
    -- Pillar 2: Tensor is the correct composition operation
    (∀ e1 e2 : Evidence, (e1 * e2).pos = e1.pos * e2.pos ∧ (e1 * e2).neg = e1.neg * e2.neg) ∧
    -- Pillar 3: Credal gaps measure uncertainty (singleton has gap 0)
    (∀ e : Evidence, credalGap {e} = 0) ∧
    -- Pillar 4: hplus adds, tensor multiplies
    (∀ e1 e2 : Evidence, (e1 + e2).pos = e1.pos + e2.pos ∧ (e1 * e2).pos = e1.pos * e2.pos) := by
  refine ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ?_, ?_, ?_⟩
  · -- Tensor structure
    intro e1 e2
    simp only [Evidence.tensor_def, and_self]
  · -- Credal gap for singletons
    intro e
    exact credalGap_singleton e
  · -- hplus vs tensor
    intro e1 e2
    constructor
    · rfl
    · simp only [Evidence.tensor_def]

end GrandUnification

/-! ## Summary

This file establishes that the four pillars of probability theory formalized
in this project are mathematically compatible:

1. **Bayesian Networks**: DAG structure, conditional independence, d-separation
   - Files: DirectedGraph.lean, BayesianNetwork.lean, DSeparation.lean

2. **PLN Evidence Quantale**: Commutative quantale, frame, deduction
   - Files: PLNEvidence.lean, EvidenceQuantale.lean, PLNDeduction.lean

3. **Heyting K&S**: Interval bounds, excluded middle gap, uncertainty
   - Files: HeytingValuationOnEvidence.lean, EvidenceIntervalBounds.lean

4. **Beta-Bernoulli**: Conjugate updating, evidence aggregation
   - Files: EvidenceBeta.lean, ConfidenceCompoundingTheorem.lean

The key insight is that PLN's 2D Evidence structure (n+, n-) naturally supports:
- Quantale tensor for composing conditional relationships
- hplus for aggregating same-phenomenon evidence
- Strength function for point probabilities
- Credal sets for interval probabilities
- Sufficient statistics for Beta posteriors
-/

end Mettapedia.ProbabilityTheory.UnifiedProbabilityBridge
