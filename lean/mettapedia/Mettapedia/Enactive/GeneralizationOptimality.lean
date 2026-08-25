import Mettapedia.Enactive.Bennett2023
import Mettapedia.Enactive.Razor
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.DeriveFintype

/-!
# Uniform future tasks and Bennett generalization optimality

Michael Timothy Bennett's 2023 Propositions 1--2 compare hypotheses by the
probability that they generalize from a known child task to an unknown parent.
The probabilistic premise is explicit: future task demands are sampled
uniformly from a finite powerset.

This file separates the combinatorial theorem from the enactive presentation.
For any finite outcome domain, a candidate covers some subset of outcomes.
The probability that a uniformly sampled demand set is contained in that
coverage is

`2 ^ |coverage| / 2 ^ |domain|`.

Consequently coverage cardinality and generalization probability induce
exactly the same preorder.  Bennett's child-task theorem follows after proving
that all models of the child have the same already-visible part of their
extension.

The necessity result is stated at its strongest valid scope: every candidate
selected by an optimal proxy must maximize weakness.  The proxy itself need
not be literally a function of weakness; it may, for example, break a tie
between equally weak maxima.  A finite counterexample records this distinction.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.GeneralizationOptimality

open scoped BigOperators

universe uCandidate uOutcome uWorld

/-! ## The presentation-independent powerset theorem -/

/-- A finite uniform-demand problem.  `coverage candidate` lists every atomic
future outcome handled by the candidate.  A sampled demand is successful when
all of its atoms lie in that coverage. -/
structure UniformSubsetProblem
    (Candidate : Type uCandidate) (Outcome : Type uOutcome)
    [DecidableEq Outcome] where
  domain : Finset Outcome
  coverage : Candidate → Finset Outcome
  coverage_subset : ∀ candidate, coverage candidate ⊆ domain

namespace UniformSubsetProblem

variable {Candidate : Type uCandidate} {Outcome : Type uOutcome}
variable [DecidableEq Outcome]

/-- Every possible future demand under the uniform-powerset premise. -/
def sampleSpace (problem : UniformSubsetProblem Candidate Outcome) :
    Finset (Finset Outcome) :=
  problem.domain.powerset

/-- Demands successfully handled by one candidate. -/
def favorable (problem : UniformSubsetProblem Candidate Outcome)
    (candidate : Candidate) : Finset (Finset Outcome) :=
  (problem.coverage candidate).powerset

/-- Exact rational success probability under the uniform powerset. -/
def probability (problem : UniformSubsetProblem Candidate Outcome)
    (candidate : Candidate) : ℚ :=
  (2 ^ (problem.coverage candidate).card : ℚ) /
    (2 ^ problem.domain.card : ℚ)

theorem card_sampleSpace (problem : UniformSubsetProblem Candidate Outcome) :
    problem.sampleSpace.card = 2 ^ problem.domain.card := by
  simp [sampleSpace]

theorem card_favorable (problem : UniformSubsetProblem Candidate Outcome)
    (candidate : Candidate) :
    (problem.favorable candidate).card =
      2 ^ (problem.coverage candidate).card := by
  simp [favorable]

/-- The displayed ratio really counts favorable demands in the sample space.
The subset premise guarantees that every favorable demand is a sampled one. -/
theorem probability_eq_card_ratio
    (problem : UniformSubsetProblem Candidate Outcome)
    (candidate : Candidate) :
    problem.probability candidate =
      (problem.favorable candidate).card / problem.sampleSpace.card := by
  rw [probability, card_favorable, card_sampleSpace]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem favorable_subset_sampleSpace
    (problem : UniformSubsetProblem Candidate Outcome)
    (candidate : Candidate) :
    problem.favorable candidate ⊆ problem.sampleSpace := by
  exact Finset.powerset_mono.mpr (problem.coverage_subset candidate)

/-- Sufficiency and order-level necessity in one theorem: under the named
uniform sample space, probability comparison is exactly coverage-cardinality
comparison. -/
theorem probability_le_iff_card_coverage_le
    (problem : UniformSubsetProblem Candidate Outcome)
    (left right : Candidate) :
    problem.probability left ≤ problem.probability right ↔
      (problem.coverage left).card ≤ (problem.coverage right).card := by
  unfold probability
  rw [div_le_div_iff_of_pos_right]
  · exact_mod_cast Nat.pow_le_pow_iff_right (by decide : 1 < 2)
  · positivity

/-- The induced probability and weakness criteria agree pointwise without
requiring either quantity to replace the underlying coverage sets. -/
theorem probabilityCriterion_agrees_cardinalityCriterion
    (problem : UniformSubsetProblem Candidate Outcome)
    (admissible : Candidate → Prop) (left right : Candidate) :
    (Razor.Criterion.ofBenefit admissible problem.probability).atLeastAsGood
        left right ↔
      (Razor.Criterion.ofBenefit admissible
        (fun candidate => (problem.coverage candidate).card)).atLeastAsGood
          left right := by
  exact problem.probability_le_iff_card_coverage_le right left

end UniformSubsetProblem

/-! ## Bennett's child-to-parent specialization -/

namespace Bennett2023

variable {World : Type uWorld} [Fintype World] [DecidableEq World]
variable {layer : Mettapedia.Enactive.Bennett2023.Layer World}

/-- Decisions outside the known child task. -/
def unseenDomain (task : Mettapedia.Enactive.Bennett2023.Task layer) :
    Finset layer.Statement :=
  layer.statements.attach \ task.decisions

/-- The unseen part of a hypothesis extension. -/
def unseenCoverage (task : Mettapedia.Enactive.Bennett2023.Task layer)
    (hypothesis : layer.Statement) :
    Finset layer.Statement :=
  layer.extension hypothesis \ task.decisions

theorem unseenCoverage_subset_unseenDomain
    (task : Mettapedia.Enactive.Bennett2023.Task layer)
    (hypothesis : layer.Statement) :
    unseenCoverage task hypothesis ⊆ unseenDomain task := by
  apply Finset.sdiff_subset_sdiff
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.rfl

/-- The uniform family of as-yet-unseen demands used by the 2023 proof. -/
def parentProblem (task : Mettapedia.Enactive.Bennett2023.Task layer) :
    UniformSubsetProblem layer.Statement layer.Statement where
  domain := unseenDomain task
  coverage := unseenCoverage task
  coverage_subset := unseenCoverage_subset_unseenDomain task

/-- For a model of the known child, total Bennett weakness decomposes into a
fixed visible contribution and its still-free unseen coverage. -/
theorem weakness_eq_unseenCoverage_add_known
    (task : Mettapedia.Enactive.Bennett2023.Task layer)
    (hypothesis : layer.Statement)
    (model : task.IsModel hypothesis) :
    layer.weakness hypothesis =
      (unseenCoverage task hypothesis).card + task.correctDecisions.card := by
  calc
    layer.weakness hypothesis = (layer.extension hypothesis).card := rfl
    _ = (layer.extension hypothesis \ task.decisions).card +
          (layer.extension hypothesis ∩ task.decisions).card :=
      (Finset.card_sdiff_add_card_inter
        (layer.extension hypothesis) task.decisions).symm
    _ = (unseenCoverage task hypothesis).card +
          task.correctDecisions.card := by
      rw [Finset.inter_comm, model]
      rfl

/-- Among models of one child task, weakness comparison is exactly comparison
of the future coverage that remains after the child's fixed decisions. -/
theorem weakness_le_iff_unseenCoverage_card_le
    (task : Mettapedia.Enactive.Bennett2023.Task layer)
    {left right : layer.Statement}
    (leftModel : task.IsModel left) (rightModel : task.IsModel right) :
    layer.weakness left ≤ layer.weakness right ↔
      (unseenCoverage task left).card ≤
        (unseenCoverage task right).card := by
  rw [weakness_eq_unseenCoverage_add_known task left leftModel,
    weakness_eq_unseenCoverage_add_known task right rightModel,
    Nat.add_le_add_iff_right]

/-- Source-faithful form of Bennett's Proposition 1: for two models of the
known child task, maximizing weakness is necessary and sufficient for
maximizing success probability over the explicit uniform unseen-demand space. -/
theorem parentProbability_le_iff_weakness_le
    (task : Mettapedia.Enactive.Bennett2023.Task layer)
    {left right : layer.Statement}
    (leftModel : task.IsModel left) (rightModel : task.IsModel right) :
    (parentProblem task).probability left ≤
        (parentProblem task).probability right ↔
      layer.weakness left ≤ layer.weakness right := by
  rw [UniformSubsetProblem.probability_le_iff_card_coverage_le,
    weakness_le_iff_unseenCoverage_card_le task leftModel rightModel]
  rfl

end Bennett2023

/-! ## What proxy necessity does and does not entail -/

namespace Proxy

variable {Candidate : Type uCandidate}

/-- A candidate maximizes a natural-valued score on a named finite fibre. -/
def MaximizesOn (candidates : Finset Candidate) (score : Candidate → ℕ)
    (candidate : Candidate) : Prop :=
  candidate ∈ candidates ∧
    ∀ other ∈ candidates, score other ≤ score candidate

/-- An induction proxy is generalization-optimal exactly when every hypothesis
it may select is a weakness maximizer.  It need not reproduce weakness away
from this maximal fibre. -/
def SelectsOnlyWeaknessMaxima (candidates : Finset Candidate)
    (weakness proxy : Candidate → ℕ) : Prop :=
  ∀ candidate, MaximizesOn candidates proxy candidate →
    MaximizesOn candidates weakness candidate

/-- Literal factorization of a proxy through weakness.  The next canary proves
that this is sufficient structure but not a necessary consequence of optimal
selection. -/
def FactorsThrough (weakness proxy : Candidate → ℕ) : Prop :=
  ∃ transform : ℕ → ℕ, proxy = transform ∘ weakness

end Proxy

namespace NecessityCanary

inductive Candidate where
  | lower
  | maxLeft
  | maxRight
deriving DecidableEq, Fintype

def candidates : Finset Candidate := Finset.univ

def weakness : Candidate → ℕ
  | .lower => 1
  | .maxLeft => 2
  | .maxRight => 2

/-- A proxy that breaks the tie between the two weakness maxima. -/
def tieBreakingProxy : Candidate → ℕ
  | .lower => 0
  | .maxLeft => 1
  | .maxRight => 2

/-- Positive control: the proxy's sole maximizer is still a weakness
maximizer, so its selection is generalization-optimal. -/
theorem tieBreakingProxy_selects_only_weakness_maxima :
    Proxy.SelectsOnlyWeaknessMaxima candidates weakness tieBreakingProxy := by
  intro candidate proxyMaximal
  cases candidate with
  | lower =>
      have impossible := proxyMaximal.2 .maxRight (by simp [candidates])
      simp [tieBreakingProxy] at impossible
  | maxLeft =>
      have impossible := proxyMaximal.2 .maxRight (by simp [candidates])
      simp [tieBreakingProxy] at impossible
  | maxRight =>
      constructor
      · simp [candidates]
      · intro other _
        cases other <;> simp [weakness]

/-- Negative control for the published necessity wording: equal weakness can
receive unequal proxy values, so an optimal selector need not be a function of
weakness. -/
theorem tieBreakingProxy_not_factorsThrough :
    ¬ Proxy.FactorsThrough weakness tieBreakingProxy := by
  rintro ⟨transform, factorization⟩
  have leftValue := congrFun factorization Candidate.maxLeft
  have rightValue := congrFun factorization Candidate.maxRight
  simp [weakness, tieBreakingProxy] at leftValue rightValue
  have impossible : (1 : ℕ) = 2 := leftValue.trans rightValue.symm
  omega

theorem optimal_selection_without_literal_weakness_factorization :
    Proxy.SelectsOnlyWeaknessMaxima candidates weakness tieBreakingProxy ∧
      ¬ Proxy.FactorsThrough weakness tieBreakingProxy :=
  ⟨tieBreakingProxy_selects_only_weakness_maxima,
    tieBreakingProxy_not_factorsThrough⟩

end NecessityCanary

#print axioms UniformSubsetProblem.probability_le_iff_card_coverage_le
#print axioms Bennett2023.parentProbability_le_iff_weakness_le
#print axioms NecessityCanary.tieBreakingProxy_selects_only_weakness_maxima
#print axioms NecessityCanary.tieBreakingProxy_not_factorsThrough

end Mettapedia.Enactive.GeneralizationOptimality
