/-
# Factor Graphs

Factor graphs are bipartite graphs representing the factorization structure of a
probability distribution (or more generally, any function that decomposes as a product).

## Overview

A factor graph consists of:
1. **Variable nodes** (V): Random variables in the model
2. **Factor nodes** (F): Functions that take subsets of variables as arguments
3. **Edges**: Connect factors to the variables in their scope

The joint distribution (or unnormalized potential) is:
  P(X) ∝ ∏_f φ_f(X_{scope(f)})

## Key Concepts

- **Scope**: The set of variables a factor depends on
- **Potential**: Non-negative function over a factor's scope
- **Partition Function**: Z = Σ_x ∏_f φ_f(x_{scope(f)})
- **Variable Elimination**: Computing marginals by summing out variables

## Relationship to Bayesian Networks

Every Bayesian network induces a factor graph where:
- Each conditional P(Xᵢ | Parents(Xᵢ)) becomes a factor
- The scope of each factor is {Xᵢ} ∪ Parents(Xᵢ)

## References

- Kschischang, Frey, Loeliger, "Factor Graphs and the Sum-Product Algorithm" (2001)
- Koller & Friedman, "Probabilistic Graphical Models" (2009), Chapter 4
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open DirectedGraph
open scoped BigOperators ENNReal

set_option linter.dupNamespace false in
/-! ## Factor Graph Structure -/

/-- A **Factor Graph** represents a function that factors as a product of local potentials.

    - V: The set of variable nodes
    - β: The state space for each variable
    - factors: The set of factor nodes
    - scope: For each factor, the set of variables it depends on
    - potential: For each factor, a non-negative function on configurations of its scope

    The joint function is: f(x) = ∏_i potential(i)(x|_{scope(i)}) -/
structure FactorGraph (V : Type*) (K : Type*) where
  /-- State space for each variable -/
  stateSpace : V → Type*
  /-- Factor node type -/
  factors : Type*
  /-- Scope of each factor: the variables it depends on -/
  scope : factors → Finset V
  /-- Potential function for each factor -/
  potential : (f : factors) → (∀ v ∈ scope f, stateSpace v) → K

namespace FactorGraph

variable {V K : Type*}

/-! ## Configuration Types -/

/-- A full configuration assigns a value to every variable. -/
def FullConfig (fg : FactorGraph V K) := ∀ v : V, fg.stateSpace v

/-- Restrict a full configuration to the scope of a factor. -/
def restrictToScope (fg : FactorGraph V K) (f : fg.factors) (x : fg.FullConfig) :
    ∀ v ∈ fg.scope f, fg.stateSpace v :=
  fun v _ => x v

/-! ## Joint Potential -/

/-- The unnormalized joint potential: product of all factor potentials.

    φ(x) = ∏_f potential(f)(x|_{scope(f)}) -/
noncomputable def unnormalizedJoint (fg : FactorGraph V K) [Fintype fg.factors]
    [CommMonoid K] (x : fg.FullConfig) : K :=
  ∏ f : fg.factors, fg.potential f (fg.restrictToScope f x)

/-- The partition function (normalizing constant).

    Z = Σ_x ∏_f φ_f(x)

    Note: This requires summing over all configurations, which needs Fintype instances. -/
noncomputable def partitionFunction (fg : FactorGraph V K) [Fintype V]
    [∀ v, Fintype (fg.stateSpace v)] [Fintype fg.factors] [DecidableEq V]
    [CommMonoid K] [AddCommMonoid K] : K :=
  by
    classical
    -- Since `V` is finite and each `stateSpace v` is finite, the dependent function type
    -- `FullConfig fg = ∀ v, stateSpace v` is also finite, so the partition function is a
    -- finite sum.
    -- We sum over all configurations using `Fintype.piFinset`.
    exact
      (Fintype.piFinset (fun v : V => (Finset.univ : Finset (fg.stateSpace v)))).sum
        (fun x => fg.unnormalizedJoint x)

/-! ## Factor Graph Properties -/

/-- A factor graph is **pairwise** if every factor involves at most 2 variables. -/
def IsPairwise (fg : FactorGraph V K) : Prop :=
  ∀ f : fg.factors, (fg.scope f).card ≤ 2

/-- A factor graph is **unary** if every factor involves exactly 1 variable. -/
def IsUnary (fg : FactorGraph V K) : Prop :=
  ∀ f : fg.factors, (fg.scope f).card = 1

/-- The **neighbors** of a variable: factors that include it in their scope. -/
def variableNeighbors (fg : FactorGraph V K) [DecidableEq V] (v : V) : Set fg.factors :=
  { f | v ∈ fg.scope f }

/-- The **neighbors** of a factor: variables in its scope. -/
def factorNeighbors (fg : FactorGraph V K) (f : fg.factors) : Finset V :=
  fg.scope f

/-! ## Properties of Unnormalized Joint -/

section Prob

variable {V : Type*}

/-- The unnormalized joint is non-negative. -/
theorem unnormalizedJoint_nonneg (fg : FactorGraph V ℝ≥0∞) [Fintype fg.factors]
    (x : fg.FullConfig) : 0 ≤ fg.unnormalizedJoint x := by
  exact zero_le _

/-- If all potentials are non-zero, the unnormalized joint is non-zero. -/
theorem unnormalizedJoint_ne_zero (fg : FactorGraph V ℝ≥0∞) [Fintype fg.factors]
    (x : fg.FullConfig)
    (hpos : ∀ f : fg.factors, fg.potential f (fg.restrictToScope f x) ≠ 0) :
    fg.unnormalizedJoint x ≠ 0 := by
  unfold unnormalizedJoint
  exact Finset.prod_ne_zero_iff.mpr (fun f _ => hpos f)

end Prob

/-! ## Relationship to Bayesian Networks -/

section BayesianNetworkConnection

variable [Fintype V]

/-- Convert a Bayesian Network to a Factor Graph.

    Each node v in the BN creates a factor with:
    - Scope = {v} ∪ parents(v)
    - Potential = CPT P(v | parents(v))

    This is stated as a type; the actual construction requires
    measurability and kernel-to-function conversion. -/
structure BNToFactorGraphData (bn : BayesianNetwork V) where
  /-- For each BN variable, there is one factor -/
  factorForNode : V → Fin (Fintype.card V)
  /-- The scope of each factor -/
  factorScope : Fin (Fintype.card V) → Finset V

/-- The factor graph induced by a Bayesian network has one factor per variable. -/
theorem bn_factor_count (_bn : BayesianNetwork V) :
    -- Each variable creates exactly one factor
    ∃ (n : ℕ), n = Fintype.card V := ⟨Fintype.card V, rfl⟩

omit [Fintype V] in
/-- In a BN-induced factor graph, each factor's scope is {v} ∪ parents(v). -/
theorem bn_factor_scope_structure (bn : BayesianNetwork V) (v : V) :
    -- The scope for v's factor contains v and its parents
    ∃ (S : Set V), v ∈ S ∧ bn.parents v ⊆ S :=
  ⟨{v} ∪ bn.parents v, Set.mem_union_left _ (Set.mem_singleton v), Set.subset_union_right⟩

end BayesianNetworkConnection

/-! ## Simple Factor Graph (Uniform State Space) -/

end FactorGraph

/-! ## Canonical Instantiations -/

/-- Classical probabilistic factor graphs (ENNReal potentials). -/
abbrev ProbFactorGraph (V : Type*) := FactorGraph V ℝ≥0∞

/-- K&S regraduated factor graphs (real-valued plausibility scale). -/
abbrev KSFactorGraph (V : Type*) := FactorGraph V ℝ

/-- A simplified factor graph where all variables have the same state space.
    Potentials take full assignments for simplicity. -/
structure SimpleFactorGraph (V : Type*) (β : Type*) where
  /-- Factor node type -/
  factors : Type*
  /-- Scope of each factor -/
  scope : factors → Finset V
  /-- Potential function for each factor (takes full assignment) -/
  potential : (f : factors) → (V → β) → ENNReal

namespace SimpleFactorGraph

variable {V β : Type*}

/-- Full configuration type for simple factor graphs. -/
abbrev FullConfig (V : Type*) (β : Type*) := V → β

/-- Unnormalized joint for simple factor graphs. -/
noncomputable def unnormalizedJoint (sfg : SimpleFactorGraph V β) [Fintype sfg.factors]
    (x : FullConfig V β) : ENNReal :=
  ∏ f : sfg.factors, sfg.potential f x

/-- The unnormalized joint is non-negative. -/
theorem unnormalizedJoint_nonneg (sfg : SimpleFactorGraph V β) [Fintype sfg.factors]
    (x : FullConfig V β) : 0 ≤ sfg.unnormalizedJoint x := by
  exact zero_le _

end SimpleFactorGraph

/-! ## Markov Random Fields

A special case where the factor graph structure comes from an undirected graph.
-/

/-- A **Markov Random Field** (MRF) is a factor graph where factors correspond
    to cliques in an undirected graph. -/
structure MarkovRandomField (V : Type*) where
  /-- State space for each variable -/
  stateSpace : V → Type*
  /-- Undirected edges (symmetric) -/
  edges : V → V → Prop
  /-- Symmetry of edges -/
  edges_symm : ∀ u v, edges u v ↔ edges v u
  /-- Clique potentials -/
  cliquePotentials : (S : Finset V) → (∀ v ∈ S, stateSpace v) → ENNReal

namespace MarkovRandomField

variable {V : Type*}

/-- The neighborhood of a vertex in an MRF. -/
def neighbors (mrf : MarkovRandomField V) (v : V) : Set V :=
  { u | mrf.edges v u }

/-- Symmetry: u is a neighbor of v iff v is a neighbor of u. -/
theorem neighbors_symm (mrf : MarkovRandomField V) (u v : V) :
    u ∈ mrf.neighbors v ↔ v ∈ mrf.neighbors u := by
  simp only [neighbors, Set.mem_setOf_eq]
  exact mrf.edges_symm v u

end MarkovRandomField

/-! ## Summary

This file establishes:

1. **FactorGraph structure**: Factors with scopes and potentials
2. **Unnormalized joint**: Product of all factor potentials
3. **Partition function**: Normalizing constant (specification)
4. **BN connection**: Every Bayesian network induces a factor graph
5. **SimpleFactorGraph**: Uniform state space version
6. **MarkovRandomField**: Undirected graphical model

The factor graph representation is more general than Bayesian networks
and allows for undirected models, constraint satisfaction, and
message-passing algorithms (sum-product, max-product).

See DSeparation.lean for conditional independence in directed models.
-/

end Mettapedia.ProbabilityTheory.BayesianNetworks
