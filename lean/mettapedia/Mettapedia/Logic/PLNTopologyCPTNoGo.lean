import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mettapedia.Logic.PLNBayesNetWorldModel

/-!
# No-Go: Topology-CPT Gap

This module formalizes the **topology-CPT gap** no-go theorem:

For a Bayesian network with a fixed graph topology (DAG structure), the
**conditioning residual** — the change in a node's probability when we condition
on a parent variable — can vary arbitrarily across different CPT parameterizations
of the same network.

No function of the topology alone can provide a non-trivial (< 1) certified upper
bound on the conditioning residual without additional assumptions on the CPT parameters.

**Design implication**: topology-based proxies for `conditioning_residual_abs`
cannot provide certified bounds. Any claimed topology-only bound is either trivial
(≥ 1, which is always satisfied since residuals lie in [0,1]) or unsound.

## Mathematical content

We work with the simplest possible case: a two-node binary network X → Y.
A CPT is specified by `P(Y=1|X=1)` and `P(Y=1|X=0)`.

The **conditioning residual** is `|P(Y=1|X=1) - P(Y=1|X=0)|` ∈ [0, 1].

Theorem (`topology_bound_not_tight`): for any claimed bound `b < 1`, there exists a
CPT with conditioning residual > b. Hence no topology function with value < 1 can
certifiably bound the residual.

Theorem (`same_topology_different_residual`): `cpt_strong` and `cpt_indep` share
the same graph X → Y but have residuals 0.8 and 0.0 respectively.

This mirrors `PLNJointEvidenceNoGo.lean`:
two models agreeing on topology but disagreeing on the quantity of interest.
-/

namespace Mettapedia.Logic.PLNTopologyCPTNoGo

open Mettapedia.Logic.PLNBayesNetWorldModel

/-! ## Basic CPT structure for a binary two-node network -/

/-- A conditional probability table for a binary node Y with a single binary parent X.
The topology is fixed: a single directed edge X → Y. -/
structure BinaryCPT where
  /-- P(Y=1 | X=1) -/
  pYgivenX1 : ℝ
  /-- P(Y=1 | X=0) -/
  pYgivenX0 : ℝ
  h1lo : 0 ≤ pYgivenX1
  h1hi : pYgivenX1 ≤ 1
  h0lo : 0 ≤ pYgivenX0
  h0hi : pYgivenX0 ≤ 1

/-- The conditioning residual: how much conditioning on X=1 vs X=0 shifts P(Y=1). -/
def condResidual (c : BinaryCPT) : ℝ := |c.pYgivenX1 - c.pYgivenX0|

/-- The conditioning residual lies in [0, 1]. -/
theorem condResidual_mem_Icc (c : BinaryCPT) :
    condResidual c ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact abs_nonneg _
  · apply abs_le.mpr
    constructor <;> linarith [c.h1lo, c.h1hi, c.h0lo, c.h0hi]

/-! ## Two concrete CPTs on the same topology -/

/-- **Strong dependence CPT**: Y is almost perfectly predicted by X.
Conditioning residual = |0.9 - 0.1| = 0.8. -/
def cpt_strong : BinaryCPT where
  pYgivenX1 := 0.9
  pYgivenX0 := 0.1
  h1lo := by norm_num
  h1hi := by norm_num
  h0lo := by norm_num
  h0hi := by norm_num

/-- **Independence CPT**: Y is independent of X.
Conditioning residual = |0.5 - 0.5| = 0. -/
def cpt_indep : BinaryCPT where
  pYgivenX1 := 0.5
  pYgivenX0 := 0.5
  h1lo := by norm_num
  h1hi := by norm_num
  h0lo := by norm_num
  h0hi := by norm_num

/-- **Maximum dependence CPT**: Y is perfectly predicted by X.
Conditioning residual = |1 - 0| = 1. -/
def cpt_max : BinaryCPT where
  pYgivenX1 := 1
  pYgivenX0 := 0
  h1lo := by norm_num
  h1hi := by norm_num
  h0lo := by norm_num
  h0hi := by norm_num

/-! ## Concrete residual computations -/

theorem cpt_strong_residual : condResidual cpt_strong = 4 / 5 := by
  simp only [condResidual, cpt_strong]
  norm_num

theorem cpt_indep_residual : condResidual cpt_indep = 0 := by
  simp only [condResidual, cpt_indep]
  norm_num

theorem cpt_max_residual : condResidual cpt_max = 1 := by
  simp only [condResidual, cpt_max]
  norm_num

/-! ## Main no-go theorem -/

/-- **Same topology, different residuals**: `cpt_strong` and `cpt_indep` share
the same graph topology (X → Y) but have different conditioning residuals.

This is the core witness pair for the no-go theorem:
topology alone cannot determine the residual. -/
theorem same_topology_different_residual :
    condResidual cpt_strong ≠ condResidual cpt_indep := by
  rw [cpt_strong_residual, cpt_indep_residual]
  norm_num

/-- **Topology-CPT gap**: for any claimed upper bound `b < 1` (derived from
topology alone), there exists a CPT whose conditioning residual exceeds `b`.

Since `cpt_max` achieves residual 1, and any topology function with value < 1
is exceeded by `cpt_max`, no sub-1 topology bound is universal. -/
theorem topology_bound_not_tight (b : ℝ) (hb : b < 1) :
    ∃ c : BinaryCPT, b < condResidual c :=
  ⟨cpt_max, cpt_max_residual ▸ hb⟩

/-- **Corollary**: for any topology function `f : Unit → ℝ`, if it is a valid
upper bound on all conditioning residuals (meaning `f() ≥ 1`), then it is trivially
satisfied since all residuals lie in [0,1].  A non-trivial bound (f() < 1) fails
to upper-bound `cpt_max`. -/
theorem topology_function_bound_is_trivial (f : Unit → ℝ)
    (h : ∀ c : BinaryCPT, condResidual c ≤ f ()) :
    1 ≤ f () := by
  have := h cpt_max
  rwa [cpt_max_residual] at this

/-- **The separation gap**: the residual difference between `cpt_strong` and
`cpt_indep` is exactly 4/5. No topology function can distinguish these two
parameterizations on the same graph. -/
theorem residual_separation :
    condResidual cpt_strong - condResidual cpt_indep = 4 / 5 := by
  rw [cpt_strong_residual, cpt_indep_residual]
  norm_num

/-! ## Graph-parametric lifting over actual BN topologies -/

/-- Witness that a Boolean BN topology contains at least one binary parent-child
fragment. For `BoolBayesNet`, every node is Boolean already, so only the edge
witness is needed. -/
structure BoolBNBinaryEdgeWitness {n : ℕ} (bn : BoolBayesNet n) where
  parent : Fin n
  child : Fin n
  hEdge : bn.graph.edges parent child
  hne : parent ≠ child

/-- Any Boolean BN topology with an explicit binary edge witness inherits the
same-topology/different-residual separation exhibited by the local two-node
counterexample. The graph witness certifies that the ambient topology contains a
binary parent-child fragment; the numerical separation still comes entirely from
the CPT choice on that fragment. -/
theorem same_topology_different_residual_of_binary_edge_fragment
    {n : ℕ} {bn : BoolBayesNet n} (_w : BoolBNBinaryEdgeWitness bn) :
    condResidual cpt_strong ≠ condResidual cpt_indep :=
  same_topology_different_residual

/-- In any Boolean BN topology containing a binary parent-child fragment, every
claimed topology-only upper bound `b < 1` is exceeded by some CPT
parameterization on that fragment. -/
theorem topology_bound_not_tight_of_binary_edge_fragment
    {n : ℕ} {bn : BoolBayesNet n} (_w : BoolBNBinaryEdgeWitness bn)
    (b : ℝ) (hb : b < 1) :
    ∃ c : BinaryCPT, b < condResidual c :=
  topology_bound_not_tight b hb

/-- A topology-only function on actual Boolean BN topologies can certify all
conditioning residuals for a witnessed binary edge fragment only if its value
on that topology is at least 1, hence trivial. -/
theorem topology_function_bound_is_trivial_of_binary_edge_fragment
    {n : ℕ} (bn : BoolBayesNet n) (_w : BoolBNBinaryEdgeWitness bn)
    (f : BoolBayesNet n → ℝ)
    (h : ∀ c : BinaryCPT, condResidual c ≤ f bn) :
    1 ≤ f bn := by
  have := h cpt_max
  rwa [cpt_max_residual] at this

/-- A graph-parametric restatement of the fixed 4/5 separation witnessed by the
strong-vs-independence CPT pair. -/
theorem residual_separation_of_binary_edge_fragment
    {n : ℕ} {bn : BoolBayesNet n} (_w : BoolBNBinaryEdgeWitness bn) :
    condResidual cpt_strong - condResidual cpt_indep = 4 / 5 :=
  residual_separation

end Mettapedia.Logic.PLNTopologyCPTNoGo
