import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph

/-!
# Discrete Semantics for Bayesian Networks (WIP)

This file starts the "Bayesian networks meet PLN" bridge in the **finite/discrete** setting.

What we provide here (no probabilistic heavy-lifting yet):

* A discrete CPT interface: each node has a `PMF` conditional on its parents.
* The induced factor graph (one factor per node) whose unnormalized joint is the BN product form.

What is intentionally left for later (may require real work / sorries):

* Proving the BN product form is normalized (`partitionFunction = 1`) from acyclicity.
* Proving Markov / d-separation soundness using Mathlib's conditional independence API.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators ENNReal

namespace BayesianNetwork

open DirectedGraph ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (bn : BayesianNetwork V)

/-! ## Discrete CPTs -/

/-- Parent assignments as dependent functions on a *set of parents*. We avoid bundling into
`ParentConfig` to keep typeclass requirements light. -/
def ParentAssignment (v : V) : Type _ :=
  ∀ u : V, u ∈ bn.parents v → bn.stateSpace u

/-- A discrete conditional probability table: for each node `v` and parent assignment, a `PMF`
on `stateSpace v`. -/
structure DiscreteCPT where
  cpt : ∀ v : V, bn.ParentAssignment v → PMF (bn.stateSpace v)

namespace DiscreteCPT

variable {bn}

/-- The parent assignment induced by a full configuration `x`. -/
def parentAssignOfConfig (_cpt : bn.DiscreteCPT) (x : bn.JointSpace) (v : V) :
    bn.ParentAssignment v :=
  fun u _ => x u

/-- The conditional probability of the `v`-coordinate of a full configuration `x`,
given its parents under the CPT. -/
def nodeProb (cpt : bn.DiscreteCPT) (x : bn.JointSpace) (v : V) : ℝ≥0∞ :=
  cpt.cpt v (cpt.parentAssignOfConfig x v) (x v)

/-- The BN product-form weight of a full configuration. -/
noncomputable def jointWeight (cpt : bn.DiscreteCPT) (x : bn.JointSpace) : ℝ≥0∞ :=
  ∏ v : V, cpt.nodeProb x v

/-! ## Induced Factor Graph -/

section FactorGraph

variable [DecidableRel bn.graph.edges]

-- A finset version of the parents set.
private def parentsFinset (v : V) : Finset V :=
  (Finset.univ.filter fun u : V => bn.graph.edges u v)

omit [DecidableEq V] in
private lemma mem_parentsFinset_iff (u v : V) :
    u ∈ parentsFinset (bn := bn) v ↔ bn.graph.edges u v := by
  classical
  simp [parentsFinset]

omit [DecidableEq V] in
private lemma mem_parentsFinset_iff' (u v : V) :
    u ∈ parentsFinset (bn := bn) v ↔ u ∈ bn.parents v := by
  classical
  simpa [BayesianNetwork.parents, DirectedGraph.parents] using (mem_parentsFinset_iff (bn := bn) u v)

/-- The discrete factor graph induced by a BN + CPT:
one factor per node with scope `{v} ∪ parents(v)` and potential equal to the CPT probability. -/
noncomputable def toFactorGraph (cpt : bn.DiscreteCPT) : FactorGraph V where
  stateSpace := bn.stateSpace
  factors := V
  scope := fun v => insert v (parentsFinset (bn := bn) v)
  potential := fun v x =>
    -- Build the parent assignment from the factor-scope configuration.
    let pa : bn.ParentAssignment v := fun u hu =>
      x u (by
        -- `u ∈ parents(v)` implies `u ∈ scope(v)`.
        have : u ∈ parentsFinset (bn := bn) v := (mem_parentsFinset_iff' (bn := bn) u v).2 hu
        exact Finset.mem_insert_of_mem this)
    -- The value at the node itself is in the inserted scope.
    cpt.cpt v pa (x v (by simp))

-- Help typeclass inference: the factor type of `toFactorGraph` is definitionally `V`.
private instance (cpt : bn.DiscreteCPT) : Fintype (toFactorGraph (bn := bn) cpt).factors := by
  dsimp [toFactorGraph]
  infer_instance

theorem toFactorGraph_unnormalizedJoint_eq (cpt : bn.DiscreteCPT)
    (x : (toFactorGraph (bn := bn) cpt).FullConfig) :
    (toFactorGraph (bn := bn) cpt).unnormalizedJoint x = cpt.jointWeight x := by
  classical
  -- Both sides are products over nodes/factors; unfold and simplify the scope restriction.
  unfold FactorGraph.unnormalizedJoint DiscreteCPT.jointWeight DiscreteCPT.nodeProb
  simp [FactorGraph.restrictToScope, toFactorGraph, parentsFinset]
  -- The remaining mismatch is just the (definitionally equal) parent-assignment function.
  refine Fintype.prod_congr _ _ (fun v => ?_)
  rfl

end FactorGraph

/-! ## Normalization: BN Product Form Sums to 1

The key theorem: the BN product-form weight defines a proper probability distribution.
We prove this by showing `∑ x, jointWeight cpt x = 1`.

**Proof strategy**: Induction on `|V|`. For the inductive step, pick a sink vertex `s`
(exists by DAG property). Since `s` has no children, the CPT factors for vertices `v ≠ s`
don't depend on `x_s`. We can factor out the sum over `x_s`, which equals 1 by PMF
normalization, leaving a sum over configurations on `V \ {s}`.
-/

section Normalization

variable [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]

/-- Helper: summing a PMF over all values gives 1 (finite version). -/
lemma pmf_sum_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a : ℝ≥0∞) = 1 := by
  have h := p.tsum_coe
  rw [tsum_eq_sum (s := Finset.univ) (fun x hx => (hx (Finset.mem_univ x)).elim)] at h
  exact h

/-- A PMF on a finite type implies the type is nonempty.
    (If α is empty, ∑ a, p a = 0 ≠ 1, contradicting PMF normalization.) -/
lemma pmf_nonempty {α : Type*} [Fintype α] (p : PMF α) : Nonempty α := by
  by_contra h
  simp only [not_nonempty_iff] at h
  have h_sum : ∑ a : α, (p a : ℝ≥0∞) = 0 := by
    haveI : IsEmpty α := h
    exact Finset.sum_eq_zero (fun a _ => (h.false a).elim)
  have h_one := pmf_sum_eq_one p
  rw [h_sum] at h_one
  exact zero_ne_one h_one

omit [Fintype V] [DecidableEq V] [(v : V) → Fintype (bn.stateSpace v)]
  [∀ (v : V), Nonempty (bn.stateSpace v)] in
/-- A sink vertex is not a parent of any vertex. -/
lemma sink_not_parent' (s : V) (hs : bn.graph.IsSink s) (v : V) : s ∉ bn.parents v := by
  simp only [BayesianNetwork.parents, DirectedGraph.parents, Set.mem_setOf_eq]
  rw [DirectedGraph.isSink_iff] at hs
  exact hs v

omit [Fintype V] [(v : V) → Fintype (bn.stateSpace v)] [∀ (v : V), Nonempty (bn.stateSpace v)] in
/-- For a sink s, the parent assignment for any vertex v is independent of x_s.
    That is, changing x_s doesn't change the parent assignment for v. -/
lemma parentAssignOfConfig_update_sink (cpt : bn.DiscreteCPT) (s : V) (hs : bn.graph.IsSink s) (v : V)
    (x : bn.JointSpace) (xs' : bn.stateSpace s) :
    parentAssignOfConfig cpt (Function.update x s xs') v = parentAssignOfConfig cpt x v := by
  funext u hu
  simp only [parentAssignOfConfig]
  have hus : u ≠ s := by
    intro heq
    rw [heq] at hu
    exact sink_not_parent' s hs v hu
  exact Function.update_of_ne hus xs' x

omit [Fintype V] [(v : V) → Fintype (bn.stateSpace v)] [∀ (v : V), Nonempty (bn.stateSpace v)] in
/-- For a sink s and v ≠ s, nodeProb is independent of x_s. -/
lemma nodeProb_update_sink (cpt : bn.DiscreteCPT) (s : V) (hs : bn.graph.IsSink s) (v : V) (hv : v ≠ s)
    (x : bn.JointSpace) (xs' : bn.stateSpace s) :
    nodeProb cpt (Function.update x s xs') v = nodeProb cpt x v := by
  simp only [nodeProb]
  rw [parentAssignOfConfig_update_sink cpt s hs v x xs']
  rw [Function.update_of_ne hv]

omit [Fintype V] [(v : V) → Fintype (bn.stateSpace v)]
  [∀ (v : V), Nonempty (bn.stateSpace v)] in
/-- Split configuration sum via Equiv.piSplitAt. -/
private lemma piSplitAt_symm_apply (s : V) (x : bn.JointSpace) :
    (Equiv.piSplitAt s bn.stateSpace).symm ((Equiv.piSplitAt s bn.stateSpace) x) = x :=
  Equiv.symm_apply_apply _ _

omit [∀ (v : V), Nonempty (bn.stateSpace v)] in
private lemma sum_piSplitAt (s : V) (f : bn.JointSpace → ℝ≥0∞) :
    ∑ x : bn.JointSpace, f x =
    ∑ p : bn.stateSpace s × ((v : { v : V // v ≠ s }) → bn.stateSpace v.val),
      f ((Equiv.piSplitAt s bn.stateSpace).symm p) := by
  apply Fintype.sum_equiv (Equiv.piSplitAt s bn.stateSpace)
  intro x
  rw [piSplitAt_symm_apply]

omit [∀ (v : V), Nonempty (bn.stateSpace v)] in
private lemma sum_piSplitAt' (s : V) (f : bn.JointSpace → ℝ≥0∞) :
    ∑ x : bn.JointSpace, f x =
    ∑ xs : bn.stateSpace s,
    ∑ xrest : (v : { v : V // v ≠ s }) → bn.stateSpace v.val,
      f ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) := by
  rw [sum_piSplitAt (bn := bn) s f, ← Fintype.sum_prod_type']

omit [(v : V) → Fintype (bn.stateSpace v)] [∀ (v : V), Nonempty (bn.stateSpace v)] in
/-- Key helper: split product at sink, showing the sink factor is the only one depending on xs. -/
private lemma jointWeight_split_sink (cpt : bn.DiscreteCPT) (s : V) (_hs : bn.graph.IsSink s)
    (xs : bn.stateSpace s)
    (xrest : (v : { v : V // v ≠ s }) → bn.stateSpace v.val) :
    jointWeight cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) =
    nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) s *
    ∏ v : { v : V // v ≠ s }, nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) v.val := by
  simp only [jointWeight]
  -- Split the product: ∏_v f(v) = ∏_{v≠s} f(v) * ∏_{v=s} f(v)
  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun v => v ≠ s)]
  -- Now we have: ∏_{v≠s} nodeProb v * ∏_{¬(v≠s)} nodeProb v
  -- The second factor is over {v | v = s}, a singleton, which equals nodeProb s
  -- Just need to show these are equal (with a commutation)
  rw [mul_comm]
  congr 1
  -- Show ∏_{v : {v | ¬(v ≠ s)}} nodeProb v = nodeProb s
  -- Since {v | ¬(v ≠ s)} = {s}, this is a product over a singleton
  have h_singleton : ∀ (v : { v : V // ¬(v ≠ s) }), v.val = s := by
    intro ⟨v, hv⟩
    push_neg at hv
    exact hv
  -- The product over a singleton type equals the single value
  have h_unique : Unique { v : V // ¬(v ≠ s) } := by
    refine ⟨⟨s, not_not.mpr rfl⟩, ?_⟩
    intro ⟨v, hv⟩
    ext
    exact h_singleton ⟨v, hv⟩
  conv_lhs =>
    arg 2; ext v
    rw [h_singleton v]
  haveI : Unique { v : V // ¬(v ≠ s) } := h_unique
  rw [Fintype.prod_unique]

omit [(v : V) → Fintype (bn.stateSpace v)] [∀ (v : V), Nonempty (bn.stateSpace v)] in
/-- The product over non-sink vertices doesn't depend on the sink value. -/
private lemma prod_nonSink_indep (cpt : bn.DiscreteCPT) (s : V) (hs : bn.graph.IsSink s)
    (xs xs' : bn.stateSpace s)
    (xrest : (v : { v : V // v ≠ s }) → bn.stateSpace v.val) :
    ∏ v : { v : V // v ≠ s },
      nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) v.val =
    ∏ v : { v : V // v ≠ s },
      nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs', xrest)) v.val := by
  apply Fintype.prod_congr
  intro ⟨v, hv⟩
  -- Show that changing xs to xs' doesn't change nodeProb at v ≠ s
  -- because the configs only differ at s, and s is a sink
  symm
  have heq : (Equiv.piSplitAt s bn.stateSpace).symm (xs', xrest) =
             Function.update ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) s xs' := by
    ext u
    simp only [Equiv.piSplitAt_symm_apply, Function.update]
    split_ifs with hu
    · rfl
    · rfl
  rw [heq]
  exact nodeProb_update_sink cpt s hs v hv _ xs'

omit [Fintype V] in
/-- Summing nodeProb at sink over all sink values gives 1. -/
private lemma sum_nodeProb_sink_eq_one (cpt : bn.DiscreteCPT) (s : V) (hs : bn.graph.IsSink s)
    (xrest : (v : { v : V // v ≠ s }) → bn.stateSpace v.val) :
    ∑ xs : bn.stateSpace s,
      nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) s = 1 := by
  -- nodeProb at s is the CPT probability for s given its parents
  -- Summing over all values of s (with fixed parent values) gives 1 by PMF normalization
  have h : ∀ xs, nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) s =
           (cpt.cpt s (parentAssignOfConfig cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) s)) xs := by
    intro xs
    unfold nodeProb
    simp only [Equiv.piSplitAt_symm_apply, dif_pos]
  simp_rw [h]
  -- The parent assignment doesn't depend on xs (we can pick any reference value)
  -- Pick a reference xs₀ and show all parent assignments are equal
  obtain ⟨xs₀⟩ : Nonempty (bn.stateSpace s) := inferInstance
  have hall : ∀ xs, parentAssignOfConfig cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) s =
                    parentAssignOfConfig cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs₀, xrest)) s := by
    intro xs
    funext u hu
    simp only [parentAssignOfConfig, Equiv.piSplitAt_symm_apply]
    have hus : u ≠ s := by
      intro heq; rw [heq] at hu
      exact sink_not_parent' s hs s hu
    simp [hus]
  simp_rw [hall]
  exact pmf_sum_eq_one (cpt.cpt s _)

/-- Cardinality of subtype decreases when removing one element. -/
private lemma card_subtype_ne (s : V) :
    Fintype.card { v : V // v ≠ s } = Fintype.card V - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- The BN joint weight sums to 1, making it a valid probability distribution.

This is the fundamental normalization theorem for Bayesian networks:
  ∑_x ∏_v P(x_v | Parents(v)) = 1

The proof uses induction on |V|. At each step, we identify a sink vertex s,
factor out the sum over x_s (which gives 1 by PMF normalization), and apply
the induction hypothesis to the remaining vertices.
-/
theorem jointWeight_sum_eq_one (cpt : bn.DiscreteCPT) :
    ∑ x : bn.JointSpace, cpt.jointWeight x = 1 := by
  classical
  -- Induction on the number of vertices
  induction hcard : Fintype.card V generalizing V bn cpt with
  | zero =>
    -- V is empty: one configuration (empty function), empty product = 1
    have hempty : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard
    simp only [jointWeight, Fintype.prod_empty]
    -- Sum over empty function type has one element
    have : Unique bn.JointSpace := Pi.uniqueOfIsEmpty bn.stateSpace
    simp
  | succ n ih =>
    -- |V| = n + 1 ≥ 1, so V is nonempty
    have hne : Nonempty V := Fintype.card_pos_iff.mp (hcard ▸ Nat.succ_pos n)
    -- Find a sink (exists by acyclicity)
    obtain ⟨s, hs⟩ := DirectedGraph.exists_sink_of_acyclic_nonempty bn.graph bn.acyclic
    -- Split the sum: ∑_x = ∑_{xs} ∑_{xrest}
    rw [sum_piSplitAt' (bn := bn) s]
    -- Split the product at the sink
    simp_rw [jointWeight_split_sink cpt s hs]
    -- Exchange order of sum and product for the non-sink part
    -- ∑_{xs} ∑_{xrest} [nodeProb_s * prod_{v≠s} nodeProb_v]
    -- = ∑_{xrest} ∑_{xs} [nodeProb_s * prod_{v≠s} nodeProb_v]
    rw [Finset.sum_comm]
    -- The prod_{v≠s} doesn't depend on xs, so we can factor it out
    -- ∑_{xrest} [prod_{v≠s} nodeProb_v] * [∑_{xs} nodeProb_s]
    -- = ∑_{xrest} [prod_{v≠s} nodeProb_v] * 1
    -- = ∑_{xrest} [prod_{v≠s} nodeProb_v]
    obtain ⟨xs₀⟩ : Nonempty (bn.stateSpace s) := inferInstance
    -- For each xrest, factor out the product (which is constant in xs)
    have h_factor : ∀ (xrest : (v : { v : V // v ≠ s }) → bn.stateSpace v.val),
        ∑ xs : bn.stateSpace s, nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) s *
          ∏ v : { v : V // v ≠ s }, nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) v.val =
        (∑ xs : bn.stateSpace s, nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) s) *
          ∏ v : { v : V // v ≠ s }, nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs₀, xrest)) v.val := by
      intro xrest
      -- First, show all products are equal (by prod_nonSink_indep)
      have h_prod_eq : ∀ xs, ∏ v : { v : V // v ≠ s }, nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs, xrest)) v.val =
                             ∏ v : { v : V // v ≠ s }, nodeProb cpt ((Equiv.piSplitAt s bn.stateSpace).symm (xs₀, xrest)) v.val :=
        fun xs => prod_nonSink_indep cpt s hs xs xs₀ xrest
      -- Rewrite all products to use xs₀
      conv_lhs => arg 2; ext xs; rw [h_prod_eq xs]
      -- Now factor out the constant product
      rw [← Finset.sum_mul]
    simp_rw [h_factor, sum_nodeProb_sink_eq_one cpt s hs, one_mul]
    -- Now we have ∑_{xrest} ∏_{v≠s} nodeProb_v
    -- This is the same as jointWeight for a BN on V \ {s}
    -- We need to apply the induction hypothesis
    -- The cardinality is n by card_subtype_ne
    have hcard' : Fintype.card { v : V // v ≠ s } = n := by
      rw [card_subtype_ne]; omega
    -- Construct the restricted BN on V \ {s}
    let V' := { v : V // v ≠ s }
    -- The restricted graph
    let G' : DirectedGraph V' := {
      edges := fun u v => bn.graph.edges u.val v.val
    }
    -- Verify G' is acyclic (acyclicity transfers from bn.graph)
    -- First, a helper to convert paths from G' to bn.graph
    have lift_path : ∀ (a b : V'), G'.Reachable a b → bn.graph.Reachable a.val b.val := by
      intro a b p
      induction p with
      | refl => exact DirectedGraph.Path.refl _
      | step hedge' _ ih => exact DirectedGraph.Path.step hedge' ih
    have hG'_acyclic : G'.IsAcyclic := by
      intro ⟨v, hv⟩ ⟨⟨u, hu⟩, hedge, hpath⟩
      exact bn.acyclic v ⟨u, hedge, lift_path _ _ hpath⟩
    -- The restricted BN
    let bn' : BayesianNetwork V' := {
      graph := G'
      stateSpace := fun v => bn.stateSpace v.val
      acyclic := hG'_acyclic
      measurableSpace := fun v => bn.measurableSpace v.val
    }
    -- The restricted CPT
    let cpt' : bn'.DiscreteCPT := {
      cpt := fun ⟨v, hv⟩ pa' =>
        -- Need to construct a ParentAssignment for bn from pa' for bn'
        let pa : bn.ParentAssignment v := fun u hu =>
          -- u is a parent of v in bn.graph
          -- Since s is a sink, s is not a parent of any vertex, so u ≠ s
          have hus : u ≠ s := fun heq => by
            rw [heq] at hu
            exact sink_not_parent' s hs v hu
          pa' ⟨u, hus⟩ (by
            simp only [bn', G', BayesianNetwork.parents, DirectedGraph.parents,
                Set.mem_setOf_eq] at hu ⊢
            exact hu)
        cpt.cpt v pa
    }
    -- Apply IH to bn'
    have hih := ih (bn := bn') (cpt := cpt') hcard'
    -- Now we need to show the sum over xrest equals jointWeight for bn'
    convert hih using 1
    -- Show the sums are equal by bijection
    apply Finset.sum_congr rfl
    intro xrest _
    simp only [jointWeight]
    -- Show the products are equal
    apply Fintype.prod_congr
    intro ⟨v, hv⟩
    -- Both sides unfold to cpt.cpt v (pa) (value)
    -- where pa and value differ only in how they extract from xrest vs piSplitAt.symm
    -- Since v ≠ s, piSplitAt.symm (xs₀, xrest) v = xrest ⟨v, hv⟩
    -- Since parents u ≠ s, piSplitAt.symm (xs₀, xrest) u = xrest ⟨u, _⟩
    simp only [nodeProb]
    -- Show values at v are equal
    have hval : ((Equiv.piSplitAt s bn.stateSpace).symm (xs₀, xrest)) v = xrest ⟨v, hv⟩ := by
      simp only [Equiv.piSplitAt_symm_apply, hv, dite_false]
    rw [hval]
    -- Show parent assignments produce the same PMF value
    -- Both sides apply cpt.cpt v to a parent assignment, then evaluate at xrest ⟨v, hv⟩
    -- Now we need: parentAssignOfConfig cpt (...) v = cpt' parent assignment for ⟨v, hv⟩
    -- Both extract from xrest for each parent u of v (since u ≠ s)
    -- Use congr_arg to reduce to parent assignment equality
    apply congr_arg (fun pa => (cpt.cpt v pa) (xrest ⟨v, hv⟩))
    funext u hu
    simp only [parentAssignOfConfig]
    have hus : u ≠ s := fun heq => sink_not_parent' s hs v (heq ▸ hu)
    simp [hus]

end Normalization

/-! ## Joint PMF and Measure (requires normalization) -/

section JointDistribution

variable [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]

/-- The BN joint weight has sum 1 (HasSum version for PMF construction). -/
lemma jointWeight_hasSum_one (cpt : bn.DiscreteCPT) : HasSum cpt.jointWeight 1 := by
  -- For finite types, HasSum f a ↔ ∑ b, f b = a
  -- We have hasSum_fintype which gives HasSum f (∑ b, f b)
  have h := hasSum_fintype cpt.jointWeight
  -- And we know ∑ b, jointWeight cpt b = 1
  rw [jointWeight_sum_eq_one (bn := bn) cpt] at h
  exact h

/-- The joint PMF induced by a discrete CPT.
    This wraps `jointWeight` as a proper `PMF` structure. -/
noncomputable def jointPMF (cpt : bn.DiscreteCPT) : PMF bn.JointSpace :=
  ⟨cpt.jointWeight, jointWeight_hasSum_one cpt⟩

/-- The joint probability measure on JointSpace. -/
noncomputable def jointMeasure (cpt : bn.DiscreteCPT) : MeasureTheory.Measure bn.JointSpace :=
  cpt.jointPMF.toMeasure

/-- The joint measure is a probability measure. -/
instance jointMeasure_isProbabilityMeasure (cpt : bn.DiscreteCPT) :
    MeasureTheory.IsProbabilityMeasure cpt.jointMeasure :=
  PMF.toMeasure.isProbabilityMeasure cpt.jointPMF

end JointDistribution

end DiscreteCPT

end BayesianNetwork

end Mettapedia.ProbabilityTheory.BayesianNetworks
