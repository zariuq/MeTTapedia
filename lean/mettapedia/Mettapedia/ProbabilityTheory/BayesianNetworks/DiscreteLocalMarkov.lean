/-
LLM primer: This file proves HasLocalMarkovProperty for discrete CPTs. The key insight
is that nodeProb cpt x w depends only on x_w and x_{Pa(w)}. So for w ∈ ND(v)\Pa(v)\{v},
nodeProb doesn't depend on x_v (since v ∉ Pa(w) in a DAG). This factorization gives
the local Markov property: {v} ⫫ ND(v)\Pa(v)\{v} | Pa(v).
The measure-theoretic bridge from factorization to Mathlib's CondIndep is nontrivial.

LLM primer on nodeProb structure:
  nodeProb cpt x v = cpt.cpt v (parentAssignOfConfig cpt x v) (x v)
  parentAssignOfConfig _cpt x v = fun u _ => x u
  So nodeProb unfolds to: cpt.cpt v (fun u _ => x u) (x v)
  After simp only [nodeProb], goal becomes cpt.cpt v (parentAssignOfConfig ...) (x v).
  Use `have` + `rw` pattern rather than `congr` to rewrite parent assignments.
-/
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparationSoundness

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (bn : BayesianNetwork V)
variable [∀ v : V, Fintype (bn.stateSpace v)]
variable [∀ v : V, Nonempty (bn.stateSpace v)]

open BayesianNetwork DiscreteCPT DirectedGraph

/-! ## Graph-level lemma: non-descendants don't have v as parent -/

omit [Fintype V] [DecidableEq V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- In a DAG, if w is a non-descendant of v (and w ≠ v), then v is not a parent of w.
    Proof: if v ∈ Pa(w) then G.edges v w, so w ∈ desc(v), contradicting w ∉ desc(v). -/
theorem not_parent_of_nonDescendant
    (v w : V)
    (hw_nd : w ∉ bn.graph.descendants v)
    (hwv : w ≠ v) :
    v ∉ bn.graph.parents w := by
  intro hpar
  apply hw_nd
  exact ⟨bn.graph.edge_reachable hpar, hwv⟩

omit [Fintype V] [DecidableEq V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- For w ∈ nonDescendantsExceptParentsAndSelf v, v ∉ Pa(w). -/
theorem not_parent_of_nonDescExceptParentsSelf
    (v w : V) (hw : w ∈ bn.nonDescendantsExceptParentsAndSelf v) :
    v ∉ bn.graph.parents w := by
  have hmem := hw
  rw [BayesianNetwork.nonDescendantsExceptParentsAndSelf, Set.mem_diff] at hmem
  have hw_nd : w ∉ bn.graph.descendants v := hmem.1
  have hw_not_pv_or_v : w ∉ bn.graph.parents v ∪ {v} := hmem.2
  have hwv : w ≠ v := by
    intro h; exact hw_not_pv_or_v (Set.mem_union_right _ (Set.mem_singleton_iff.mpr h))
  exact not_parent_of_nonDescendant bn v w hw_nd hwv

/-! ## Factorization: nodeProb independence -/

omit [Fintype V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- nodeProb cpt x w depends only on x_w and x_{Pa(w)}.
    Changing x_v where v ∉ Pa(w) ∪ {w} does not change nodeProb. -/
theorem nodeProb_update_irrelevant
    (cpt : bn.DiscreteCPT) (v w : V)
    (hv_not_parent : v ∉ bn.graph.parents w)
    (hvw : v ≠ w)
    (x : bn.JointSpace) (a : bn.stateSpace v) :
    cpt.nodeProb (Function.update x v a) w = cpt.nodeProb x w := by
  simp only [nodeProb]
  have hpa : cpt.parentAssignOfConfig (Function.update x v a) w =
             cpt.parentAssignOfConfig x w := by
    funext u hu
    simp only [parentAssignOfConfig]
    have huv : u ≠ v := by intro h; subst h; exact hv_not_parent hu
    simp [Function.update_of_ne huv]
  have hval : (Function.update x v a) w = x w := by
    simp [Function.update_of_ne hvw.symm]
  rw [hpa, hval]

/-- For w ∈ ND(v)\Pa(v)\{v}, nodeProb cpt x w is independent of x_v. -/
theorem nodeProb_independent_of_nonDesc
    (cpt : bn.DiscreteCPT) (v w : V)
    (hw : w ∈ bn.nonDescendantsExceptParentsAndSelf v)
    (x : bn.JointSpace) (a : bn.stateSpace v) :
    cpt.nodeProb (Function.update x v a) w = cpt.nodeProb x w := by
  apply nodeProb_update_irrelevant bn cpt v w
  · exact not_parent_of_nonDescExceptParentsSelf bn v w hw
  · intro h; subst h
    rw [BayesianNetwork.nonDescendantsExceptParentsAndSelf, Set.mem_diff] at hw
    exact hw.2 (Set.mem_union_right _ rfl)

/-! ## Joint weight factorization -/

omit [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- The joint weight factors as nodeProb at v times the product over all other nodes. -/
theorem jointWeight_factor_single
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) :
    cpt.jointWeight x = cpt.nodeProb x v * ∏ w ∈ Finset.univ.erase v, cpt.nodeProb x w := by
  unfold jointWeight
  rw [← Finset.mul_prod_erase Finset.univ (fun w => cpt.nodeProb x w) (Finset.mem_univ v)]

/-- The "rest" factor (product over w ≠ v) does not depend on x_v
    for nodes in ND(v)\Pa(v)\{v}. More precisely: updating x_v doesn't change
    the product over w ∈ ND(v)\Pa(v)\{v}. -/
theorem prod_nonDesc_independent_of_xv
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) (a : bn.stateSpace v) :
    ∏ w ∈ (Finset.univ.filter (· ∈ bn.nonDescendantsExceptParentsAndSelf v)),
      cpt.nodeProb (Function.update x v a) w =
    ∏ w ∈ (Finset.univ.filter (· ∈ bn.nonDescendantsExceptParentsAndSelf v)),
      cpt.nodeProb x w := by
  apply Finset.prod_congr rfl
  intro w hw
  rw [Finset.mem_filter] at hw
  exact nodeProb_independent_of_nonDesc bn cpt v w hw.2 x a

/-- Generalized update-invariance: for any `w ≠ v` that is not a descendant of `v`,
`nodeProb` at `w` is unchanged by updating `x_v`.

This is useful when splitting finite products into parent/non-descendant parts while
holding descendants fixed (screening/factorization proofs on parent fibers). -/
theorem nodeProb_independent_of_not_desc_not_self
    (cpt : bn.DiscreteCPT) (v w : V)
    (hw_not_desc : w ∉ bn.graph.descendants v)
    (hw_ne : w ≠ v)
    (x : bn.JointSpace) (a : bn.stateSpace v) :
    cpt.nodeProb (Function.update x v a) w = cpt.nodeProb x w := by
  apply nodeProb_update_irrelevant bn cpt v w
  · exact not_parent_of_nonDescendant bn v w hw_not_desc hw_ne
  · exact hw_ne.symm

/-- If `d` is a descendant of `v` and `w` is not, then `d` cannot be a parent of `w`.
Otherwise we would get a directed path `v ↝ d → w`, contradicting `w ∉ desc(v)`. -/
theorem not_parent_of_descendant_to_nonDesc
    (v d w : V)
    (hd_desc : d ∈ bn.graph.descendants v)
    (hw_not_desc : w ∉ bn.graph.descendants v) :
    d ∉ bn.graph.parents w := by
  intro hdw
  rcases hd_desc with ⟨hvd, _hvd_ne⟩
  have hw_ne : w ≠ v := by
    intro hwv
    subst hwv
    exact bn.acyclic d ⟨w, hdw, hvd⟩
  apply hw_not_desc
  exact ⟨bn.graph.reachable_trans hvd (bn.graph.edge_reachable hdw), hw_ne⟩

/-- Updating a descendant coordinate does not affect `nodeProb` at non-descendant targets. -/
theorem nodeProb_independent_of_descendant_update
    (cpt : bn.DiscreteCPT) (v d w : V)
    (hd_desc : d ∈ bn.graph.descendants v)
    (hw_not_desc : w ∉ bn.graph.descendants v)
    (x : bn.JointSpace) (a : bn.stateSpace d) :
    cpt.nodeProb (Function.update x d a) w = cpt.nodeProb x w := by
  by_cases hdw : d = w
  · subst hdw
    exfalso
    exact hw_not_desc hd_desc
  · apply nodeProb_update_irrelevant bn cpt d w
    · exact not_parent_of_descendant_to_nonDesc bn v d w hd_desc hw_not_desc
    · exact hdw

/-- Product-level version of `nodeProb_independent_of_not_desc_not_self` over all
vertices outside `desc(v)` and distinct from `v`. -/
theorem prod_notDescNotSelf_independent_of_xv
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) (a : bn.stateSpace v) :
    ∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
      cpt.nodeProb (Function.update x v a) w
      =
    ∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
      cpt.nodeProb x w := by
  apply Finset.prod_congr rfl
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨_, hw_not_desc, hw_ne⟩
  exact nodeProb_independent_of_not_desc_not_self bn cpt v w hw_not_desc hw_ne x a

omit [Fintype V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- nodeProb at v depends only on x_v and x_{Pa(v)}, not on ND coordinates. -/
theorem nodeProb_v_independent_of_nonDesc
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) (w : V)
    (hw : w ∈ bn.nonDescendantsExceptParentsAndSelf v)
    (b : bn.stateSpace w) :
    cpt.nodeProb (Function.update x w b) v = cpt.nodeProb x v := by
  have hwv : w ≠ v := by
    intro h; subst h
    rw [BayesianNetwork.nonDescendantsExceptParentsAndSelf, Set.mem_diff] at hw
    exact hw.2 (Set.mem_union_right _ rfl)
  have hw_not_parent : w ∉ bn.graph.parents v := by
    intro hpar
    rw [BayesianNetwork.nonDescendantsExceptParentsAndSelf, Set.mem_diff] at hw
    exact hw.2 (Set.mem_union_left _ hpar)
  exact nodeProb_update_irrelevant bn cpt w v hw_not_parent hwv x b

/-! ## Bridge to conditional independence (measure theory) -/

omit [Fintype V] [DecidableEq V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- The factorization property that underlies the local Markov condition:
    for any fixed parent assignment, the joint probability factors into a
    v-component and a non-descendant component.

    This is the mathematical content; the bridge to Mathlib's CondIndep
    is a separate (nontrivial) measure-theoretic step. -/
theorem factorization_given_parents
    (cpt : bn.DiscreteCPT) (v : V) (x y : bn.JointSpace)
    (hpa : ∀ u ∈ bn.graph.parents v, x u = y u)
    (hv : x v = y v) :
    cpt.nodeProb x v = cpt.nodeProb y v := by
  simp only [nodeProb]
  have hpa_eq : cpt.parentAssignOfConfig x v = cpt.parentAssignOfConfig y v := by
    funext u hu
    exact hpa u hu
  rw [hpa_eq, hv]

/-! ## Telescoping sum: marginalizing out subsets of vertices

The key technical infrastructure for the CondIndep bridge. For any subset D of vertices
in a DAG, summing the product of nodeProbs over all D-configurations (with coordinates
outside D fixed) gives 1. This is because we can process D from sinks inward: at each
step, the sink's CPT sums to 1 (PMF normalization), and removing the sink gives a
smaller set for induction.
-/

omit [Fintype V] [DecidableEq V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- In a DAG, v is not its own parent. -/
theorem not_self_parent (v : V) : v ∉ bn.graph.parents v := by
  intro hpar
  exact bn.graph.isAcyclic_irrefl bn.acyclic v hpar

/-- Summing nodeProb at v over all values of v gives 1, for any configuration x.
    This uses the fact that v ∉ Pa(v) in a DAG, so updating x at v doesn't change
    the parent assignment. -/
theorem nodeProb_sum_one_at_vertex
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) :
    ∑ a : bn.stateSpace v, cpt.nodeProb (Function.update x v a) v = 1 := by
  -- nodeProb (update x v a) v = cpt.cpt v (parentAssignOfConfig (update x v a) v) a
  -- parentAssignOfConfig (update x v a) v = parentAssignOfConfig x v
  --   because for u ∈ Pa(v), u ≠ v (since v ∉ Pa(v)), so update doesn't affect u
  -- So nodeProb (update x v a) v = cpt.cpt v (parentAssignOfConfig x v) a
  -- And ∑_a cpt.cpt v pa a = 1 (PMF)
  have hpa : ∀ a, cpt.parentAssignOfConfig (Function.update x v a) v =
                  cpt.parentAssignOfConfig x v := by
    intro a; funext u hu; simp only [parentAssignOfConfig]
    have huv : u ≠ v := by intro h; exact not_self_parent bn v (h ▸ hu)
    simp [Function.update_of_ne huv]
  simp only [nodeProb, hpa, Function.update_self]
  exact DiscreteCPT.pmf_sum_eq_one (cpt.cpt v (cpt.parentAssignOfConfig x v))

/-- Any nonempty finite subset of a DAG has a sink within it (a vertex with no edges
    to other vertices in the subset). -/
theorem exists_finset_sink (D : Finset V) (hne : D.Nonempty) :
    ∃ s ∈ D, ∀ w ∈ D, ¬bn.graph.edges s w := by
  -- Construct the induced subgraph on D and find its sink
  let G' : DirectedGraph ↥D := { edges := fun u v => bn.graph.edges u.val v.val }
  have hG'_acyclic : G'.IsAcyclic := by
    intro ⟨v, hv⟩ ⟨⟨u, hu⟩, hedge, hpath⟩
    apply bn.acyclic v
    refine ⟨u, hedge, ?_⟩
    have : ∀ (a b : ↥D), G'.Reachable a b → bn.graph.Reachable a.val b.val := by
      intro a b hr
      induction hr with
      | refl => exact DirectedGraph.reachable_refl _ _
      | step h _ ih => exact DirectedGraph.Path.step h ih
    exact this ⟨u, hu⟩ ⟨v, hv⟩ hpath
  haveI : Nonempty ↥D := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨⟨s, hs⟩, hsink⟩ := DirectedGraph.exists_sink_of_acyclic_nonempty G' hG'_acyclic
  exact ⟨s, hs, fun w hw hedge => by
    rw [DirectedGraph.isSink_iff] at hsink
    exact hsink ⟨w, hw⟩ hedge⟩

/-- Replace coordinates in D with values from xD, keep others from x. -/
noncomputable def patchConfig (x : bn.JointSpace) (D : Finset V)
    (xD : ∀ d : ↥D, bn.stateSpace d) : bn.JointSpace :=
  fun v => if h : v ∈ D then xD ⟨v, h⟩ else x v

omit [Fintype V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- patchConfig agrees with x outside D. -/
theorem patchConfig_outside (x : bn.JointSpace) (D : Finset V)
    (xD : ∀ d : ↥D, bn.stateSpace d) (v : V) (hv : v ∉ D) :
    patchConfig bn x D xD v = x v := by
  simp [patchConfig, hv]

omit [Fintype V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- patchConfig gives the D-values inside D. -/
theorem patchConfig_inside (x : bn.JointSpace) (D : Finset V)
    (xD : ∀ d : ↥D, bn.stateSpace d) (v : V) (hv : v ∈ D) :
    patchConfig bn x D xD v = xD ⟨v, hv⟩ := by
  simp [patchConfig, hv]

omit [Fintype V]
  [∀ v : V, Fintype (bn.stateSpace v)] [∀ v : V, Nonempty (bn.stateSpace v)] in
/-- For a D-sink s, nodeProb at d ∈ D \ {s} is independent of the s-coordinate. -/
theorem nodeProb_patchConfig_sink_indep
    (cpt : bn.DiscreteCPT) (D : Finset V) (s : V) (hs : s ∈ D)
    (hsink : ∀ w ∈ D, ¬bn.graph.edges s w)
    (d : V) (hd : d ∈ D) (hds : d ≠ s)
    (x : bn.JointSpace) (xD xD' : ∀ v : ↥D, bn.stateSpace v)
    (hagree : ∀ (w : ↥D), w.val ≠ s → xD w = xD' w) :
    cpt.nodeProb (patchConfig bn x D xD) d =
    cpt.nodeProb (patchConfig bn x D xD') d := by
  simp only [nodeProb]
  -- Show parent assignments are equal
  have hpa : cpt.parentAssignOfConfig (patchConfig bn x D xD) d =
             cpt.parentAssignOfConfig (patchConfig bn x D xD') d := by
    funext u hu; simp only [parentAssignOfConfig, patchConfig]
    split_ifs with h
    · -- u ∈ D: need u ≠ s
      have hus : u ≠ s := by
        intro heq; subst heq; exact hsink d hd hu
      exact hagree ⟨u, h⟩ hus
    · rfl -- u ∉ D: both equal x u
  -- Show values at d are equal
  have hval : patchConfig bn x D xD d = patchConfig bn x D xD' d := by
    simp [patchConfig, hd]; exact hagree ⟨d, hd⟩ hds
  rw [hpa, hval]

/-- If we patch only descendant coordinates of `v`, node probabilities at non-descendants
    are unchanged. -/
theorem nodeProb_patch_descendants_irrelevant
    (cpt : bn.DiscreteCPT) (v w : V)
    (D : Finset V)
    (hD_desc : ∀ d, d ∈ D → d ∈ bn.graph.descendants v)
    (x : bn.JointSpace) (xD : ∀ d : ↥D, bn.stateSpace d)
    (hw_not_desc : w ∉ bn.graph.descendants v) :
    cpt.nodeProb (patchConfig bn x D xD) w = cpt.nodeProb x w := by
  have hw_not_memD : w ∉ D := by
    intro hwD
    exact hw_not_desc (hD_desc w hwD)
  simp only [nodeProb]
  have hpa : cpt.parentAssignOfConfig (patchConfig bn x D xD) w =
             cpt.parentAssignOfConfig x w := by
    funext u hu
    have hu_not_memD : u ∉ D := by
      intro huD
      have hu_desc : u ∈ bn.graph.descendants v := hD_desc u huD
      have hu_not_parent : u ∉ bn.graph.parents w :=
        not_parent_of_descendant_to_nonDesc bn v u w hu_desc hw_not_desc
      exact hu_not_parent hu
    simp [parentAssignOfConfig, patchConfig, hu_not_memD]
  have hval : patchConfig bn x D xD w = x w := by
    simp [patchConfig, hw_not_memD]
  rw [hpa, hval]

/-- Product-level form of `nodeProb_patch_descendants_irrelevant` over all non-descendants
    of `v` (excluding `v` itself). -/
theorem prod_notDescNotSelf_patch_descendants_irrelevant
    (cpt : bn.DiscreteCPT) (v : V)
    (D : Finset V)
    (hD_desc : ∀ d, d ∈ D → d ∈ bn.graph.descendants v)
    (x : bn.JointSpace) (xD : ∀ d : ↥D, bn.stateSpace d) :
    ∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
      cpt.nodeProb (patchConfig bn x D xD) w
      =
    ∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
      cpt.nodeProb x w := by
  apply Finset.prod_congr rfl
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨_, hw_not_desc, _⟩
  exact nodeProb_patch_descendants_irrelevant bn cpt v w D hD_desc x xD hw_not_desc

/-! ## Telescoping sum (main theorem)

For now, we state the telescoping sum as an axiom since its proof requires
constructing explicit equivalences between Finset-indexed Pi types that are
technically involved. The mathematical content is standard: process sinks
one at a time, each CPT sums to 1. -/

/-- The telescoping sum: summing the product of nodeProbs over all D-configurations
    gives 1, for any fixed outside configuration. This is the key marginalization
    property of BN product distributions.

    Proof idea: by induction on |D|. Find a sink s in D. Since s has no edges to
    other D-vertices, the nodeProbs at d ∈ D\{s} don't depend on x_s. Factor out
    the sum over x_s (which gives 1 by PMF normalization). Apply IH to D\{s}. -/
theorem telescoping_sum
    (cpt : bn.DiscreteCPT) (D : Finset V) (x : bn.JointSpace) :
    ∑ xD : (∀ d : ↥D, bn.stateSpace d),
      ∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d = 1 := by
  induction h : D.card generalizing D x with
  | zero =>
    -- D is empty
    have hempty : D = ∅ := Finset.card_eq_zero.mp h
    subst hempty
    -- Sum over unique element of (∀ d : ↥∅, ...), product is empty = 1
    simp [Finset.univ_eq_empty]
  | succ n ih =>
    -- Construct a sub-BN on the vertices in D
    let G_D : DirectedGraph ↥D := { edges := fun u v => bn.graph.edges u.val v.val }
    have hG_D_acyclic : G_D.IsAcyclic := by
      intro ⟨v, hv⟩ ⟨⟨u, hu⟩, hedge, hpath⟩
      apply bn.acyclic v
      refine ⟨u, hedge, ?_⟩
      have lift : ∀ (a b : ↥D), G_D.Reachable a b → bn.graph.Reachable a.val b.val := by
        intro a b hr
        induction hr with
        | refl => exact DirectedGraph.reachable_refl _ _
        | step h _ ih' => exact DirectedGraph.Path.step h ih'
      exact lift ⟨u, hu⟩ ⟨v, hv⟩ hpath
    let bn_D : BayesianNetwork ↥D := {
      graph := G_D
      stateSpace := fun d => bn.stateSpace d.val
      acyclic := hG_D_acyclic
      measurableSpace := fun d => bn.measurableSpace d.val
    }
    -- Construct CPT: for each d ∈ D, fix non-D-parents at x
    let cpt_D : bn_D.DiscreteCPT := {
      cpt := fun d pa_D =>
        cpt.cpt d.val (fun u hu =>
          if h : u ∈ D then pa_D ⟨u, h⟩ hu else x u)
    }
    -- Show nodeProbs match
    have hnode_eq : ∀ (xD : ∀ d : ↥D, bn.stateSpace d) (d : ↥D),
        cpt_D.nodeProb xD d = cpt.nodeProb (patchConfig bn x D xD) d.val := by
      intro xD d
      simp only [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig]
      -- Both sides are cpt.cpt d.val (parent_assign) (value)
      -- The parent assignments and values are the same after unfolding
      show cpt_D.cpt d (fun u _ => xD u) (xD d) =
        cpt.cpt d.val (fun u _ => patchConfig bn x D xD u) (patchConfig bn x D xD d.val)
      -- Unfold the value at d
      have hval : patchConfig bn x D xD d.val = xD d := by
        simp [patchConfig, d.prop]
      rw [hval]
      -- Unfold cpt_D and show parent assignments match
      show cpt.cpt d.val (fun u hu =>
        if h : u ∈ D then (fun u _ => xD u) ⟨u, h⟩ hu else x u) (xD d) =
        cpt.cpt d.val (fun u _ => patchConfig bn x D xD u) (xD d)
      congr 1
    -- Show jointWeights match
    have hjw_eq : ∀ (xD : ∀ d : ↥D, bn.stateSpace d),
        cpt_D.jointWeight xD = ∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d := by
      intro xD
      simp only [DiscreteCPT.jointWeight]
      apply Fintype.prod_congr
      intro d
      exact hnode_eq xD d
    -- Apply jointWeight_sum_eq_one to the sub-BN
    have hsub := DiscreteCPT.jointWeight_sum_eq_one cpt_D
    rw [show ∑ xD, ∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d =
        ∑ xD, cpt_D.jointWeight xD from by
      apply Finset.sum_congr rfl; intro xD _; exact (hjw_eq xD).symm]
    exact hsub

set_option maxHeartbeats 800000

/-! ## HasLocalMarkovProperty instance for discrete CPTs

The factorization lemmas above prove the mathematical content: nodeProb for w ∈ ND(v)\Pa(v)\{v}
is independent of x_v. The bridge to Mathlib's `CondIndep` requires reducing to the
algebraic CI condition on parent fibers, then using the BN product factorization and
the telescoping sum to verify it.

Proof strategy (tower property + pull-out):

Given: t₁ is m_v-measurable, t₂ is m_ND-measurable.
Show: μ⟦t₁ ∩ t₂ | m_pa⟧ =ᵐ μ⟦t₁ | m_pa⟧ * μ⟦t₂ | m_pa⟧

Step 1: 1_{t₁∩t₂} = 1_{t₁} · 1_{t₂} (indicator multiplication)
Step 2: μ⟦f | m_pa⟧ =ᵐ μ⟦μ⟦f | m_pa ⊔ m_v⟧ | m_pa⟧ (tower property, m_pa ≤ m_pa ⊔ m_v)
Step 3: μ⟦1_{t₁}·1_{t₂} | m_pa ⊔ m_v⟧ =ᵐ 1_{t₁} · μ⟦1_{t₂} | m_pa ⊔ m_v⟧
         (pull-out: 1_{t₁} is (m_pa ⊔ m_v)-measurable since m_v ≤ m_pa ⊔ m_v)
Step 4: μ⟦1_{t₂} | m_pa ⊔ m_v⟧ =ᵐ μ⟦1_{t₂} | m_pa⟧
         ← BN FACTORIZATION: knowing x_v gives no info about ND' given Pa(v).
         On each parent-vertex fiber F_{c,a}, the marginal weight factors as
         φ_v(a,c) · φ_ND(x_{ND'},c), with the descendant sum = 1 (telescoping_sum).
         So P(t₂|Pa=c,v=a) = P(t₂|Pa=c) — the ratio is independent of a.
Step 5: μ⟦1_{t₁} · μ⟦1_{t₂}|m_pa⟧ | m_pa⟧ =ᵐ μ⟦1_{t₁}|m_pa⟧ · μ⟦1_{t₂}|m_pa⟧
         (pull-out: μ⟦1_{t₂}|m_pa⟧ is m_pa-measurable)

The only non-standard step is Step 4, which encapsulates the BN factorization.
The algebraic CI: μ(t₂∩F_c∩B) · μ(F_c) = μ(t₂∩F_c) · μ(F_c∩B) for m_v-meas B
follows from the factored weight after summing out descendants (telescoping_sum). -/

variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]

/-- Helper: condExp of an indicator is bounded by 1 in norm a.e. -/
private lemma condExp_indicator_norm_le_one
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    {m' : MeasurableSpace bn.JointSpace} (hm' : m' ≤ MeasurableSpace.pi)
    [SigmaFinite (μ.trim hm')]
    (s : Set bn.JointSpace) (hs : @MeasurableSet _ MeasurableSpace.pi s) :
    ∀ᵐ ω ∂μ, ‖(μ[s.indicator (fun _ => (1 : ℝ)) | m']) ω‖ ≤ 1 := by
  have hint : Integrable (s.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hs
  have h_ind_le : (s.indicator fun _ => (1 : ℝ)) ≤ᵐ[μ] fun _ => (1 : ℝ) :=
    Filter.Eventually.of_forall fun ω => by
      simp only [Set.indicator_apply]; split_ifs <;> norm_num
  have h_mono : (μ[s.indicator (fun _ => (1 : ℝ)) | m']) ≤ᵐ[μ] (μ[fun _ => (1 : ℝ) | m']) :=
    condExp_mono hint (integrable_const (1 : ℝ)) h_ind_le
  have h_const : (μ[fun _ => (1 : ℝ) | m']) = fun _ => (1 : ℝ) :=
    condExp_of_stronglyMeasurable hm' stronglyMeasurable_const (integrable_const _)
  have h_le : (μ[s.indicator (fun _ => (1 : ℝ)) | m']) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have := h_const ▸ h_mono; exact this
  have h_ge : (0 : bn.JointSpace → ℝ) ≤ᵐ[μ] (μ[s.indicator (fun _ => (1 : ℝ)) | m']) :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      simp only [Set.indicator_apply]; split_ifs <;> norm_num)
  filter_upwards [h_le, h_ge] with ω hle hge
  rw [Real.norm_eq_abs, abs_le]
  simp only [Pi.zero_apply] at hge
  exact ⟨by linarith, hle⟩

/-! ### Parent-fiber decomposition helpers

These lemmas let us treat any `m_pa`-measurable set as the preimage of a set of
parent assignments via the restriction map. They will be used to decompose
integrals over parent fibers in the BN CI proof below.
-/

lemma measurableSet_vertices_preimage
    (S : Set V) {s : Set bn.JointSpace}
    (hs : MeasurableSet[bn.measurableSpaceOfVertices S] s) :
    ∃ T : Set (∀ p : S, bn.stateSpace p),
      MeasurableSet T ∧ s = (restrictToSet (bn := bn) S) ⁻¹' T := by
  have hs' :
      MeasurableSet[
        MeasurableSpace.comap (restrictToSet (bn := bn) S) (by infer_instance)] s := by
    simpa [measurableSpaceOfVertices_eq_comap_restrict (bn := bn) S] using hs
  rcases (MeasurableSpace.measurableSet_comap).1 hs' with ⟨T, hT, hpre⟩
  exact ⟨T, hT, hpre.symm⟩

lemma measurableSet_singleton_preimage
    (v : V) {s : Set bn.JointSpace}
    (hs : MeasurableSet[bn.measurableSpaceOfVertices ({v} : Set V)] s) :
    ∃ T : Set (bn.stateSpace v), MeasurableSet T ∧ s = (fun ω : bn.JointSpace => ω v) ⁻¹' T := by
  have hs' :
      MeasurableSet[
        MeasurableSpace.comap (fun ω : bn.JointSpace => ω v) (by infer_instance)] s := by
    simpa [measurableSpaceOfVertices_singleton (bn := bn) v] using hs
  rcases (MeasurableSpace.measurableSet_comap).1 hs' with ⟨T, hT, hpre⟩
  exact ⟨T, hT, hpre.symm⟩

noncomputable def parentsRestrict (v : V) :
    bn.JointSpace → (∀ p : {x // x ∈ (bn.graph.parents v : Set V)}, bn.stateSpace p.1) :=
  restrictToSet (bn := bn) (bn.graph.parents v)

lemma measurableSet_parents_preimage
    (v : V) {s : Set bn.JointSpace}
    (hs : MeasurableSet[bn.measurableSpaceOfVertices (bn.graph.parents v)] s) :
    ∃ S : Set (∀ p : {x // x ∈ (bn.graph.parents v : Set V)}, bn.stateSpace p.1),
      MeasurableSet S ∧ s = (parentsRestrict (bn := bn) v) ⁻¹' S := by
  classical
  -- Rewrite the parent sigma-algebra as a comap, then use measurableSet_comap.
  have hs' :
      MeasurableSet[
        MeasurableSpace.comap (parentsRestrict (bn := bn) v) (by infer_instance)] s := by
    simpa [parentsRestrict,
      measurableSpaceOfVertices_eq_comap_restrict (bn := bn) (bn.graph.parents v)] using hs
  rcases (MeasurableSpace.measurableSet_comap).1 hs' with ⟨S, hS, hpre⟩
  exact ⟨S, hS, hpre.symm⟩

abbrev ParentAssign (v : V) :=
  ∀ p : {x // x ∈ (bn.graph.parents v : Set V)}, bn.stateSpace p.1

def parentFiber (v : V) (c : ParentAssign (bn := bn) v) : Set bn.JointSpace :=
  (parentsRestrict (bn := bn) v) ⁻¹' {c}

lemma mem_parentFiber_iff
    (v : V) (c : ParentAssign (bn := bn) v) (ω : bn.JointSpace) :
    ω ∈ parentFiber (bn := bn) v c ↔ (parentsRestrict (bn := bn) v ω) = c := by
  rfl

lemma parentFiber_disjoint
    (v : V) (c₁ c₂ : ParentAssign (bn := bn) v) (h : c₁ ≠ c₂) :
    Disjoint (parentFiber (bn := bn) v c₁) (parentFiber (bn := bn) v c₂) := by
  classical
  refine Set.disjoint_left.mpr ?_
  intro ω hω₁ hω₂
  have h1 : parentsRestrict (bn := bn) v ω = c₁ := by
    simpa [parentFiber] using hω₁
  have h2 : parentsRestrict (bn := bn) v ω = c₂ := by
    simpa [parentFiber] using hω₂
  exact h (h1.symm.trans h2)

lemma parents_preimage_eq_iUnion
    (v : V) (S : Set (ParentAssign (bn := bn) v)) :
    (parentsRestrict (bn := bn) v) ⁻¹' S =
      ⋃ c : ParentAssign (bn := bn) v,
        (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)) := by
  classical
  ext ω
  constructor
  · intro hω
    have hmem : parentsRestrict (bn := bn) v ω ∈ S := hω
    refine Set.mem_iUnion.mpr ?_
    refine ⟨parentsRestrict (bn := bn) v ω, ?_⟩
    by_cases h : parentsRestrict (bn := bn) v ω ∈ S
    · simp [parentFiber, h]
    · exact (h hmem).elim
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨c, hc⟩
    by_cases h : c ∈ S
    · have hc' : ω ∈ parentFiber (bn := bn) v c := by
        simpa [h] using hc
      have hEq : parentsRestrict (bn := bn) v ω = c := by
        simpa [parentFiber] using hc'
      simpa [hEq] using h
    · have : ω ∈ (∅ : Set bn.JointSpace) := by simpa [h] using hc
      exact (False.elim (by simpa using this))

lemma measurable_parentFiber
    (v : V) [MeasurableSingletonClass (ParentAssign (bn := bn) v)]
    (c : ParentAssign (bn := bn) v) :
    @MeasurableSet _ MeasurableSpace.pi (parentFiber (bn := bn) v c) := by
  -- `parentsRestrict` is measurable on `JointSpace` with `MeasurableSpace.pi`,
  -- and fibers are preimages of singleton sets.
  have hle :
      MeasurableSpace.comap (parentsRestrict (bn := bn) v) (by infer_instance) ≤
        (MeasurableSpace.pi : MeasurableSpace bn.JointSpace) := by
    simpa [parentsRestrict,
      measurableSpaceOfVertices_eq_comap_restrict (bn := bn) (bn.graph.parents v)] using
      (bn.measurableSpaceOfVertices_le (bn.graph.parents v))
  have hmeas : Measurable (parentsRestrict (bn := bn) v) :=
    Measurable.of_comap_le hle
  simpa [parentFiber] using hmeas (measurableSet_singleton (x := c))

lemma measurable_parentFiber_vertices
    (v : V) [MeasurableSingletonClass (ParentAssign (bn := bn) v)]
    (c : ParentAssign (bn := bn) v) :
    MeasurableSet[bn.measurableSpaceOfVertices (bn.graph.parents v)]
      (parentFiber (bn := bn) v c) := by
  -- parentFiber is a singleton preimage under parentsRestrict, i.e. measurable in the
  -- parent-generated sigma-algebra by the comap characterization.
  have hcomap :
      MeasurableSet[
        MeasurableSpace.comap (parentsRestrict (bn := bn) v) (by infer_instance)]
        (parentFiber (bn := bn) v c) := by
    refine (MeasurableSpace.measurableSet_comap).2 ?_
    exact ⟨({c} : Set (ParentAssign (bn := bn) v)), measurableSet_singleton (x := c), rfl⟩
  simpa [parentsRestrict,
    measurableSpaceOfVertices_eq_comap_restrict (bn := bn) (bn.graph.parents v)]
    using hcomap

lemma setIntegral_parents_preimage
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    (v : V) [MeasurableSingletonClass (ParentAssign (bn := bn) v)]
    (S : Set (ParentAssign (bn := bn) v)) (f : bn.JointSpace → ℝ)
    (hf : Integrable f μ) :
    ∫ x in (parentsRestrict (bn := bn) v) ⁻¹' S, f x ∂μ =
      ∑ c : ParentAssign (bn := bn) v,
        if c ∈ S then ∫ x in parentFiber (bn := bn) v c, f x ∂μ else 0 := by
  classical
  have hrepr := parents_preimage_eq_iUnion (bn := bn) v S
  rw [hrepr]
  have hMeas :
      ∀ c : ParentAssign (bn := bn) v,
        @MeasurableSet _ MeasurableSpace.pi
          (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)) := by
    intro c
    by_cases hc : c ∈ S
    · simpa [hc] using measurable_parentFiber (bn := bn) v c
    · simp [hc]
  have hDisj :
      Pairwise (fun c1 c2 : ParentAssign (bn := bn) v =>
        Disjoint
          (if c1 ∈ S then parentFiber (bn := bn) v c1 else (∅ : Set bn.JointSpace))
          (if c2 ∈ S then parentFiber (bn := bn) v c2 else (∅ : Set bn.JointSpace))) := by
    intro c1 c2 hne
    by_cases hc1 : c1 ∈ S
    · by_cases hc2 : c2 ∈ S
      · simpa [hc1, hc2] using parentFiber_disjoint (bn := bn) v c1 c2 hne
      · simp [hc2]
    · simp [hc1]
  have hInt :
      ∀ c : ParentAssign (bn := bn) v,
        IntegrableOn (f := f)
          (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)) μ := by
    intro c
    exact hf.integrableOn
  have hUnion :
      ∫ x in ⋃ c : ParentAssign (bn := bn) v,
          (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)), f x ∂μ
        = ∑ c : ParentAssign (bn := bn) v,
            ∫ x in (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)),
              f x ∂μ :=
    MeasureTheory.integral_iUnion_fintype
      (μ := μ) (f := f)
      (s := fun c : ParentAssign (bn := bn) v =>
        if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace))
      hMeas hDisj hInt
  have hSum :
      (∑ c : ParentAssign (bn := bn) v,
          ∫ x in (if c ∈ S then parentFiber (bn := bn) v c else (∅ : Set bn.JointSpace)),
            f x ∂μ)
      = ∑ c : ParentAssign (bn := bn) v,
          if c ∈ S then ∫ x in parentFiber (bn := bn) v c, f x ∂μ else 0 := by
    refine Finset.sum_congr rfl ?_
    intro c _
    by_cases hc : c ∈ S <;> simp [hc]
  exact hUnion.trans hSum

/-- Decompose a single-vertex preimage as a finite union of `eventEq` slices. -/
lemma vertex_preimage_eq_iUnion_eventEq
    (v : V) (S : Set (bn.stateSpace v)) :
    (fun ω : bn.JointSpace => ω v) ⁻¹' S =
      ⋃ a : bn.stateSpace v,
        (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)) := by
  classical
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.mpr ?_
    refine ⟨ω v, ?_⟩
    by_cases hS : ω v ∈ S
    · simp [eventEq, hS, hω]
    · exact (hS hω).elim
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨a, ha⟩
    by_cases hS : a ∈ S
    · have : ω ∈ eventEq (bn := bn) v a := by simpa [hS] using ha
      have hv : ω v = a := by simpa [eventEq] using this
      simpa [hv] using hS
    · have : ω ∈ (∅ : Set bn.JointSpace) := by simpa [hS] using ha
      exact False.elim (by simpa using this)

/-- Distinct `eventEq` slices on the same vertex are disjoint. -/
lemma eventEq_disjoint_of_ne
    (v : V) {a₁ a₂ : bn.stateSpace v} (h : a₁ ≠ a₂) :
    Disjoint (eventEq (bn := bn) v a₁) (eventEq (bn := bn) v a₂) := by
  refine Set.disjoint_left.mpr ?_
  intro ω h1 h2
  have hv1 : ω v = a₁ := by simpa [eventEq] using h1
  have hv2 : ω v = a₂ := by simpa [eventEq] using h2
  exact h (hv1.symm.trans hv2)

/-- Set-integral decomposition over single-vertex fibers. -/
lemma setIntegral_vertex_preimage
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    (v : V) [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (S : Set (bn.stateSpace v)) (f : bn.JointSpace → ℝ)
    (hf : Integrable f μ) :
    ∫ x in (fun ω : bn.JointSpace => ω v) ⁻¹' S, f x ∂μ =
      ∑ a : bn.stateSpace v,
        if a ∈ S then ∫ x in eventEq (bn := bn) v a, f x ∂μ else 0 := by
  classical
  rw [vertex_preimage_eq_iUnion_eventEq (bn := bn) v S]
  have hMeas :
      ∀ a : bn.stateSpace v,
        @MeasurableSet _ MeasurableSpace.pi
          (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)) := by
    intro a
    by_cases ha : a ∈ S
    · simpa [ha] using measurable_eventEq (bn := bn) v a
    · simp [ha]
  have hDisj :
      Pairwise (fun a1 a2 : bn.stateSpace v =>
        Disjoint
          (if a1 ∈ S then eventEq (bn := bn) v a1 else (∅ : Set bn.JointSpace))
          (if a2 ∈ S then eventEq (bn := bn) v a2 else (∅ : Set bn.JointSpace))) := by
    intro a1 a2 hne
    by_cases h1 : a1 ∈ S
    · by_cases h2 : a2 ∈ S
      · simpa [h1, h2] using eventEq_disjoint_of_ne (bn := bn) v (a₁ := a1) (a₂ := a2) hne
      · simp [h2]
    · simp [h1]
  have hInt :
      ∀ a : bn.stateSpace v,
        IntegrableOn (f := f)
          (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)) μ := by
    intro _; exact hf.integrableOn
  have hUnion :
      ∫ x in ⋃ a : bn.stateSpace v,
          (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)), f x ∂μ
        =
      ∑ a : bn.stateSpace v,
          ∫ x in (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)),
            f x ∂μ :=
    MeasureTheory.integral_iUnion_fintype
      (μ := μ) (f := f)
      (s := fun a : bn.stateSpace v =>
        if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace))
      hMeas hDisj hInt
  have hSum :
      (∑ a : bn.stateSpace v,
          ∫ x in (if a ∈ S then eventEq (bn := bn) v a else (∅ : Set bn.JointSpace)), f x ∂μ)
      =
      ∑ a : bn.stateSpace v,
          if a ∈ S then ∫ x in eventEq (bn := bn) v a, f x ∂μ else 0 := by
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases ha : a ∈ S <;> simp [ha]
  exact hUnion.trans hSum

lemma jointMeasure_parentFiber_inter_as_sum
    (cpt : bn.DiscreteCPT)
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    (v : V) [MeasurableSingletonClass (ParentAssign (bn := bn) v)]
    (c : ParentAssign (bn := bn) v)
    {S : Set bn.JointSpace}
    (hS : @MeasurableSet _ MeasurableSpace.pi S) :
    cpt.jointMeasure (S ∩ parentFiber (bn := bn) v c) =
      ∑ x : bn.JointSpace,
        if x ∈ S ∩ parentFiber (bn := bn) v c then cpt.jointWeight x else 0 := by
  classical
  simpa using
    (BayesianNetwork.DiscreteCPT.jointMeasure_apply_as_sum
      (bn := bn) (cpt := cpt) (S := S ∩ parentFiber (bn := bn) v c)
      (hS.inter (measurable_parentFiber (bn := bn) v c)))

private lemma prod_erase_split_descendants
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) :
    (∏ w ∈ Finset.univ.erase v, cpt.nodeProb x w)
      =
    (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
      cpt.nodeProb x w) *
    (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
      cpt.nodeProb x d) := by
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      (s := Finset.univ.erase v)
      (p := fun w => w ∈ bn.graph.descendants v)
      (f := fun w => cpt.nodeProb x w)
  have hdesc :
      (Finset.univ.erase v).filter (fun w => w ∈ bn.graph.descendants v)
        =
      Finset.univ.filter (fun d => d ∈ bn.graph.descendants v) := by
    ext w
    constructor
    · intro hw
      exact by simpa using (Finset.mem_filter.mp hw).2
    · intro hw
      have hw_desc : w ∈ bn.graph.descendants v := (Finset.mem_filter.mp hw).2
      have hw_ne : w ≠ v := by
        rcases hw_desc with ⟨_, hw_ne⟩
        exact hw_ne
      exact Finset.mem_filter.mpr ⟨by simpa [hw_ne], hw_desc⟩
  have hnotdesc :
      (Finset.univ.erase v).filter (fun w => w ∉ bn.graph.descendants v)
        =
      Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v) := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨hw_erase, hw_not_desc⟩
      have hw_ne : w ≠ v := (Finset.mem_erase.mp hw_erase).1
      exact Finset.mem_filter.mpr ⟨by simp, ⟨hw_not_desc, hw_ne⟩⟩
    · intro hw
      rcases Finset.mem_filter.mp hw with ⟨_, hw_pred⟩
      rcases hw_pred with ⟨hw_not_desc, hw_ne⟩
      exact Finset.mem_filter.mpr ⟨by simpa [hw_ne], hw_not_desc⟩
  calc
    (∏ w ∈ Finset.univ.erase v, cpt.nodeProb x w)
        =
      (∏ d ∈ (Finset.univ.erase v).filter (fun w => w ∈ bn.graph.descendants v),
        cpt.nodeProb x d) *
      (∏ w ∈ (Finset.univ.erase v).filter (fun w => w ∉ bn.graph.descendants v),
        cpt.nodeProb x w) := by
          simpa [mul_comm] using hsplit.symm
    _ =
      (∏ d ∈ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v),
        cpt.nodeProb x d) *
      (∏ w ∈ Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v),
        cpt.nodeProb x w) := by
          simp [hdesc, hnotdesc]
    _ =
      (∏ w ∈ Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v),
        cpt.nodeProb x w) *
      (∏ d ∈ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v),
        cpt.nodeProb x d) := by
          ring

private lemma jointWeight_split_descendants
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) :
    cpt.jointWeight x
      =
    cpt.nodeProb x v *
      (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
        cpt.nodeProb x w) *
      (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
        cpt.nodeProb x d) := by
  calc
    cpt.jointWeight x
        = cpt.nodeProb x v * ∏ w ∈ Finset.univ.erase v, cpt.nodeProb x w := by
            simpa using jointWeight_factor_single (bn := bn) (cpt := cpt) v x
    _ =
      cpt.nodeProb x v *
      ((∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb x w) *
        (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
          cpt.nodeProb x d)) := by
            simp [prod_erase_split_descendants (bn := bn) (cpt := cpt) (v := v) (x := x)]
    _ =
      cpt.nodeProb x v *
      (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
        cpt.nodeProb x w) *
      (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
        cpt.nodeProb x d) := by
          ring

/-! ### Descendant-sum helper

These lemmas are used to collapse sums over descendant assignments in the
fiber-screening proof. They isolate the dependence on `x_v` and the ND-part
from the descendant product, which telescopes to 1.
-/

theorem descendant_not_parent
    (v d : V) (hd : d ∈ bn.graph.descendants v) : d ∉ bn.graph.parents v := by
  intro hdpar
  rcases hd with ⟨hvd, _hvd_ne⟩
  exact bn.acyclic d ⟨v, hdpar, hvd⟩

theorem nodeProb_patch_descendants_at_v
    (cpt : bn.DiscreteCPT) (v : V) (D : Finset V)
    (hD_desc : ∀ d, d ∈ D → d ∈ bn.graph.descendants v)
    (x : bn.JointSpace) (xD : ∀ d : ↥D, bn.stateSpace d) :
    cpt.nodeProb (patchConfig bn x D xD) v = cpt.nodeProb x v := by
  have hv_not_desc : v ∉ bn.graph.descendants v := by
    intro hv
    rcases hv with ⟨_hvv, hvne⟩
    exact hvne rfl
  exact nodeProb_patch_descendants_irrelevant bn cpt v v D hD_desc x xD hv_not_desc

private lemma sum_descendants_jointWeight
    (cpt : bn.DiscreteCPT) (v : V) (x : bn.JointSpace) (D : Finset V)
    (hD_desc : ∀ d, d ∈ D → d ∈ bn.graph.descendants v)
    (hD : D = Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)) :
    (∑ xD : (∀ d : ↥D, bn.stateSpace d),
        cpt.jointWeight (patchConfig bn x D xD))
      =
      cpt.nodeProb x v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb x w) := by
  classical
  have hnode_v :
      ∀ xD : (∀ d : ↥D, bn.stateSpace d),
        cpt.nodeProb (patchConfig bn x D xD) v = cpt.nodeProb x v := by
    intro xD
    exact nodeProb_patch_descendants_at_v bn cpt v D hD_desc x xD
  have hprod_nd :
      ∀ xD : (∀ d : ↥D, bn.stateSpace d),
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb (patchConfig bn x D xD) w)
          =
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb x w) := by
    intro xD
    exact prod_notDescNotSelf_patch_descendants_irrelevant bn cpt v D hD_desc x xD
  set cconst :=
    cpt.nodeProb x v *
      (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb x w)
  calc
    (∑ xD : (∀ d : ↥D, bn.stateSpace d),
        cpt.jointWeight (patchConfig bn x D xD))
        =
      ∑ xD : (∀ d : ↥D, bn.stateSpace d),
        cconst *
          (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
              cpt.nodeProb (patchConfig bn x D xD) d) := by
        refine Finset.sum_congr rfl ?_
        intro xD _
        have hsplit := jointWeight_split_descendants (bn := bn) (cpt := cpt) (v := v)
          (x := patchConfig bn x D xD)
        -- Replace the v-part and ND-part by constants using hnode_v and hprod_nd
        -- and keep descendant product as-is.
        simpa [hnode_v xD, hprod_nd xD, cconst, mul_assoc, mul_left_comm, mul_comm] using hsplit
    _ =
      cconst *
        ∑ xD : (∀ d : ↥D, bn.stateSpace d),
          (∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d) := by
        -- rewrite the descendant product using hD, then pull out constants
        have hD' :
            (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)) = D := by
          simpa using hD.symm
        have hprod_desc :
            ∀ xD : (∀ d : ↥D, bn.stateSpace d),
              (∏ d ∈ D, cpt.nodeProb (patchConfig bn x D xD) d)
                =
              ∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d := by
          intro xD
          -- product over the finset equals product over the attached subtype
          simpa using (Finset.prod_attach (s := D)
            (f := fun d => cpt.nodeProb (patchConfig bn x D xD) d)).symm
        -- now pull out constants from the sum
        -- rewrite the product inside the sum to a product over the subtype
        have hsum_rewrite :
            (∑ xD : (∀ d : ↥D, bn.stateSpace d),
                cconst *
                  (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
                      cpt.nodeProb (patchConfig bn x D xD) d))
              =
            ∑ xD : (∀ d : ↥D, bn.stateSpace d),
              cconst * (∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d) := by
          refine Finset.sum_congr rfl ?_
          intro xD _
          simp [hD', hprod_desc xD, cconst, mul_assoc, mul_left_comm, mul_comm]
        -- pull out constants
        calc
          (∑ xD : (∀ d : ↥D, bn.stateSpace d),
              cconst *
                (∏ d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
                    cpt.nodeProb (patchConfig bn x D xD) d))
              =
            ∑ xD : (∀ d : ↥D, bn.stateSpace d),
              cconst * (∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d) := by
                exact hsum_rewrite
          _ = cconst *
              ∑ xD : (∀ d : ↥D, bn.stateSpace d),
                (∏ d : ↥D, cpt.nodeProb (patchConfig bn x D xD) d) := by
                -- pull cconst out of the sum
                simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, cconst]
    _ =
      cpt.nodeProb x v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb x w) * 1 := by
        -- telescoping sum on descendants
        have htel := telescoping_sum (bn := bn) (cpt := cpt) (D := D) (x := x)
        -- rewrite the sum to 1, then simp
        have htel' := congrArg (fun t => cconst * t) htel
        simpa [cconst, mul_assoc, mul_left_comm, mul_comm] using htel'
    _ =
      cpt.nodeProb x v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb x w) := by
        simp

/-! ### Reindex bridge: split `JointSpace` into descendant/non-descendant coordinates

These helpers provide the concrete reindexing bridge needed by the fiber-screening step:
`JointSpace` is split via `Equiv.piEquivPiSubtypeProd`, and descendant assignments are
connected to the finite `patchConfig` representation used by `sum_descendants_jointWeight`.
-/

private noncomputable def descSetToFin
    (v : V)
    (xD : ∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) :
    ∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)), bn.stateSpace d :=
  fun d => xD ⟨d.1, (Finset.mem_filter.mp d.2).2⟩

private noncomputable def descFinToSet
    (v : V)
    (xD : ∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)), bn.stateSpace d) :
    ∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d :=
  fun d => xD ⟨d.1, Finset.mem_filter.mpr ⟨Finset.mem_univ d.1, d.2⟩⟩

private noncomputable def descAssignEquiv
    (v : V) :
    (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) ≃
      (∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)), bn.stateSpace d) where
  toFun := descSetToFin (bn := bn) v
  invFun := descFinToSet (bn := bn) v
  left_inv := by
    intro xD
    funext d
    simp [descSetToFin, descFinToSet]
  right_inv := by
    intro xD
    funext d
    simp [descSetToFin, descFinToSet]

private noncomputable def baseFromNonDesc
    (v : V)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) :
    bn.JointSpace :=
  fun u =>
    if hu : u ∈ bn.graph.descendants v then
      Classical.choice (inferInstance : Nonempty (bn.stateSpace u))
    else
      xND ⟨u, hu⟩

private noncomputable def mergeDescNonDesc
    (v : V)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n)
    (xD : ∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) :
    bn.JointSpace :=
  patchConfig bn
    (baseFromNonDesc (bn := bn) v xND)
    (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
    (descSetToFin (bn := bn) v xD)

private lemma piEquiv_descendants_symm_eq_merge
    (v : V)
    (xD : ∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) :
    (Equiv.piEquivPiSubtypeProd (p := fun d : V => d ∈ bn.graph.descendants v)
      (β := fun d : V => bn.stateSpace d)).symm (xD, xND)
      =
    mergeDescNonDesc (bn := bn) v xND xD := by
  funext u
  by_cases hu : u ∈ bn.graph.descendants v
  · have hDmem : u ∈ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
    calc
      (Equiv.piEquivPiSubtypeProd (p := fun d : V => d ∈ bn.graph.descendants v)
          (β := fun d : V => bn.stateSpace d)).symm (xD, xND) u
          = xD ⟨u, hu⟩ := by
              simp [Equiv.piEquivPiSubtypeProd, hu]
      _ =
        patchConfig bn
          (baseFromNonDesc (bn := bn) v xND)
          (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
          (descSetToFin (bn := bn) v xD) u := by
            simpa [patchConfig_inside (bn := bn)
              (x := baseFromNonDesc (bn := bn) v xND)
              (D := Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
              (xD := descSetToFin (bn := bn) v xD)
              (v := u) hDmem, descSetToFin]
  · have hDnot : u ∉ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v) := by
      intro hmem
      exact hu (Finset.mem_filter.mp hmem).2
    calc
      (Equiv.piEquivPiSubtypeProd (p := fun d : V => d ∈ bn.graph.descendants v)
          (β := fun d : V => bn.stateSpace d)).symm (xD, xND) u
          = xND ⟨u, hu⟩ := by
              simp [Equiv.piEquivPiSubtypeProd, hu]
      _ =
        patchConfig bn
          (baseFromNonDesc (bn := bn) v xND)
          (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
          (descSetToFin (bn := bn) v xD) u := by
            simp [patchConfig_outside (bn := bn)
              (x := baseFromNonDesc (bn := bn) v xND)
              (D := Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
              (xD := descSetToFin (bn := bn) v xD)
              (v := u) hDnot, baseFromNonDesc, hu]

private lemma sum_reindex_desc_nonDesc
    (v : V) (f : bn.JointSpace → ENNReal) :
    (∑ x : bn.JointSpace, f x)
      =
    ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        f (mergeDescNonDesc (bn := bn) v xND xD) := by
  classical
  let e :
      bn.JointSpace ≃
        (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) ×
          (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) :=
    Equiv.piEquivPiSubtypeProd (p := fun d : V => d ∈ bn.graph.descendants v)
      (β := fun d : V => bn.stateSpace d)
  calc
    (∑ x : bn.JointSpace, f x)
        =
      ∑ p :
          (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) ×
            (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        f (e.symm p) := by
          refine Fintype.sum_equiv e f (fun p => f (e.symm p)) ?_
          intro x
          simpa [e] using congrArg f ((Equiv.symm_apply_apply e x).symm)
    _ =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          f (e.symm (xD, xND)) := by
            simpa using
              (Fintype.sum_prod_type
                (f := fun p :
                    (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d) ×
                      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) =>
                  f (e.symm p)))
    _ =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          f (mergeDescNonDesc (bn := bn) v xND xD) := by
            refine Finset.sum_congr rfl ?_
            intro xD _
            refine Finset.sum_congr rfl ?_
            intro xND _
            simpa [e] using congrArg f
              (piEquiv_descendants_symm_eq_merge (bn := bn) (v := v) (xD := xD) (xND := xND))

private lemma sum_descendants_jointWeight_over_nonDesc
    (cpt : bn.DiscreteCPT) (v : V)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) :
    (∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD))
      =
    cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
      (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
        cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w) := by
  classical
  have hD_desc :
      ∀ d, d ∈ (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)) →
        d ∈ bn.graph.descendants v := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  calc
    (∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD))
        =
      ∑ xD : (∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)), bn.stateSpace d),
        cpt.jointWeight
          (patchConfig bn
            (baseFromNonDesc (bn := bn) v xND)
            (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
            xD) := by
              calc
                (∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
                    cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD))
                    =
                  ∑ xD :
                      (∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
                        bn.stateSpace d),
                    cpt.jointWeight
                      (mergeDescNonDesc (bn := bn) v xND
                        ((descAssignEquiv (bn := bn) v).symm xD)) := by
                          refine Fintype.sum_equiv (descAssignEquiv (bn := bn) v)
                            (fun xD =>
                              cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD))
                            (fun xD =>
                              cpt.jointWeight
                                (mergeDescNonDesc (bn := bn) v xND
                                  ((descAssignEquiv (bn := bn) v).symm xD))) ?_
                          intro xD
                          rfl
                _ =
                  ∑ xD :
                      (∀ d : ↥(Finset.univ.filter (fun d => d ∈ bn.graph.descendants v)),
                        bn.stateSpace d),
                    cpt.jointWeight
                      (patchConfig bn
                        (baseFromNonDesc (bn := bn) v xND)
                        (Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
                        xD) := by
                          refine Finset.sum_congr rfl ?_
                          intro xD _
                          have hround :
                              descSetToFin (bn := bn) v ((descAssignEquiv (bn := bn) v).symm xD)
                                = xD := by
                            exact
                              (Equiv.apply_symm_apply (descAssignEquiv (bn := bn) v) xD)
                          simpa [mergeDescNonDesc, hround]
    _ =
      cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w) := by
            simpa using
              (sum_descendants_jointWeight (bn := bn) (cpt := cpt) (v := v)
                (x := baseFromNonDesc (bn := bn) v xND)
                (D := Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
                hD_desc rfl)

private lemma sum_jointWeight_reindex_and_collapse
    (cpt : bn.DiscreteCPT) (v : V) :
    (∑ x : bn.JointSpace, cpt.jointWeight x)
      =
    ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
      cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w) := by
  classical
  calc
    (∑ x : bn.JointSpace, cpt.jointWeight x)
        =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) := by
            exact sum_reindex_desc_nonDesc (bn := bn) (v := v) (f := cpt.jointWeight)
    _ =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
          cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) := by
            simpa using
              (Finset.sum_comm
                (f := fun xD
                    (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n)) =>
                  cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD)))
    _ =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
          (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w) := by
              refine Finset.sum_congr rfl ?_
              intro xND _
              exact sum_descendants_jointWeight_over_nonDesc (bn := bn) (cpt := cpt)
                (v := v) xND

private lemma sum_descendants_jointWeight_over_nonDesc_if
    (cpt : bn.DiscreteCPT) (v : V)
    (xND : ∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n)
    (P : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop) :
    (∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        (if P xND then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0))
      =
    if P xND then
      cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w)
    else 0 := by
  by_cases hP : P xND
  · simp [hP, sum_descendants_jointWeight_over_nonDesc]
  · simp [hP]

private lemma sum_jointWeight_reindex_and_collapse_of_desc_irrel
    (cpt : bn.DiscreteCPT) (v : V)
    (Q : bn.JointSpace → Prop)
    (P : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop)
    (hQP :
      ∀ xND xD,
        Q (mergeDescNonDesc (bn := bn) v xND xD) ↔ P xND) :
    (∑ x : bn.JointSpace, if Q x then cpt.jointWeight x else 0)
      =
    ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
      if P xND then
        cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
          (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
            cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w)
      else 0 := by
  classical
  calc
    (∑ x : bn.JointSpace, if Q x then cpt.jointWeight x else 0)
        =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          (if Q (mergeDescNonDesc (bn := bn) v xND xD)
            then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0) := by
            exact sum_reindex_desc_nonDesc (bn := bn) (v := v)
              (f := fun x => if Q x then cpt.jointWeight x else 0)
    _ =
      ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
        ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
          (if P xND
            then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro xD _
            refine Finset.sum_congr rfl ?_
            intro xND _
            by_cases hP : P xND
            · have hQ : Q (mergeDescNonDesc (bn := bn) v xND xD) := (hQP xND xD).2 hP
              simp [hP, hQ]
            · have hQ : ¬ Q (mergeDescNonDesc (bn := bn) v xND xD) := by
                intro hQ
                exact hP ((hQP xND xD).1 hQ)
              simp [hP, hQ]
    _ =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        ∑ xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d),
          (if P xND
            then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0) := by
            simpa using
              (Finset.sum_comm
                (f := fun xD
                    (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n)) =>
                  if P xND then cpt.jointWeight (mergeDescNonDesc (bn := bn) v xND xD) else 0))
    _ =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P xND then
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
            (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
              cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w)
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro xND _
          simpa using
            (sum_descendants_jointWeight_over_nonDesc_if (bn := bn) (cpt := cpt) (v := v)
              (xND := xND) (P := P))

/-- Per-parent-fiber screening identity used in `condExp_indicator_mul_of_bn_ci`.
This is the discrete BN algebraic core:
`μ((B ∩ t₂) ∩ F_c) * μ(F_c) = μ(B ∩ F_c) * μ(t₂ ∩ F_c)`.
-/
private lemma fiber_screening_mul
    (cpt : bn.DiscreteCPT) (v : V)
    (B : Set bn.JointSpace)
    (hB : MeasurableSet[bn.measurableSpaceOfVertices ({v} : Set V)] B)
    (t₂ : Set bn.JointSpace)
    (ht₂ : MeasurableSet[bn.measurableSpaceOfVertices
            (bn.nonDescendantsExceptParentsAndSelf v)] t₂)
    (c : ParentAssign (bn := bn) v) :
    cpt.jointMeasure (((B ∩ t₂)) ∩ parentFiber (bn := bn) v c) *
      cpt.jointMeasure (parentFiber (bn := bn) v c)
      =
      cpt.jointMeasure (B ∩ parentFiber (bn := bn) v c) *
      cpt.jointMeasure (t₂ ∩ parentFiber (bn := bn) v c) := by
  -- Reduce measurable sets to finite coordinate-restriction preimages.
  rcases measurableSet_singleton_preimage (bn := bn) (v := v) (s := B) hB with
    ⟨SB, hSB, hBpre⟩
  rcases measurableSet_vertices_preimage (bn := bn)
    (S := bn.nonDescendantsExceptParentsAndSelf v) (s := t₂) ht₂ with
    ⟨SND, hSND, ht₂pre⟩
  subst hBpre
  subst ht₂pre
  let F : Set bn.JointSpace := parentFiber (bn := bn) v c
  have hB_pi : @MeasurableSet _ MeasurableSpace.pi ((fun ω : bn.JointSpace => ω v) ⁻¹' SB) := by
    exact (measurable_pi_apply v) hSB
  have hRestr_meas : Measurable (restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) := by
    have hle :
        MeasurableSpace.comap
          (restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v))
          (by infer_instance)
          ≤ (MeasurableSpace.pi : MeasurableSpace bn.JointSpace) := by
      simpa [measurableSpaceOfVertices_eq_comap_restrict (bn := bn)
        (bn.nonDescendantsExceptParentsAndSelf v)] using
        (bn.measurableSpaceOfVertices_le (bn.nonDescendantsExceptParentsAndSelf v))
    exact Measurable.of_comap_le hle
  have ht₂_pi :
      @MeasurableSet _ MeasurableSpace.pi
        ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND) := by
    exact hRestr_meas hSND
  have hBt₂_pi :
      @MeasurableSet _ MeasurableSpace.pi
        (((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩
         ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)) := by
    exact hB_pi.inter ht₂_pi
  have hμ_BtF :
      cpt.jointMeasure ((((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩
        ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)) ∩ F) =
      ∑ x : bn.JointSpace,
        if x ∈ ((((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩
          ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)) ∩ F)
        then cpt.jointWeight x else 0 := by
    simpa [F] using
      (jointMeasure_parentFiber_inter_as_sum (bn := bn) (cpt := cpt) (v := v) (c := c)
        (S := (((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩
          ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)))
        hBt₂_pi)
  have hμ_BF :
      cpt.jointMeasure (((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩ F) =
      ∑ x : bn.JointSpace,
        if x ∈ (((fun ω : bn.JointSpace => ω v) ⁻¹' SB) ∩ F) then cpt.jointWeight x else 0 := by
    simpa [F] using
      (jointMeasure_parentFiber_inter_as_sum (bn := bn) (cpt := cpt) (v := v) (c := c)
        (S := ((fun ω : bn.JointSpace => ω v) ⁻¹' SB)) hB_pi)
  have hμ_t₂F :
      cpt.jointMeasure
        (((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND) ∩ F) =
      ∑ x : bn.JointSpace,
        if x ∈ (((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND) ∩ F)
        then cpt.jointWeight x else 0 := by
    simpa [F] using
      (jointMeasure_parentFiber_inter_as_sum (bn := bn) (cpt := cpt) (v := v) (c := c)
        (S := ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND))
        ht₂_pi)
  have hμ_F :
      cpt.jointMeasure F =
      ∑ x : bn.JointSpace, if x ∈ F then cpt.jointWeight x else 0 := by
    simpa [F] using
      (jointMeasure_parentFiber_inter_as_sum (bn := bn) (cpt := cpt) (v := v) (c := c)
        (S := (Set.univ : Set bn.JointSpace)) MeasurableSet.univ)
  let Bset : Set bn.JointSpace := ((fun ω : bn.JointSpace => ω v) ⁻¹' SB)
  let Tset : Set bn.JointSpace :=
    ((restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)) ⁻¹' SND)
  let S_BtF : Set bn.JointSpace := (Bset ∩ Tset) ∩ F
  let S_BF : Set bn.JointSpace := Bset ∩ F
  let S_t₂F : Set bn.JointSpace := Tset ∩ F
  let P_BtF :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop :=
    fun xND => baseFromNonDesc (bn := bn) v xND ∈ S_BtF
  let P_BF :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop :=
    fun xND => baseFromNonDesc (bn := bn) v xND ∈ S_BF
  let P_t₂F :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop :=
    fun xND => baseFromNonDesc (bn := bn) v xND ∈ S_t₂F
  let P_F :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → Prop :=
    fun xND => baseFromNonDesc (bn := bn) v xND ∈ F
  let A :
      (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n) → ENNReal :=
    fun xND =>
      cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) v *
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (baseFromNonDesc (bn := bn) v xND) w)
  have hv_not_desc : v ∉ bn.graph.descendants v := by
    intro hv
    rcases hv with ⟨_, hv_ne⟩
    exact hv_ne rfl
  have hmerge_eq_base_of_not_desc :
      ∀ (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n))
        (xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d))
        (u : V),
        u ∉ bn.graph.descendants v →
          mergeDescNonDesc (bn := bn) v xND xD u = baseFromNonDesc (bn := bn) v xND u := by
    intro xND xD u hu
    have hu_not_memD : u ∉ Finset.univ.filter (fun d => d ∈ bn.graph.descendants v) := by
      intro huD
      exact hu ((Finset.mem_filter.mp huD).2)
    simpa [mergeDescNonDesc] using
      (patchConfig_outside (bn := bn)
        (x := baseFromNonDesc (bn := bn) v xND)
        (D := Finset.univ.filter (fun d => d ∈ bn.graph.descendants v))
        (xD := descSetToFin (bn := bn) v xD)
        (v := u) hu_not_memD)
  have hmerge_eq_base_at_v :
      ∀ (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n))
        (xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d)),
        mergeDescNonDesc (bn := bn) v xND xD v = baseFromNonDesc (bn := bn) v xND v := by
    intro xND xD
    exact hmerge_eq_base_of_not_desc xND xD v hv_not_desc
  have hmerge_eq_base_on_restrictND :
      ∀ (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n))
        (xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d)),
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)
          (mergeDescNonDesc (bn := bn) v xND xD)
          =
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)
          (baseFromNonDesc (bn := bn) v xND) := by
    intro xND xD
    funext u
    have hu_not_desc : u.1 ∉ bn.graph.descendants v := by
      have hu_mem : u.1 ∈ bn.nonDescendantsExceptParentsAndSelf v := u.2
      have hu_mem' :
          u.1 ∉ bn.graph.descendants v ∧ u.1 ∉ bn.graph.parents v ∪ ({v} : Set V) := by
        simpa [BayesianNetwork.nonDescendantsExceptParentsAndSelf, Set.mem_diff] using hu_mem
      exact hu_mem'.1
    exact hmerge_eq_base_of_not_desc xND xD u.1 hu_not_desc
  have hmerge_eq_base_on_parents :
      ∀ (xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n))
        (xD : (∀ d : {d // d ∈ bn.graph.descendants v}, bn.stateSpace d)),
        parentsRestrict (bn := bn) v (mergeDescNonDesc (bn := bn) v xND xD)
          =
        parentsRestrict (bn := bn) v (baseFromNonDesc (bn := bn) v xND) := by
    intro xND xD
    funext p
    have hp_not_desc : p.1 ∉ bn.graph.descendants v := by
      intro hp_desc
      exact (descendant_not_parent (bn := bn) (v := v) (d := p.1) hp_desc) p.2
    exact hmerge_eq_base_of_not_desc xND xD p.1 hp_not_desc
  have hQP_BtF :
      ∀ xND xD,
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ S_BtF) ↔ P_BtF xND := by
    intro xND xD
    have hB :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ Bset) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ Bset) := by
      simpa [Bset, hmerge_eq_base_at_v xND xD]
    have hT :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ Tset) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ Tset) := by
      simpa [Tset, hmerge_eq_base_on_restrictND xND xD]
    have hFm :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ F) := by
      simpa [F, parentFiber, hmerge_eq_base_on_parents xND xD]
    simpa [P_BtF, S_BtF, Set.mem_inter_iff, hB, hT, hFm]
  have hQP_BF :
      ∀ xND xD,
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ S_BF) ↔ P_BF xND := by
    intro xND xD
    have hB :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ Bset) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ Bset) := by
      simpa [Bset, hmerge_eq_base_at_v xND xD]
    have hFm :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ F) := by
      simpa [F, parentFiber, hmerge_eq_base_on_parents xND xD]
    simpa [P_BF, S_BF, Set.mem_inter_iff, hB, hFm]
  have hQP_t₂F :
      ∀ xND xD,
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ S_t₂F) ↔ P_t₂F xND := by
    intro xND xD
    have hT :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ Tset) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ Tset) := by
      simpa [Tset, hmerge_eq_base_on_restrictND xND xD]
    have hFm :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ F) := by
      simpa [F, parentFiber, hmerge_eq_base_on_parents xND xD]
    simpa [P_t₂F, S_t₂F, Set.mem_inter_iff, hT, hFm]
  have hQP_F :
      ∀ xND xD,
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔ P_F xND := by
    intro xND xD
    have hFm :
        ((mergeDescNonDesc (bn := bn) v xND xD) ∈ F) ↔
          ((baseFromNonDesc (bn := bn) v xND) ∈ F) := by
      simpa [F, parentFiber, hmerge_eq_base_on_parents xND xD]
    simpa [P_F] using hFm
  have hsum_BtF :
      (∑ x : bn.JointSpace, if x ∈ S_BtF then cpt.jointWeight x else 0)
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_BtF xND then A xND else 0 := by
    classical
    convert
      (sum_jointWeight_reindex_and_collapse_of_desc_irrel
        (bn := bn) (cpt := cpt) (v := v)
        (Q := fun x => x ∈ S_BtF) (P := P_BtF) hQP_BtF) using 1
    · refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x ∈ S_BtF <;> simp [h]
    · simp [A]
  have hsum_BF :
      (∑ x : bn.JointSpace, if x ∈ S_BF then cpt.jointWeight x else 0)
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_BF xND then A xND else 0 := by
    classical
    convert
      (sum_jointWeight_reindex_and_collapse_of_desc_irrel
        (bn := bn) (cpt := cpt) (v := v)
        (Q := fun x => x ∈ S_BF) (P := P_BF) hQP_BF) using 1
    · refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x ∈ S_BF <;> simp [h]
    · simp [A]
  have hsum_t₂F :
      (∑ x : bn.JointSpace, if x ∈ S_t₂F then cpt.jointWeight x else 0)
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_t₂F xND then A xND else 0 := by
    classical
    convert
      (sum_jointWeight_reindex_and_collapse_of_desc_irrel
        (bn := bn) (cpt := cpt) (v := v)
        (Q := fun x => x ∈ S_t₂F) (P := P_t₂F) hQP_t₂F) using 1
    · refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x ∈ S_t₂F <;> simp [h]
    · simp [A]
  have hsum_F :
      (∑ x : bn.JointSpace, if x ∈ F then cpt.jointWeight x else 0)
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_F xND then A xND else 0 := by
    simpa [A] using
      (sum_jointWeight_reindex_and_collapse_of_desc_irrel
        (bn := bn) (cpt := cpt) (v := v)
        (Q := fun x => x ∈ F) (P := P_F) hQP_F)
  have hμ_BtF_ND :
      cpt.jointMeasure S_BtF
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_BtF xND then A xND else 0 := by
    calc
      cpt.jointMeasure S_BtF
          = ∑ x : bn.JointSpace, if x ∈ S_BtF then cpt.jointWeight x else 0 := by
              simpa [S_BtF, Bset, Tset, Set.inter_assoc] using hμ_BtF
      _ = ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
            if P_BtF xND then A xND else 0 := hsum_BtF
  have hμ_BF_ND :
      cpt.jointMeasure S_BF
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_BF xND then A xND else 0 := by
    calc
      cpt.jointMeasure S_BF
          = ∑ x : bn.JointSpace, if x ∈ S_BF then cpt.jointWeight x else 0 := by
              simpa [S_BF, Bset] using hμ_BF
      _ = ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
            if P_BF xND then A xND else 0 := hsum_BF
  have hμ_t₂F_ND :
      cpt.jointMeasure S_t₂F
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_t₂F xND then A xND else 0 := by
    calc
      cpt.jointMeasure S_t₂F
          = ∑ x : bn.JointSpace, if x ∈ S_t₂F then cpt.jointWeight x else 0 := by
              simpa [S_t₂F, Tset] using hμ_t₂F
      _ = ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
            if P_t₂F xND then A xND else 0 := hsum_t₂F
  have hμ_F_ND :
      cpt.jointMeasure F
        =
      ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
        if P_F xND then A xND else 0 := by
    calc
      cpt.jointMeasure F
          = ∑ x : bn.JointSpace, if x ∈ F then cpt.jointWeight x else 0 := hμ_F
      _ = ∑ xND : (∀ n : {n // n ∉ bn.graph.descendants v}, bn.stateSpace n),
            if P_F xND then A xND else 0 := hsum_F
  let NDIdx := {n // n ∉ bn.graph.descendants v}
  let xvIdx : NDIdx := ⟨v, hv_not_desc⟩
  let XRest := (∀ n : {n : NDIdx // n ≠ xvIdx}, bn.stateSpace n.1.1)
  let eND :
      (∀ n : NDIdx, bn.stateSpace n.1) ≃ (bn.stateSpace v × XRest) :=
    Equiv.piSplitAt xvIdx (fun n : NDIdx => bn.stateSpace n.1)
  have hsum_split_xND :
      ∀ f : (∀ n : NDIdx, bn.stateSpace n.1) → ENNReal,
        (∑ xND : (∀ n : NDIdx, bn.stateSpace n.1), f xND)
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            f (eND.symm (a, xrest)) := by
    intro f
    classical
    calc
      (∑ xND : (∀ n : NDIdx, bn.stateSpace n.1), f xND)
          =
        ∑ p : bn.stateSpace v × XRest, f (eND.symm p) := by
          refine Fintype.sum_equiv eND f (fun p => f (eND.symm p)) ?_
          intro xND
          simp
      _ =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest, f (eND.symm (a, xrest)) := by
            simpa using
              (Fintype.sum_prod_type
                (f := fun p : bn.stateSpace v × XRest => f (eND.symm p)))
  have hμ_BtF_split :
      cpt.jointMeasure S_BtF
        =
      ∑ a : bn.stateSpace v,
        ∑ xrest : XRest,
          if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    rw [hμ_BtF_ND]
    simpa using
      (hsum_split_xND
        (f := fun xND : (∀ n : NDIdx, bn.stateSpace n.1) =>
          if P_BtF xND then A xND else 0))
  have hμ_BF_split :
      cpt.jointMeasure S_BF
        =
      ∑ a : bn.stateSpace v,
        ∑ xrest : XRest,
          if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    rw [hμ_BF_ND]
    simpa using
      (hsum_split_xND
        (f := fun xND : (∀ n : NDIdx, bn.stateSpace n.1) =>
          if P_BF xND then A xND else 0))
  have hμ_t₂F_split :
      cpt.jointMeasure S_t₂F
        =
      ∑ a : bn.stateSpace v,
        ∑ xrest : XRest,
          if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    rw [hμ_t₂F_ND]
    simpa using
      (hsum_split_xND
        (f := fun xND : (∀ n : NDIdx, bn.stateSpace n.1) =>
          if P_t₂F xND then A xND else 0))
  have hμ_F_split :
      cpt.jointMeasure F
        =
      ∑ a : bn.stateSpace v,
        ∑ xrest : XRest,
          if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    rw [hμ_F_ND]
    simpa using
      (hsum_split_xND
        (f := fun xND : (∀ n : NDIdx, bn.stateSpace n.1) =>
          if P_F xND then A xND else 0))
  let paC : bn.ParentAssignment v := fun u hu => c ⟨u, hu⟩
  let qB : ENNReal := ∑ a : bn.stateSpace v, if a ∈ SB then cpt.cpt v paC a else 0
  let a0 : bn.stateSpace v := Classical.choice (inferInstance : Nonempty (bn.stateSpace v))
  let xND0 : XRest → (∀ n : NDIdx, bn.stateSpace n.1) := fun xrest => eND.symm (a0, xrest)
  let x0 : XRest → bn.JointSpace := fun xrest => baseFromNonDesc (bn := bn) v (xND0 xrest)
  let R : XRest → ENNReal := fun xrest =>
    ∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
      cpt.nodeProb (x0 xrest) w
  let PF0 : XRest → Prop := fun xrest => P_F (xND0 xrest)
  let PT0 : XRest → Prop := fun xrest => P_t₂F (xND0 xrest)

  have hparents_update_v :
      ∀ (x : bn.JointSpace) (a : bn.stateSpace v),
        parentsRestrict (bn := bn) v (Function.update x v a)
          =
        parentsRestrict (bn := bn) v x := by
    intro x a
    funext p
    have hp_ne : p.1 ≠ v := by
      intro hp
      exact not_self_parent (bn := bn) v (by simpa [hp] using p.2)
    simp [parentsRestrict, restrictToSet, Function.update_of_ne hp_ne]

  have hv_not_ND : v ∉ bn.nonDescendantsExceptParentsAndSelf v := by
    intro hv_mem
    have hv_mem' :
        v ∉ bn.graph.descendants v ∧ v ∉ bn.graph.parents v ∪ ({v} : Set V) := by
      simpa [BayesianNetwork.nonDescendantsExceptParentsAndSelf, Set.mem_diff] using hv_mem
    exact hv_mem'.2 (Set.mem_union_right _ rfl)

  have hrestrictND_update :
      ∀ (x : bn.JointSpace) (a : bn.stateSpace v),
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v) (Function.update x v a)
          =
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v) x := by
    intro x a
    funext u
    have hu_ne : u.1 ≠ v := by
      intro hu
      apply hv_not_ND
      simpa [hu] using u.2
    simp [restrictToSet, Function.update_of_ne hu_ne]

  have hxND_update :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        eND.symm (a, xrest) = Function.update (xND0 xrest) xvIdx a := by
    intro a xrest
    funext n
    by_cases hn : n = xvIdx
    · subst hn
      have hpair : eND (eND.symm (a, xrest)) = (a, xrest) :=
        Equiv.apply_symm_apply eND (a, xrest)
      have hfst : (eND (eND.symm (a, xrest))).1 = a := congrArg Prod.fst hpair
      simpa [eND] using hfst
    · have h1 : (eND.symm (a, xrest)) n = xrest ⟨n, hn⟩ := by
        have hpair : eND (eND.symm (a, xrest)) = (a, xrest) :=
          Equiv.apply_symm_apply eND (a, xrest)
        have hsnd :
            (eND (eND.symm (a, xrest))).2 ⟨n, hn⟩ = xrest ⟨n, hn⟩ :=
          congrArg (fun g => g ⟨n, hn⟩) (congrArg Prod.snd hpair)
        simpa [eND] using hsnd
      have h2 : (xND0 xrest) n = xrest ⟨n, hn⟩ := by
        have hpair : eND (eND.symm (a0, xrest)) = (a0, xrest) :=
          Equiv.apply_symm_apply eND (a0, xrest)
        have hsnd :
            (eND (eND.symm (a0, xrest))).2 ⟨n, hn⟩ = xrest ⟨n, hn⟩ :=
          congrArg (fun g => g ⟨n, hn⟩) (congrArg Prod.snd hpair)
        simpa [xND0, eND] using hsnd
      simp [Function.update_of_ne hn, h1, h2]

  have hbase_update :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))
          =
        Function.update (x0 xrest) v a := by
    intro a xrest
    funext u
    by_cases hu_desc : u ∈ bn.graph.descendants v
    · have huv_ne : u ≠ v := by
        intro huv
        subst huv
        exact hv_not_desc hu_desc
      simp [baseFromNonDesc, x0, xND0, hu_desc, Function.update_of_ne huv_ne]
    · have hu_not_desc : u ∉ bn.graph.descendants v := hu_desc
      by_cases huv : u = v
      · subst huv
        have hxv : (eND.symm (a, xrest)) xvIdx = a := by
          simpa [Function.update_self] using
            congrArg (fun f => f xvIdx) (hxND_update a xrest)
        simpa [baseFromNonDesc, x0, xND0, hv_not_desc, xvIdx]
          using hxv
      · have hidx_ne : (⟨u, hu_not_desc⟩ : NDIdx) ≠ xvIdx := by
          intro h
          apply huv
          exact congrArg Subtype.val h
        have hx :
            (eND.symm (a, xrest)) ⟨u, hu_not_desc⟩
              =
            (xND0 xrest) ⟨u, hu_not_desc⟩ := by
          have hx' := congrArg (fun f => f ⟨u, hu_not_desc⟩) (hxND_update a xrest)
          simp [Function.update_of_ne hidx_ne] at hx'
          exact hx'
        have hx0 :
            (x0 xrest) u = (xND0 xrest) ⟨u, hu_not_desc⟩ := by
          simp [x0, baseFromNonDesc, hu_not_desc]
        simp [baseFromNonDesc, hu_not_desc, Function.update_of_ne huv, hx, hx0]

  have hP_F_indep :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        P_F (eND.symm (a, xrest)) ↔ PF0 xrest := by
    intro a xrest
    constructor
    · intro h
      have hpar_upd :
          parentsRestrict (bn := bn) v (Function.update (x0 xrest) v a) = c := by
        simpa [hbase_update a xrest, F, parentFiber, P_F] using h
      have hpar0 :
          parentsRestrict (bn := bn) v (x0 xrest) = c := by
        simpa [hparents_update_v (x := x0 xrest) (a := a)] using hpar_upd
      simpa [PF0, P_F, x0, xND0, F, parentFiber]
        using hpar0
    · intro h
      have hpar0 :
          parentsRestrict (bn := bn) v (x0 xrest) = c := by
        simpa [PF0, P_F, x0, xND0, F, parentFiber] using h
      have hpar_upd :
          parentsRestrict (bn := bn) v (Function.update (x0 xrest) v a) = c := by
        simpa [hparents_update_v (x := x0 xrest) (a := a)] using hpar0
      simpa [hbase_update a xrest, F, parentFiber, P_F] using hpar_upd

  have hP_t₂F_implies_P_F :
      ∀ xND, P_t₂F xND → P_F xND := by
    intro xND h
    have hmem : baseFromNonDesc (bn := bn) v xND ∈ S_t₂F := by
      simpa [P_t₂F] using h
    exact hmem.2

  have hP_t₂F_indep :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        P_t₂F (eND.symm (a, xrest)) ↔ PT0 xrest := by
    intro a xrest
    let xnew : bn.JointSpace := baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))
    have hT_indep : xnew ∈ Tset ↔ x0 xrest ∈ Tset := by
      dsimp [xnew, Tset]
      change
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v)
          (baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))) ∈ SND
          ↔
        restrictToSet (bn := bn) (bn.nonDescendantsExceptParentsAndSelf v) (x0 xrest) ∈ SND
      rw [hbase_update a xrest]
      simpa [hrestrictND_update (x := x0 xrest) (a := a)]
    have hF_indep : xnew ∈ F ↔ x0 xrest ∈ F := by
      simpa [xnew, PF0, P_F, x0, xND0] using hP_F_indep a xrest
    have hS : xnew ∈ S_t₂F ↔ x0 xrest ∈ S_t₂F := by
      simpa [S_t₂F, Set.mem_inter_iff, hT_indep, hF_indep]
    simpa [P_t₂F, PT0, xnew, xND0] using hS

  have hP_BF_split :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        P_BF (eND.symm (a, xrest)) ↔ (a ∈ SB ∧ PF0 xrest) := by
    intro a xrest
    let xnew : bn.JointSpace := baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))
    have hB_mem : xnew ∈ Bset ↔ a ∈ SB := by
      dsimp [xnew, Bset]
      rw [hbase_update a xrest]
      simp
    have hF_mem : xnew ∈ F ↔ PF0 xrest := by
      simpa [xnew, P_F] using hP_F_indep a xrest
    simpa [P_BF, xnew, S_BF, Set.mem_inter_iff, hB_mem, hF_mem]

  have hP_BtF_split :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        P_BtF (eND.symm (a, xrest)) ↔ (a ∈ SB ∧ PT0 xrest) := by
    intro a xrest
    let xnew : bn.JointSpace := baseFromNonDesc (bn := bn) v (eND.symm (a, xrest))
    have hB_mem : xnew ∈ Bset ↔ a ∈ SB := by
      dsimp [xnew, Bset]
      rw [hbase_update a xrest]
      simp
    have hT2_mem : xnew ∈ S_t₂F ↔ PT0 xrest := by
      simpa [xnew, P_t₂F] using hP_t₂F_indep a xrest
    have hTF : xnew ∈ Tset ∩ F ↔ PT0 xrest := by
      simpa [S_t₂F, Set.mem_inter_iff] using hT2_mem
    have hBt : xnew ∈ S_BtF ↔ (a ∈ SB ∧ PT0 xrest) := by
      constructor
      · intro hx
        have hxB : xnew ∈ Bset := hx.1.1
        have hxTF : xnew ∈ Tset ∩ F := ⟨hx.1.2, hx.2⟩
        exact ⟨hB_mem.mp hxB, hTF.mp hxTF⟩
      · intro h
        rcases h with ⟨ha, hpt⟩
        have hxB : xnew ∈ Bset := hB_mem.mpr ha
        have hxTF : xnew ∈ Tset ∩ F := hTF.mpr hpt
        exact ⟨⟨hxB, hxTF.1⟩, hxTF.2⟩
    simpa [P_BtF, xnew] using hBt

  have hnodeProb_eq_cpt :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        PF0 xrest →
          cpt.nodeProb (Function.update (x0 xrest) v a) v = cpt.cpt v paC a := by
    intro a xrest hPF
    have hpar0 : parentsRestrict (bn := bn) v (x0 xrest) = c := by
      simpa [PF0, P_F, x0, xND0, F, parentFiber] using hPF
    have hpar_upd : parentsRestrict (bn := bn) v (Function.update (x0 xrest) v a) = c := by
      simpa [hparents_update_v (x := x0 xrest) (a := a)] using hpar0
    have hpa_cfg : cpt.parentAssignOfConfig (Function.update (x0 xrest) v a) v = paC := by
      funext u hu
      have hcomp := congrArg (fun p => p ⟨u, hu⟩) hpar_upd
      simpa [parentsRestrict, restrictToSet, DiscreteCPT.parentAssignOfConfig, paC] using hcomp
    calc
      cpt.nodeProb (Function.update (x0 xrest) v a) v
          = cpt.cpt v (cpt.parentAssignOfConfig (Function.update (x0 xrest) v a) v)
              ((Function.update (x0 xrest) v a) v) := rfl
      _ = cpt.cpt v paC a := by simp [hpa_cfg, paC]

  have hA_decomp :
      ∀ (a : bn.stateSpace v) (xrest : XRest),
        A (eND.symm (a, xrest))
          =
        cpt.nodeProb (Function.update (x0 xrest) v a) v * R xrest := by
    intro a xrest
    have hprod :
        (∏ w ∈ (Finset.univ.filter (fun w => w ∉ bn.graph.descendants v ∧ w ≠ v)),
          cpt.nodeProb (Function.update (x0 xrest) v a) w)
          =
        R xrest := by
      simpa [R] using
        (prod_notDescNotSelf_independent_of_xv (bn := bn) (cpt := cpt)
          (v := v) (x := x0 xrest) (a := a))
    simp [A, x0, hprod, hbase_update a xrest]

  have hsum_cpt_row : ∑ a : bn.stateSpace v, cpt.cpt v paC a = 1 := by
    simpa using pmf_sum_eq_one (cpt.cpt v paC)

  have hμ_BtF_split' :
      cpt.jointMeasure S_BtF
        =
      ∑ xrest : XRest,
        ∑ a : bn.stateSpace v,
          if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    calc
      cpt.jointMeasure S_BtF
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_BtF_split
      _ =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
              simpa using
                (Finset.sum_comm
                  (f := fun a : bn.stateSpace v =>
                    fun xrest : XRest =>
                      if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0))

  have hμ_BF_split' :
      cpt.jointMeasure S_BF
        =
      ∑ xrest : XRest,
        ∑ a : bn.stateSpace v,
          if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    calc
      cpt.jointMeasure S_BF
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_BF_split
      _ =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
              simpa using
                (Finset.sum_comm
                  (f := fun a : bn.stateSpace v =>
                    fun xrest : XRest =>
                      if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0))

  have hμ_t₂F_split' :
      cpt.jointMeasure S_t₂F
        =
      ∑ xrest : XRest,
        ∑ a : bn.stateSpace v,
          if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    calc
      cpt.jointMeasure S_t₂F
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_t₂F_split
      _ =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
              simpa using
                (Finset.sum_comm
                  (f := fun a : bn.stateSpace v =>
                    fun xrest : XRest =>
                      if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0))

  have hμ_F_split' :
      cpt.jointMeasure F
        =
      ∑ xrest : XRest,
        ∑ a : bn.stateSpace v,
          if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
    calc
      cpt.jointMeasure F
          =
        ∑ a : bn.stateSpace v,
          ∑ xrest : XRest,
            if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_F_split
      _ =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := by
              simpa using
                (Finset.sum_comm
                  (f := fun a : bn.stateSpace v =>
                    fun xrest : XRest =>
                      if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0))

  have hInner_F :
      ∀ xrest : XRest,
        (∑ a : bn.stateSpace v,
          if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
          =
        if PF0 xrest then R xrest else 0 := by
    intro xrest
    by_cases hPF : PF0 xrest
    · have hPFa : ∀ a : bn.stateSpace v, P_F (eND.symm (a, xrest)) := by
        intro a
        exact (hP_F_indep a xrest).2 hPF
      calc
        (∑ a : bn.stateSpace v,
          if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
            = ∑ a : bn.stateSpace v, A (eND.symm (a, xrest)) := by
                simp [hPFa]
        _ = ∑ a : bn.stateSpace v,
              cpt.nodeProb (Function.update (x0 xrest) v a) v * R xrest := by
                refine Finset.sum_congr rfl ?_
                intro a _
                simpa using hA_decomp a xrest
        _ = (∑ a : bn.stateSpace v, cpt.nodeProb (Function.update (x0 xrest) v a) v) * R xrest := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (bn.stateSpace v)))
                  (f := fun a : bn.stateSpace v =>
                    cpt.nodeProb (Function.update (x0 xrest) v a) v)
                  (a := R xrest)).symm
        _ = (∑ a : bn.stateSpace v, cpt.cpt v paC a) * R xrest := by
              refine congrArg (fun z => z * R xrest) ?_
              refine Finset.sum_congr rfl ?_
              intro a _
              exact hnodeProb_eq_cpt a xrest hPF
        _ = R xrest := by simp [hsum_cpt_row]
        _ = if PF0 xrest then R xrest else 0 := by simp [hPF]
    · have hPFa : ∀ a : bn.stateSpace v, ¬ P_F (eND.symm (a, xrest)) := by
        intro a h
        exact hPF ((hP_F_indep a xrest).1 h)
      simp [hPFa, hPF]

  have hInner_t₂F :
      ∀ xrest : XRest,
        (∑ a : bn.stateSpace v,
          if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
          =
        if PT0 xrest then R xrest else 0 := by
    intro xrest
    by_cases hPT : PT0 xrest
    · have hPF : PF0 xrest := by
        exact hP_t₂F_implies_P_F (xND := xND0 xrest) (by simpa [PT0] using hPT)
      have hPTa : ∀ a : bn.stateSpace v, P_t₂F (eND.symm (a, xrest)) := by
        intro a
        exact (hP_t₂F_indep a xrest).2 hPT
      calc
        (∑ a : bn.stateSpace v,
          if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
            = ∑ a : bn.stateSpace v, A (eND.symm (a, xrest)) := by
                simp [hPTa]
        _ = ∑ a : bn.stateSpace v,
              cpt.nodeProb (Function.update (x0 xrest) v a) v * R xrest := by
                refine Finset.sum_congr rfl ?_
                intro a _
                simpa using hA_decomp a xrest
        _ = (∑ a : bn.stateSpace v, cpt.nodeProb (Function.update (x0 xrest) v a) v) * R xrest := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (bn.stateSpace v)))
                  (f := fun a : bn.stateSpace v =>
                    cpt.nodeProb (Function.update (x0 xrest) v a) v)
                  (a := R xrest)).symm
        _ = (∑ a : bn.stateSpace v, cpt.cpt v paC a) * R xrest := by
              refine congrArg (fun z => z * R xrest) ?_
              refine Finset.sum_congr rfl ?_
              intro a _
              exact hnodeProb_eq_cpt a xrest hPF
        _ = R xrest := by simp [hsum_cpt_row]
        _ = if PT0 xrest then R xrest else 0 := by simp [hPT]
    · have hPTa : ∀ a : bn.stateSpace v, ¬ P_t₂F (eND.symm (a, xrest)) := by
        intro a h
        exact hPT ((hP_t₂F_indep a xrest).1 h)
      simp [hPTa, hPT]

  have hInner_BF :
      ∀ xrest : XRest,
        (∑ a : bn.stateSpace v,
          if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
          =
        if PF0 xrest then qB * R xrest else 0 := by
    intro xrest
    by_cases hPF : PF0 xrest
    · have hBFa :
          ∀ a : bn.stateSpace v,
            P_BF (eND.symm (a, xrest)) ↔ a ∈ SB := by
        intro a
        simpa [hPF, and_assoc] using hP_BF_split a xrest
      calc
        (∑ a : bn.stateSpace v,
          if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
            = ∑ a : bn.stateSpace v,
                if a ∈ SB then A (eND.symm (a, xrest)) else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  by_cases ha : a ∈ SB <;> simp [hBFa a, ha]
        _ = ∑ a : bn.stateSpace v,
              if a ∈ SB then cpt.cpt v paC a * R xrest else 0 := by
                refine Finset.sum_congr rfl ?_
                intro a _
                by_cases ha : a ∈ SB
                · simp [ha, hA_decomp a xrest, hnodeProb_eq_cpt a xrest hPF]
                · simp [ha]
        _ = (∑ a : bn.stateSpace v, if a ∈ SB then cpt.cpt v paC a else 0) * R xrest := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (bn.stateSpace v)))
                  (f := fun a : bn.stateSpace v => if a ∈ SB then cpt.cpt v paC a else 0)
                  (a := R xrest)).symm
        _ = qB * R xrest := by simp [qB]
        _ = if PF0 xrest then qB * R xrest else 0 := by simp [hPF]
    · have hBFa : ∀ a : bn.stateSpace v, ¬ P_BF (eND.symm (a, xrest)) := by
        intro a h
        exact hPF (hP_BF_split a xrest |>.1 h |>.2)
      simp [hBFa, hPF]

  have hInner_BtF :
      ∀ xrest : XRest,
        (∑ a : bn.stateSpace v,
          if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
          =
        if PT0 xrest then qB * R xrest else 0 := by
    intro xrest
    by_cases hPT : PT0 xrest
    · have hPF : PF0 xrest := by
        exact hP_t₂F_implies_P_F (xND := xND0 xrest) (by simpa [PT0] using hPT)
      have hBtFa :
          ∀ a : bn.stateSpace v,
            P_BtF (eND.symm (a, xrest)) ↔ a ∈ SB := by
        intro a
        simpa [hPT, and_assoc] using hP_BtF_split a xrest
      calc
        (∑ a : bn.stateSpace v,
          if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0)
            = ∑ a : bn.stateSpace v,
                if a ∈ SB then A (eND.symm (a, xrest)) else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  by_cases ha : a ∈ SB <;> simp [hBtFa a, ha]
        _ = ∑ a : bn.stateSpace v,
              if a ∈ SB then cpt.cpt v paC a * R xrest else 0 := by
                refine Finset.sum_congr rfl ?_
                intro a _
                by_cases ha : a ∈ SB
                · simp [ha, hA_decomp a xrest, hnodeProb_eq_cpt a xrest hPF]
                · simp [ha]
        _ = (∑ a : bn.stateSpace v, if a ∈ SB then cpt.cpt v paC a else 0) * R xrest := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (bn.stateSpace v)))
                  (f := fun a : bn.stateSpace v => if a ∈ SB then cpt.cpt v paC a else 0)
                  (a := R xrest)).symm
        _ = qB * R xrest := by simp [qB]
        _ = if PT0 xrest then qB * R xrest else 0 := by simp [hPT]
    · have hBtFa : ∀ a : bn.stateSpace v, ¬ P_BtF (eND.symm (a, xrest)) := by
        intro a h
        exact hPT (hP_BtF_split a xrest |>.1 h |>.2)
      simp [hBtFa, hPT]

  have hμ_F_as :
      cpt.jointMeasure F = ∑ xrest : XRest, if PF0 xrest then R xrest else 0 := by
    calc
      cpt.jointMeasure F
          =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_F_split'
      _ = ∑ xrest : XRest, if PF0 xrest then R xrest else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            exact hInner_F xrest

  have hμ_t₂F_as :
      cpt.jointMeasure S_t₂F = ∑ xrest : XRest, if PT0 xrest then R xrest else 0 := by
    calc
      cpt.jointMeasure S_t₂F
          =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_t₂F (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_t₂F_split'
      _ = ∑ xrest : XRest, if PT0 xrest then R xrest else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            exact hInner_t₂F xrest

  have hμ_BF_as :
      cpt.jointMeasure S_BF = ∑ xrest : XRest, if PF0 xrest then qB * R xrest else 0 := by
    calc
      cpt.jointMeasure S_BF
          =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_BF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_BF_split'
      _ = ∑ xrest : XRest, if PF0 xrest then qB * R xrest else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            exact hInner_BF xrest

  have hμ_BtF_as :
      cpt.jointMeasure S_BtF = ∑ xrest : XRest, if PT0 xrest then qB * R xrest else 0 := by
    calc
      cpt.jointMeasure S_BtF
          =
        ∑ xrest : XRest,
          ∑ a : bn.stateSpace v,
            if P_BtF (eND.symm (a, xrest)) then A (eND.symm (a, xrest)) else 0 := hμ_BtF_split'
      _ = ∑ xrest : XRest, if PT0 xrest then qB * R xrest else 0 := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            exact hInner_BtF xrest

  have hμ_BF_q :
      cpt.jointMeasure S_BF = qB * cpt.jointMeasure F := by
    calc
      cpt.jointMeasure S_BF = ∑ xrest : XRest, if PF0 xrest then qB * R xrest else 0 := hμ_BF_as
      _ = ∑ xrest : XRest, qB * (if PF0 xrest then R xrest else 0) := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            by_cases hPF : PF0 xrest <;> simp [hPF]
      _ = qB * (∑ xrest : XRest, if PF0 xrest then R xrest else 0) := by
            simpa using
              (Finset.mul_sum
                (a := qB) (s := (Finset.univ : Finset XRest))
                (f := fun xrest : XRest => if PF0 xrest then R xrest else 0)).symm
      _ = qB * cpt.jointMeasure F := by rw [hμ_F_as]

  have hμ_BtF_q :
      cpt.jointMeasure S_BtF = qB * cpt.jointMeasure S_t₂F := by
    calc
      cpt.jointMeasure S_BtF = ∑ xrest : XRest, if PT0 xrest then qB * R xrest else 0 := hμ_BtF_as
      _ = ∑ xrest : XRest, qB * (if PT0 xrest then R xrest else 0) := by
            refine Finset.sum_congr rfl ?_
            intro xrest _
            by_cases hPT : PT0 xrest <;> simp [hPT]
      _ = qB * (∑ xrest : XRest, if PT0 xrest then R xrest else 0) := by
            simpa using
              (Finset.mul_sum
                (a := qB) (s := (Finset.univ : Finset XRest))
                (f := fun xrest : XRest => if PT0 xrest then R xrest else 0)).symm
      _ = qB * cpt.jointMeasure S_t₂F := by rw [hμ_t₂F_as]

  have hfinal :
      cpt.jointMeasure S_BtF * cpt.jointMeasure F
        =
      cpt.jointMeasure S_BF * cpt.jointMeasure S_t₂F := by
    calc
      cpt.jointMeasure S_BtF * cpt.jointMeasure F
          = (qB * cpt.jointMeasure S_t₂F) * cpt.jointMeasure F := by
              rw [hμ_BtF_q]
      _ = qB * (cpt.jointMeasure S_t₂F * cpt.jointMeasure F) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ = qB * (cpt.jointMeasure F * cpt.jointMeasure S_t₂F) := by
            simp [mul_comm]
      _ = (qB * cpt.jointMeasure F) * cpt.jointMeasure S_t₂F := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ = cpt.jointMeasure S_BF * cpt.jointMeasure S_t₂F := by
            rw [hμ_BF_q]
  simpa [S_BtF, S_BF, S_t₂F, Bset, Tset, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    using hfinal


/-- BN factorization CI on parent fibers: for B ∈ m_v and f = t₂.indicator 1 with t₂ ∈ m_{ND'},
    on each parent fiber F_c the joint weight factors as nodeProb(v,x_v,c) · Ψ(x_{ND'},c)
    after marginalizing descendants (telescoping_sum). This product structure gives:
    μ[B.indicator 1 * f | m_pa] =ᵃᵉ μ[B.indicator 1 | m_pa] * μ[f | m_pa]

    Proof: On fiber F_c, w(x) = nodeProb(v, x_v, c) · Ψ(x_{ND'}, c) · Σ_desc(→1).
    Since nodeProb(v) depends only on x_v,c and Ψ depends only on x_{ND'},c:
    μ(B∩t₂∩F_c) · μ(F_c) = μ(B∩F_c) · μ(t₂∩F_c). Summing over fibers gives CI. -/
private lemma condExp_indicator_mul_of_bn_ci
    (cpt : bn.DiscreteCPT) (v : V)
    (B : Set bn.JointSpace)
    (hB : MeasurableSet[bn.measurableSpaceOfVertices ({v} : Set V)] B)
    (t₂ : Set bn.JointSpace)
    (ht₂ : MeasurableSet[bn.measurableSpaceOfVertices
            (bn.nonDescendantsExceptParentsAndSelf v)] t₂) :
    cpt.jointMeasure[B.indicator (fun _ => (1 : ℝ)) * t₂.indicator (fun _ => (1 : ℝ)) |
      bn.measurableSpaceOfVertices (bn.graph.parents v)] =ᵐ[cpt.jointMeasure]
    cpt.jointMeasure[B.indicator (fun _ => (1 : ℝ)) |
      bn.measurableSpaceOfVertices (bn.graph.parents v)] *
    cpt.jointMeasure[t₂.indicator (fun _ => (1 : ℝ)) |
      bn.measurableSpaceOfVertices (bn.graph.parents v)] := by
  -- On each parent fiber F_c, w(x) factors as nodeProb(v, x_v, c) · Ψ(x_{ND'}, c)
  -- after marginalizing descendants. Since B depends only on x_v and t₂ on x_{ND'},
  -- the sums factor, giving CI.
  -- Proof: characterize μ[g|m_pa]*μ[f|m_pa] as a condExp via its integral identity.
  -- The integral condition ∫_s (prod) dμ = ∫_s (g*f) dμ on each parent fiber F_c
  -- follows from the BN product factorization: p(x)|_{F_c} = φ(x_v) · ψ(x_{ND'})
  -- (after marginalizing descendants via telescoping_sum), making g and f independent.
  set μ := cpt.jointMeasure with hμ_def
  set m_pa := bn.measurableSpaceOfVertices (bn.graph.parents v) with hm_pa_def
  set f := t₂.indicator (fun _ => (1 : ℝ)) with hf_def
  set g := B.indicator (fun _ => (1 : ℝ)) with hg_def
  have hm_pa_le : m_pa ≤ MeasurableSpace.pi := bn.measurableSpaceOfVertices_le _
  haveI hsf : SigmaFinite (μ.trim hm_pa_le) :=
    BayesianNetwork.sigmaFinite_trim_of_le bn μ m_pa hm_pa_le
  have hB_pi : @MeasurableSet _ MeasurableSpace.pi B :=
    (bn.measurableSpaceOfVertices_le _) _ hB
  have ht₂_pi : @MeasurableSet _ MeasurableSpace.pi t₂ :=
    (bn.measurableSpaceOfVertices_le _) _ ht₂
  have hf_int : Integrable f μ := (integrable_const 1).indicator ht₂_pi
  have hg_int : Integrable g μ := (integrable_const 1).indicator hB_pi
  have hgf_eq : g * f = (B ∩ t₂).indicator (fun _ => (1 : ℝ)) := by
    ext x; simp only [g, f, Pi.mul_apply, Set.indicator, Set.mem_inter_iff]
    split_ifs <;> simp_all
  have hgf_int : Integrable (g * f) μ := by
    rw [hgf_eq]; exact (integrable_const 1).indicator (hB_pi.inter ht₂_pi)
  -- Product of condExps: m_pa-measurable, integrable (bounded by 1)
  have hprod_sm : StronglyMeasurable[m_pa] (μ[g | m_pa] * μ[f | m_pa]) :=
    stronglyMeasurable_condExp.mul stronglyMeasurable_condExp
  have hg_bnd := condExp_indicator_norm_le_one bn μ hm_pa_le B hB_pi
  have hf_bnd := condExp_indicator_norm_le_one bn μ hm_pa_le t₂ ht₂_pi
  have hprod_int : Integrable (μ[g | m_pa] * μ[f | m_pa]) μ := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (stronglyMeasurable_condExp.mono hm_pa_le).aestronglyMeasurable.mul
        (stronglyMeasurable_condExp.mono hm_pa_le).aestronglyMeasurable
    · filter_upwards [hg_bnd, hf_bnd] with x hgx hfx
      simp only [Pi.mul_apply, norm_mul]
      exact le_trans (mul_le_mul hgx hfx (norm_nonneg _) zero_le_one) (by norm_num)
  -- Characterize via ae_eq_condExp: need ∫_s prod dμ = ∫_s g*f dμ for all s ∈ m_pa
  symm
  exact ae_eq_condExp_of_forall_setIntegral_eq hm_pa_le hgf_int
    (fun s _ _ => hprod_int.integrableOn)
    (fun s hs _ => by
      -- Represent `s` as a preimage under the parent-restriction map, then
      -- reduce the integral equality to parent-fiber equalities.
      rcases measurableSet_parents_preimage (bn := bn) v hs with ⟨S, hS, hs_eq⟩
      subst hs_eq
      have hL :=
        setIntegral_parents_preimage (bn := bn) (μ := μ) v S
          (μ[g | m_pa] * μ[f | m_pa]) hprod_int
      have hR :=
        setIntegral_parents_preimage (bn := bn) (μ := μ) v S (g * f) hgf_int
      -- It remains to prove the per-fiber identity:
      --   ∫_{F_c} μ[g|m_pa] * μ[f|m_pa] dμ = ∫_{F_c} g*f dμ
      -- for each parent assignment `c`.
      have hFiber :
          ∀ c : ParentAssign (bn := bn) v,
            ∫ x in parentFiber (bn := bn) v c, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
              = ∫ x in parentFiber (bn := bn) v c, (g * f) x ∂μ := by
        intro c
        let F : Set bn.JointSpace := parentFiber (bn := bn) v c
        have hF_meas : @MeasurableSet _ MeasurableSpace.pi F := by
          simpa [F] using measurable_parentFiber (bn := bn) v c
        have hF_meas_mpa : MeasurableSet[m_pa] F := by
          simpa [F, hm_pa_def] using measurable_parentFiber_vertices (bn := bn) v c
        by_cases hμF0 : μ F = 0
        · have hrestrict0 : μ.restrict F = 0 := Measure.restrict_zero_set hμF0
          calc
            ∫ x in parentFiber (bn := bn) v c, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
                = ∫ x in F, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ := by rfl
            _ = 0 := by simp [MeasureTheory.integral_zero_measure, hrestrict0]
            _ = ∫ x in F, (g * f) x ∂μ := by simp [MeasureTheory.integral_zero_measure, hrestrict0]
            _ = ∫ x in parentFiber (bn := bn) v c, (g * f) x ∂μ := by rfl
        · have hFne : F.Nonempty := by
            by_contra hne
            have hE : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
            exact hμF0 (by simpa [hE] using (MeasureTheory.measure_empty (μ := μ)))
          rcases hFne with ⟨ω0, hω0⟩
          have hconst_g :
              (fun x => (μ[g | m_pa]) x) =ᵐ[μ.restrict F] fun _ => (μ[g | m_pa]) ω0 := by
            refine (MeasureTheory.ae_restrict_iff' hF_meas).2 ?_
            refine Filter.Eventually.of_forall ?_
            intro x hx
            have hPx : parentsRestrict (bn := bn) v x = c := by
              simpa [F, parentFiber] using hx
            have hP0 : parentsRestrict (bn := bn) v ω0 = c := by
              simpa [F, parentFiber] using hω0
            exact measurable_const_on_fiber_set (bn := bn) (S := (bn.graph.parents v : Set V))
              (f := fun z => (μ[g | m_pa]) z)
              ((stronglyMeasurable_condExp (μ := μ) (m := m_pa) (f := g)).measurable)
              (by simpa [parentsRestrict] using hPx.trans hP0.symm)
          have hconst_f :
              (fun x => (μ[f | m_pa]) x) =ᵐ[μ.restrict F] fun _ => (μ[f | m_pa]) ω0 := by
            refine (MeasureTheory.ae_restrict_iff' hF_meas).2 ?_
            refine Filter.Eventually.of_forall ?_
            intro x hx
            have hPx : parentsRestrict (bn := bn) v x = c := by
              simpa [F, parentFiber] using hx
            have hP0 : parentsRestrict (bn := bn) v ω0 = c := by
              simpa [F, parentFiber] using hω0
            exact measurable_const_on_fiber_set (bn := bn) (S := (bn.graph.parents v : Set V))
              (f := fun z => (μ[f | m_pa]) z)
              ((stronglyMeasurable_condExp (μ := μ) (m := m_pa) (f := f)).measurable)
              (by simpa [parentsRestrict] using hPx.trans hP0.symm)
          have hconst_prod :
              (fun x => (μ[g | m_pa] * μ[f | m_pa]) x) =ᵐ[μ.restrict F]
                fun _ => (μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0 := by
            filter_upwards [hconst_g, hconst_f] with x hgx hfx
            simp [hgx, hfx]
          have hLconst :
              ∫ x in F, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
                = ((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F := by
            exact setIntegral_const_on (bn := bn) (μ := μ) (s := F) hF_meas _ hconst_prod
          have hGconst :
              ∫ x in F, (μ[g | m_pa]) x ∂μ = (μ[g | m_pa]) ω0 * μ.real F := by
            exact setIntegral_const_on (bn := bn) (μ := μ) (s := F) hF_meas _ hconst_g
          have hFconst :
              ∫ x in F, (μ[f | m_pa]) x ∂μ = (μ[f | m_pa]) ω0 * μ.real F := by
            exact setIntegral_const_on (bn := bn) (μ := μ) (s := F) hF_meas _ hconst_f
          have hGset :
              ∫ x in F, (μ[g | m_pa]) x ∂μ = ∫ x in F, g x ∂μ := by
            exact (MeasureTheory.setIntegral_condExp
              (hm := hm_pa_le) (μ := μ) (f := g) hg_int hF_meas_mpa)
          have hFset :
              ∫ x in F, (μ[f | m_pa]) x ∂μ = ∫ x in F, f x ∂μ := by
            exact (MeasureTheory.setIntegral_condExp
              (hm := hm_pa_le) (μ := μ) (f := f) hf_int hF_meas_mpa)
          have hInt_g :
              ∫ x in F, g x ∂μ = μ.real (B ∩ F) := by
            calc
              ∫ x in F, g x ∂μ
                  = ∫ x in F, (B.indicator (fun _ : bn.JointSpace => (1 : ℝ))) x ∂μ := by
                      rfl
              _ = ∫ x in F ∩ B, (fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ := by
                    simpa using
                      (MeasureTheory.setIntegral_indicator (μ := μ) (s := F)
                        (t := B) (f := fun _ : bn.JointSpace => (1 : ℝ)) hB_pi)
              _ = μ.real (F ∩ B) := by
                    simpa using
                      (MeasureTheory.setIntegral_const (μ := μ) (s := F ∩ B)
                        (c := (1 : ℝ)))
              _ = μ.real (B ∩ F) := by simp [Set.inter_comm]
          have hInt_f :
              ∫ x in F, f x ∂μ = μ.real (t₂ ∩ F) := by
            calc
              ∫ x in F, f x ∂μ
                  = ∫ x in F, (t₂.indicator (fun _ : bn.JointSpace => (1 : ℝ))) x ∂μ := by
                      rfl
              _ = ∫ x in F ∩ t₂, (fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ := by
                    simpa using
                      (MeasureTheory.setIntegral_indicator (μ := μ) (s := F)
                        (t := t₂) (f := fun _ : bn.JointSpace => (1 : ℝ)) ht₂_pi)
              _ = μ.real (F ∩ t₂) := by
                    simpa using
                      (MeasureTheory.setIntegral_const (μ := μ) (s := F ∩ t₂)
                        (c := (1 : ℝ)))
              _ = μ.real (t₂ ∩ F) := by simp [Set.inter_comm]
          have hInt_gf :
              ∫ x in F, (g * f) x ∂μ = μ.real ((B ∩ t₂) ∩ F) := by
            calc
              ∫ x in F, (g * f) x ∂μ
                  = ∫ x in F, ((B ∩ t₂).indicator (fun _ : bn.JointSpace => (1 : ℝ))) x ∂μ := by
                      rw [hgf_eq]
              _ = ∫ x in F ∩ (B ∩ t₂), (fun _ : bn.JointSpace => (1 : ℝ)) x ∂μ := by
                    simpa using
                      (MeasureTheory.setIntegral_indicator (μ := μ) (s := F)
                        (t := (B ∩ t₂)) (f := fun _ : bn.JointSpace => (1 : ℝ))
                        (hB_pi.inter ht₂_pi))
              _ = μ.real (F ∩ (B ∩ t₂)) := by
                    simpa using
                      (MeasureTheory.setIntegral_const (μ := μ) (s := F ∩ (B ∩ t₂))
                        (c := (1 : ℝ)))
              _ = μ.real ((B ∩ t₂) ∩ F) := by
                    simp [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          have hscreen : μ ((B ∩ t₂) ∩ F) * μ F = μ (B ∩ F) * μ (t₂ ∩ F) := by
            simpa [μ, F, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
              fiber_screening_mul (bn := bn) (cpt := cpt) (v := v) (B := B) (hB := hB)
                (t₂ := t₂) (ht₂ := ht₂) c
          have hscreen_real :
              μ.real ((B ∩ t₂) ∩ F) * μ.real F = μ.real (B ∩ F) * μ.real (t₂ ∩ F) := by
            have htoReal := congrArg ENNReal.toReal hscreen
            simpa [Measure.real, ENNReal.toReal_mul,
              MeasureTheory.measure_ne_top (μ := μ) (s := ((B ∩ t₂) ∩ F)),
              MeasureTheory.measure_ne_top (μ := μ) (s := F),
              MeasureTheory.measure_ne_top (μ := μ) (s := (B ∩ F)),
              MeasureTheory.measure_ne_top (μ := μ) (s := (t₂ ∩ F))] using htoReal
          have hGF : (μ[g | m_pa]) ω0 * μ.real F = μ.real (B ∩ F) := by
            calc
              (μ[g | m_pa]) ω0 * μ.real F = ∫ x in F, (μ[g | m_pa]) x ∂μ := by
                simpa [hGconst] using hGconst.symm
              _ = ∫ x in F, g x ∂μ := hGset
              _ = μ.real (B ∩ F) := hInt_g
          have hFF : (μ[f | m_pa]) ω0 * μ.real F = μ.real (t₂ ∩ F) := by
            calc
              (μ[f | m_pa]) ω0 * μ.real F = ∫ x in F, (μ[f | m_pa]) x ∂μ := by
                simpa [hFconst] using hFconst.symm
              _ = ∫ x in F, f x ∂μ := hFset
              _ = μ.real (t₂ ∩ F) := hInt_f
          have hmul :
              (((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F) * μ.real F
                = (μ.real ((B ∩ t₂) ∩ F)) * μ.real F := by
            calc
              (((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F) * μ.real F
                  = ((μ[g | m_pa]) ω0 * μ.real F) * ((μ[f | m_pa]) ω0 * μ.real F) := by
                      ring
              _ = μ.real (B ∩ F) * μ.real (t₂ ∩ F) := by
                    simp [hGF, hFF]
              _ = (μ.real ((B ∩ t₂) ∩ F)) * μ.real F := by
                    simpa [mul_comm, mul_left_comm, mul_assoc] using hscreen_real.symm
          have hmain :
              ((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F
                = μ.real ((B ∩ t₂) ∩ F) := by
            have hF0 : μ.real F ≠ 0 := by
              intro h0
              have hzero_or_top : μ F = 0 ∨ μ F = ⊤ := by
                exact (ENNReal.toReal_eq_zero_iff (μ F)).1 (by simpa [Measure.real] using h0)
              have : μ F = 0 := by
                rcases hzero_or_top with hzero | htop
                · exact hzero
                · exact (MeasureTheory.measure_ne_top (μ := μ) (s := F) htop).elim
              exact hμF0 this
            exact mul_right_cancel₀ hF0 hmul
          calc
            ∫ x in F, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
                = ((μ[g | m_pa]) ω0 * (μ[f | m_pa]) ω0) * μ.real F := hLconst
            _ = μ.real ((B ∩ t₂) ∩ F) := hmain
            _ = ∫ x in F, (g * f) x ∂μ := by
                  symm
                  exact hInt_gf
      calc
        ∫ x in (parentsRestrict (bn := bn) v) ⁻¹' S, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
            = ∑ c : ParentAssign (bn := bn) v,
                if c ∈ S then
                  ∫ x in parentFiber (bn := bn) v c, (μ[g | m_pa] * μ[f | m_pa]) x ∂μ
                else 0 := hL
        _ = ∑ c : ParentAssign (bn := bn) v,
              if c ∈ S then
                ∫ x in parentFiber (bn := bn) v c, (g * f) x ∂μ
              else 0 := by
              refine Finset.sum_congr rfl ?_
              intro c _
              by_cases hc : c ∈ S
              · simp [hc]
                exact hFiber c
              · simp [hc]
        _ = ∫ x in (parentsRestrict (bn := bn) v) ⁻¹' S, (g * f) x ∂μ := hR.symm)
    hprod_sm.aestronglyMeasurable

/-- Key BN-specific lemma: conditioning on vertex v gives no additional information
    about non-descendants beyond what the parents provide.

    This is the heart of the local Markov property for Bayesian networks.
    The proof uses the BN product factorization: on each parent fiber F_c,
    the weight factors as φ_v(x_v,c) · φ_ND(x_{ND'},c) after marginalizing
    descendants (via telescoping_sum). Since the ratio μ(t₂∩F_{c,a})/μ(F_{c,a})
    is independent of a (the v-value), adding v to the conditioning doesn't change
    the conditional expectation of t₂. -/
theorem condExp_ndesc_indep_of_vertex
    (cpt : bn.DiscreteCPT) (v : V)
    (t₂ : Set bn.JointSpace)
    (ht₂ : MeasurableSet[bn.measurableSpaceOfVertices
            (bn.nonDescendantsExceptParentsAndSelf v)] t₂) :
    (cpt.jointMeasure)⟦t₂ |
      bn.measurableSpaceOfVertices (bn.graph.parents v) ⊔
      bn.measurableSpaceOfVertices ({v} : Set V)⟧ =ᵐ[cpt.jointMeasure]
    (cpt.jointMeasure)⟦t₂ | bn.measurableSpaceOfVertices (bn.graph.parents v)⟧ := by
  -- Strategy: use ae_eq_condExp_of_forall_setIntegral_eq to show
  -- μ[f|m_pa] is a version of μ[f|m_pav], where f = 1_{t₂}.
  set μ := cpt.jointMeasure with hμ_def
  set m_pa := bn.measurableSpaceOfVertices (bn.graph.parents v) with hm_pa_def
  set m_v := bn.measurableSpaceOfVertices ({v} : Set V) with hm_v_def
  set m_pav := m_pa ⊔ m_v with hm_pav_def
  set f : bn.JointSpace → ℝ := t₂.indicator (fun _ => 1) with hf_def
  have hm_pa_le : m_pa ≤ MeasurableSpace.pi := bn.measurableSpaceOfVertices_le _
  have hm_pav_le : m_pav ≤ MeasurableSpace.pi :=
    sup_le hm_pa_le (bn.measurableSpaceOfVertices_le _)
  haveI : SigmaFinite (μ.trim hm_pav_le) :=
    BayesianNetwork.sigmaFinite_trim_of_le bn μ m_pav hm_pav_le
  have ht₂_pi : @MeasurableSet _ MeasurableSpace.pi t₂ :=
    (bn.measurableSpaceOfVertices_le _) _ ht₂
  have hf_int : Integrable f μ := (integrable_const 1).indicator ht₂_pi
  -- μ[f|m_pa] is m_pav-strongly measurable (since m_pa ≤ m_pav)
  have hm_pa_le_pav : m_pa ≤ m_pav := le_sup_left
  have hg_sm : AEStronglyMeasurable[m_pav] (μ[f | m_pa]) μ :=
    (stronglyMeasurable_condExp (m := m_pa)).mono hm_pa_le_pav |>.aestronglyMeasurable
  -- μ[f|m_pa] is integrable on any set
  have hg_int : ∀ s, MeasurableSet[m_pav] s → μ s < ⊤ → IntegrableOn (μ[f | m_pa]) s μ :=
    fun _ _ _ => integrable_condExp.integrableOn
  -- KEY: integral condition on all m_pav-measurable sets
  have hg_eq : ∀ s, MeasurableSet[m_pav] s → μ s < ⊤ →
      ∫ x in s, (μ[f | m_pa]) x ∂μ = ∫ x in s, f x ∂μ := by
    intro s hs _
    -- Use Dynkin π-λ theorem (induction_on_inter) to extend from π-system generators
    -- π-system: {A ∩ B | A ∈ m_pa, B ∈ m_v}
    let π : Set (Set bn.JointSpace) :=
      {t | ∃ A B, MeasurableSet[m_pa] A ∧ MeasurableSet[m_v] B ∧ t = A ∩ B}
    -- m_pav = generateFrom π
    have h_gen : m_pav = MeasurableSpace.generateFrom π := by
      apply le_antisymm
      · apply sup_le
        · intro t ht
          exact MeasurableSpace.measurableSet_generateFrom
            ⟨t, Set.univ, ht, MeasurableSet.univ, (Set.inter_univ t).symm⟩
        · intro t ht
          exact MeasurableSpace.measurableSet_generateFrom
            ⟨Set.univ, t, MeasurableSet.univ, ht, (Set.univ_inter t).symm⟩
      · exact MeasurableSpace.generateFrom_le fun t ⟨A, B, hA, hB, ht_eq⟩ => by
          subst ht_eq
          exact MeasurableSet.inter (hm_pa_le_pav _ hA) ((le_sup_right : m_v ≤ m_pav) _ hB)
    -- π is a π-system
    have h_pi : IsPiSystem π := by
      intro s₁ ⟨A₁, B₁, hA₁, hB₁, hs₁⟩ s₂ ⟨A₂, B₂, hA₂, hB₂, hs₂⟩ _
      exact ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, by
        subst hs₁; subst hs₂; ext x; simp [Set.mem_inter_iff]; tauto⟩
    -- SigmaFinite for m_pa (needed for setIntegral_condExp)
    haveI hsf_pa : SigmaFinite (μ.trim hm_pa_le) :=
      BayesianNetwork.sigmaFinite_trim_of_le bn μ m_pa hm_pa_le
    -- Apply Dynkin theorem
    have h_dynkin := MeasurableSpace.induction_on_inter h_gen h_pi
      (C := fun s _ => ∫ x in s, (μ[f | m_pa]) x ∂μ = ∫ x in s, f x ∂μ)
      (by simp) -- C(∅)
      (by -- C(basic): for A ∩ B ∈ π — BN factorization gives CI on parent fibers
        intro t ⟨A, B, hA, hB, ht_eq⟩; subst ht_eq
        have hB_pi : @MeasurableSet _ MeasurableSpace.pi B :=
          (bn.measurableSpaceOfVertices_le _) _ hB
        -- Use the CI lemma
        have hci := condExp_indicator_mul_of_bn_ci bn cpt v B hB t₂ ht₂
        -- hci : μ[g * f | m_pa] =ᵃᵉ μ[g | m_pa] * μ[f | m_pa]
        -- where g = B.indicator 1
        set g := B.indicator (fun _ => (1 : ℝ)) with hg_def
        have hg_int : Integrable g μ := (integrable_const 1).indicator hB_pi
        -- g * f = (B ∩ t₂).indicator 1
        have hgf_eq : g * f = (B ∩ t₂).indicator (fun _ => (1 : ℝ)) := by
          ext x; simp only [g, f, hg_def, hf_def, Pi.mul_apply, Set.indicator,
            Set.mem_inter_iff]; split_ifs <;> simp_all
        have hgf_int : Integrable (g * f) μ := by
          rw [hgf_eq]; exact (integrable_const 1).indicator (hB_pi.inter ht₂_pi)
        -- Key identity: g * μ[f|m_pa] = μ[f|m_pa] * g (commute for pull-out)
        have hgce_int : Integrable (g * fun x => (μ[f|m_pa]) x) μ := by
          have heq : g * (fun x => (μ[f|m_pa]) x) =
              B.indicator (fun x => (μ[f|m_pa]) x) := by
            ext x; simp [g, Set.indicator, Pi.mul_apply]
          rw [heq]; exact (integrable_condExp (m := m_pa)).indicator hB_pi
        -- Convert ∫_{A∩B} to ∫_A via setIntegral_indicator
        rw [← setIntegral_indicator hB_pi, ← setIntegral_indicator hB_pi]
        -- Rewrite B.indicator h as g * h
        have h_ind_rhs : (fun x => B.indicator f x) = g * f := by
          ext x; simp only [Set.indicator_apply, Pi.mul_apply, g]
          split_ifs <;> simp
        have h_ind_lhs : (fun x => B.indicator (fun x => (μ[f|m_pa]) x) x) =
            (g * fun x => (μ[f|m_pa]) x) := by
          ext x; simp only [Set.indicator_apply, Pi.mul_apply, g]
          split_ifs <;> simp
        rw [h_ind_lhs, h_ind_rhs]
        -- Goal: ∫_A (g * μ[f|m_pa]) dμ = ∫_A (g * f) dμ
        -- Step 1: RHS = ∫_A μ[g*f|m_pa] dμ (by setIntegral_condExp.symm)
        rw [(setIntegral_condExp hm_pa_le hgf_int hA).symm]
        -- Step 2: LHS = ∫_A μ[g*μ[f|m_pa]|m_pa] dμ (by setIntegral_condExp.symm)
        rw [show ∫ x in A, (g * fun x => (μ[f|m_pa]) x) x ∂μ =
            ∫ x in A, (μ[g * fun x => (μ[f|m_pa]) x | m_pa]) x ∂μ from
          (setIntegral_condExp hm_pa_le hgce_int hA).symm]
        -- Goal: ∫_A μ[g*μ[f|m_pa]|m_pa] dμ = ∫_A μ[g*f|m_pa] dμ
        -- Step 3: By pull-out, μ[g*μ[f|m_pa]|m_pa] =ᵃᵉ μ[f|m_pa]*μ[g|m_pa]
        -- (since μ[f|m_pa] is m_pa-strongly-measurable)
        have hce_bnd := condExp_indicator_norm_le_one bn μ hm_pa_le t₂ ht₂_pi
        have h_pullout : μ[g * (fun x => (μ[f|m_pa]) x) | m_pa] =ᵐ[μ]
            (fun x => (μ[f|m_pa]) x) * μ[g | m_pa] := by
          have hcomm : g * (fun x => (μ[f|m_pa]) x) =
              (fun x => (μ[f|m_pa]) x) * g := mul_comm _ _
          rw [hcomm]
          exact condExp_stronglyMeasurable_mul_of_bound hm_pa_le
            stronglyMeasurable_condExp hg_int 1 hce_bnd
        -- Step 4: By CI, μ[g*f|m_pa] =ᵃᵉ μ[g|m_pa]*μ[f|m_pa]
        -- Both =ᵃᵉ μ[f|m_pa]*μ[g|m_pa] (by mul_comm)
        have h_ci_comm : μ[g * f | m_pa] =ᵐ[μ]
            (fun x => (μ[f|m_pa]) x) * μ[g | m_pa] := by
          exact hci.trans (Filter.EventuallyEq.of_eq (mul_comm _ _))
        -- Both integrands are a.e. equal:
        -- μ[g * μ[f|m_pa] | m_pa] =ᵃᵉ μ[f|m_pa] * μ[g|m_pa] =ᵃᵉ μ[g * f | m_pa]
        -- So their integrals over A are equal
        exact setIntegral_congr_ae (hm_pa_le _ hA)
          ((h_pullout.trans h_ci_comm.symm).mono (fun x hx => fun _ => hx)))
      (by -- C(complement): C(t) → C(tᶜ)
        intro t ht hCt
        have ht_pi : @MeasurableSet _ MeasurableSpace.pi t := hm_pav_le _ ht
        have h_total : ∫ x, (μ[f | m_pa]) x ∂μ = ∫ x, f x ∂μ :=
          integral_condExp hm_pa_le
        have hg_int' : Integrable (fun x => (μ[f | m_pa]) x : bn.JointSpace → ℝ) μ :=
          integrable_condExp (m := m_pa)
        have hg_add := integral_add_compl ht_pi hg_int'
        have hf_add := integral_add_compl ht_pi hf_int
        linarith)
      (by -- C(countable disjoint union)
        intro g_seq hd hm hC
        have hg_meas : ∀ i, @MeasurableSet _ MeasurableSpace.pi (g_seq i) :=
          fun i => hm_pav_le _ (hm i)
        have h1 : ∫ x in ⋃ i, g_seq i, (μ[f | m_pa]) x ∂μ =
            ∑' i, ∫ x in g_seq i, (μ[f | m_pa]) x ∂μ :=
          integral_iUnion hg_meas hd integrable_condExp.integrableOn
        have h2 : ∫ x in ⋃ i, g_seq i, f x ∂μ =
            ∑' i, ∫ x in g_seq i, f x ∂μ :=
          integral_iUnion hg_meas hd hf_int.integrableOn
        rw [h1, h2]
        exact tsum_congr hC)
    exact h_dynkin s hs
  exact (ae_eq_condExp_of_forall_setIntegral_eq hm_pav_le hf_int hg_int hg_eq hg_sm).symm

/-- The local Markov property holds for discrete CPT joint measures.

    Uses the tower/pull-out proof:
    1. Pull-out on m_pa⊔m_v: μ[1_{t₁}·1_{t₂}|m_pav] =ᵐ 1_{t₁}·μ[1_{t₂}|m_pav]
    2. BN factorization: μ[1_{t₂}|m_pav] =ᵐ μ[1_{t₂}|m_pa]
    3. Tower: μ[μ[·|m_pav]|m_pa] =ᵐ μ[·|m_pa]
    4. Pull-out on m_pa: μ[μ[f₂|m_pa]·1_{t₁}|m_pa] =ᵐ μ[f₂|m_pa]·μ[1_{t₁}|m_pa]
-/
theorem discrete_localMarkovCondition
    (cpt : bn.DiscreteCPT) (v : V) :
    LocalMarkovCondition bn cpt.jointMeasure v := by
  rw [LocalMarkovCondition, condIndep_iff]
  · intro t₁ t₂ ht₁ ht₂
    let m_pa := bn.measurableSpaceOfVertices (bn.graph.parents v)
    let m_pav := m_pa ⊔ bn.measurableSpaceOfVertices ({v} : Set V)
    have hm_pa_le : m_pa ≤ MeasurableSpace.pi := bn.measurableSpaceOfVertices_le _
    have hm_pav_le : m_pav ≤ MeasurableSpace.pi :=
      sup_le hm_pa_le (bn.measurableSpaceOfVertices_le _)
    haveI hsf : SigmaFinite (cpt.jointMeasure.trim hm_pav_le) :=
      BayesianNetwork.sigmaFinite_trim_of_le bn cpt.jointMeasure m_pav hm_pav_le
    have ht₁_pi : @MeasurableSet _ MeasurableSpace.pi t₁ :=
      (bn.measurableSpaceOfVertices_le _) _ ht₁
    have ht₂_pi : @MeasurableSet _ MeasurableSpace.pi t₂ :=
      (bn.measurableSpaceOfVertices_le _) _ ht₂
    -- Indicator functions
    let f₁ := t₁.indicator (fun _ => (1 : ℝ))
    let f₂ := t₂.indicator (fun _ => (1 : ℝ))
    have hf₁_int : Integrable f₁ cpt.jointMeasure :=
      (integrable_const (1 : ℝ)).indicator ht₁_pi
    have hf₂_int : Integrable f₂ cpt.jointMeasure :=
      (integrable_const (1 : ℝ)).indicator ht₂_pi
    -- Step 1: 1_{t₁∩t₂} = f₁ * f₂
    have hind : (t₁ ∩ t₂).indicator (fun _ => (1 : ℝ)) = f₁ * f₂ := by
      ext ω; simp only [f₁, f₂, Set.indicator, Pi.mul_apply, Set.mem_inter_iff]
      split_ifs <;> simp_all
    -- Step 2: Pull-out on m_pav: μ[f₁*f₂|m_pav] =ᵐ f₁ * μ[f₂|m_pav]
    have hf₁_sm : StronglyMeasurable[m_pav] f₁ :=
      (stronglyMeasurable_const.indicator ht₁).mono le_sup_right
    have hf₁_bnd : ∀ᵐ ω ∂cpt.jointMeasure, ‖f₁ ω‖ ≤ 1 := by
      filter_upwards with ω; simp only [f₁, Set.indicator]; split_ifs <;> simp
    have h2 : cpt.jointMeasure[(t₁ ∩ t₂).indicator (fun _ => (1:ℝ)) | m_pav] =ᵐ[cpt.jointMeasure]
        f₁ * cpt.jointMeasure[f₂ | m_pav] :=
      (condExp_congr_ae (Filter.EventuallyEq.of_eq hind)).trans
        (condExp_stronglyMeasurable_mul_of_bound hm_pav_le hf₁_sm hf₂_int 1 hf₁_bnd)
    -- Step 3: BN factorization: μ[f₂|m_pav] =ᵐ μ[f₂|m_pa]
    have h3 := condExp_ndesc_indep_of_vertex bn cpt v t₂ ht₂
    -- Step 4: Combine 2+3: μ[1_{t₁∩t₂}|m_pav] =ᵐ f₁ * μ[f₂|m_pa]
    have h4 := h2.trans (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ f₁) h3)
    -- Step 5: Tower + condition: μ[1_{t₁∩t₂}|m_pa] =ᵐ μ[f₁*μ[f₂|m_pa]|m_pa]
    have h5 : cpt.jointMeasure[(t₁ ∩ t₂).indicator (fun _ => (1:ℝ)) | m_pa]
        =ᵐ[cpt.jointMeasure]
        cpt.jointMeasure[f₁ * cpt.jointMeasure[f₂ | m_pa] | m_pa] :=
      (condExp_condExp_of_le (m₁ := m_pa) (m₂ := m_pav) le_sup_left hm_pav_le).symm.trans
        (condExp_congr_ae h4)
    -- Step 6: Pull-out on m_pa: μ[g*f₁|m_pa] =ᵐ g*μ[f₁|m_pa] where g = μ[f₂|m_pa]
    have hce_bnd := condExp_indicator_norm_le_one bn cpt.jointMeasure hm_pa_le t₂ ht₂_pi
    have h6 : cpt.jointMeasure[f₁ * cpt.jointMeasure[f₂ | m_pa] | m_pa]
        =ᵐ[cpt.jointMeasure]
        cpt.jointMeasure[f₁ | m_pa] * cpt.jointMeasure[f₂ | m_pa] := by
      have hcomm : f₁ * cpt.jointMeasure[f₂ | m_pa] =
          cpt.jointMeasure[f₂ | m_pa] * f₁ := mul_comm _ _
      rw [hcomm]
      exact (condExp_stronglyMeasurable_mul_of_bound hm_pa_le
        stronglyMeasurable_condExp hf₁_int 1 hce_bnd).trans
        (Filter.EventuallyEq.of_eq (mul_comm _ _))
    exact h5.trans h6
  · exact bn.measurableSpaceOfVertices_le _
  · exact bn.measurableSpaceOfVertices_le _

instance discrete_hasLocalMarkovProperty
    (cpt : bn.DiscreteCPT) :
    HasLocalMarkovProperty bn cpt.jointMeasure where
  markov_condition := discrete_localMarkovCondition bn cpt

end Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov
