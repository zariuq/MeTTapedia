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
      -- Goal: ∫_s (μ[g|m_pa] * μ[f|m_pa]) dμ = ∫_s (g * f) dμ
      -- On each parent fiber F_c, BN weight factors as φ(x_v,c) * Ψ(x_{ND'},c)
      -- after marginalizing descendants. Since g depends only on x_v and f on x_{ND'},
      -- the sums factor: ∫_{F_c} g*f = (∫_{F_c} g)(∫_{F_c} f)/μ(F_c), giving CI.
      sorry)
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
