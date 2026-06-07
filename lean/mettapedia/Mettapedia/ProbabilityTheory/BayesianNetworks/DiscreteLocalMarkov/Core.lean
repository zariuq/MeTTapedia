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
import Mettapedia.ProbabilityTheory.BayesianNetworks.ScreeningOffFromCondIndep

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

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

/-! ## Block-scope respect for relevant factors -/

/-- If a relevant local factor scope meets the `X`-reachable outside-`Z` block,
then any variable outside `X ∪ Z` is not a parent of that factor head. -/
theorem not_parent_of_outside_xReachableBlock_conditioning_of_scope_meets_xReachableBlock
    (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    {v u w : V}
    (hv : v ∈ DSeparation.relevantVertices bn.graph X Y Z)
    (huBlock : u ∈ DSeparation.xReachableBlock bn.graph X Y Z)
    (huScope : u = v ∨ bn.graph.edges u v)
    (hwOut : w ∉ DSeparation.xReachableBlock bn.graph X Y Z ∪ Z) :
    w ∉ bn.graph.parents v := by
  intro hwPar
  have hwRel : w ∈ DSeparation.relevantVertices bn.graph X Y Z :=
    DSeparation.edge_source_relevant bn.graph X Y Z hv hwPar
  have hwZ : w ∉ Z := by
    exact fun hwZ => hwOut (Or.inr hwZ)
  have hwW : w ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hwRel, hwZ⟩
  have hwX : w ∈ DSeparation.xReachableBlock bn.graph X Y Z :=
    DSeparation.same_headScope_relevantOutsideConditioning_subset_xReachableBlock
      bn.graph X Y Z hirr hv huBlock huScope hwW (Or.inr hwPar)
  exact hwOut (Or.inl hwX)

/-- If a relevant local factor scope meets the `X`-reachable outside-`Z` block,
then updating any variable outside `X ∪ Z` does not affect the factor head. -/
theorem nodeProb_independent_of_outside_xReachableBlock_conditioning_of_scope_meets_xReachableBlock
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    {v u w : V}
    (hv : v ∈ DSeparation.relevantVertices bn.graph X Y Z)
    (huBlock : u ∈ DSeparation.xReachableBlock bn.graph X Y Z)
    (huScope : u = v ∨ bn.graph.edges u v)
    (hwOut : w ∉ DSeparation.xReachableBlock bn.graph X Y Z ∪ Z)
    (x : bn.JointSpace) (a : bn.stateSpace w) :
    cpt.nodeProb (Function.update x w a) v = cpt.nodeProb x v := by
  apply nodeProb_update_irrelevant bn cpt w v
  · exact not_parent_of_outside_xReachableBlock_conditioning_of_scope_meets_xReachableBlock
      bn X Y Z hirr hv huBlock huScope hwOut
  · intro hwv
    subst w
    by_cases hvZ : v ∈ Z
    · exact hwOut (Or.inr hvZ)
    · have hvW : v ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hv, hvZ⟩
      have hvX : v ∈ DSeparation.xReachableBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_xReachableBlock
          bn.graph X Y Z hirr hv huBlock huScope hvW (Or.inl rfl)
      exact hwOut (Or.inl hvX)

/-- Symmetric block-scope respect: if a relevant local factor scope meets the
`Y`-reachable outside-`Z` block, then variables outside `Y ∪ Z` are irrelevant
to that factor head. -/
theorem nodeProb_independent_of_outside_yReachableBlock_conditioning_of_scope_meets_yReachableBlock
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    {v u w : V}
    (hv : v ∈ DSeparation.relevantVertices bn.graph X Y Z)
    (huBlock : u ∈ DSeparation.yReachableBlock bn.graph X Y Z)
    (huScope : u = v ∨ bn.graph.edges u v)
    (hwOut : w ∉ DSeparation.yReachableBlock bn.graph X Y Z ∪ Z)
    (x : bn.JointSpace) (a : bn.stateSpace w) :
    cpt.nodeProb (Function.update x w a) v = cpt.nodeProb x v := by
  apply nodeProb_update_irrelevant bn cpt w v
  · intro hwPar
    have hwRel : w ∈ DSeparation.relevantVertices bn.graph X Y Z :=
      DSeparation.edge_source_relevant bn.graph X Y Z hv hwPar
    have hwZ : w ∉ Z := by
      exact fun hwZ => hwOut (Or.inr hwZ)
    have hwW : w ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hwRel, hwZ⟩
    have hwY : w ∈ DSeparation.yReachableBlock bn.graph X Y Z :=
      DSeparation.same_headScope_relevantOutsideConditioning_subset_yReachableBlock
        bn.graph X Y Z hirr hv huBlock huScope hwW (Or.inr hwPar)
    exact hwOut (Or.inl hwY)
  · intro hwv
    subst w
    by_cases hvZ : v ∈ Z
    · exact hwOut (Or.inr hvZ)
    · have hvW : v ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hv, hvZ⟩
      have hvY : v ∈ DSeparation.yReachableBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_yReachableBlock
          bn.graph X Y Z hirr hv huBlock huScope hvW (Or.inl rfl)
      exact hwOut (Or.inl hvY)

/-- Residual block-scope respect: if a relevant local factor scope meets neither
the `X`- nor `Y`-reachable outside-`Z` blocks, then variables outside the
residual block and conditioning set are irrelevant to that factor head. -/
theorem nodeProb_independent_of_outside_residualBlock_conditioning_of_scope_missing_xy
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    {v w : V}
    (hv : v ∈ DSeparation.relevantVertices bn.graph X Y Z)
    (hNoX : ∀ {u : V}, u ∈ DSeparation.xReachableBlock bn.graph X Y Z →
      ¬ (u = v ∨ bn.graph.edges u v))
    (hNoY : ∀ {u : V}, u ∈ DSeparation.yReachableBlock bn.graph X Y Z →
      ¬ (u = v ∨ bn.graph.edges u v))
    (hwOut : w ∉ DSeparation.residualBlock bn.graph X Y Z ∪ Z)
    (x : bn.JointSpace) (a : bn.stateSpace w) :
    cpt.nodeProb (Function.update x w a) v = cpt.nodeProb x v := by
  apply nodeProb_update_irrelevant bn cpt w v
  · intro hwPar
    have hwRel : w ∈ DSeparation.relevantVertices bn.graph X Y Z :=
      DSeparation.edge_source_relevant bn.graph X Y Z hv hwPar
    have hwZ : w ∉ Z := by
      exact fun hwZ => hwOut (Or.inr hwZ)
    have hwW : w ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hwRel, hwZ⟩
    have hwR : w ∈ DSeparation.residualBlock bn.graph X Y Z :=
      DSeparation.same_headScope_relevantOutsideConditioning_subset_residualBlock
        bn.graph X Y Z hNoX hNoY hwW (Or.inr hwPar)
    exact hwOut (Or.inl hwR)
  · intro hwv
    subst w
    by_cases hvZ : v ∈ Z
    · exact hwOut (Or.inr hvZ)
    · have hvW : v ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hv, hvZ⟩
      have hvR : v ∈ DSeparation.residualBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_residualBlock
          bn.graph X Y Z hNoX hNoY hvW (Or.inl rfl)
      exact hwOut (Or.inl hvR)

/-- If a relevant local factor scope meets the `X`-reachable outside-`Z` block,
then `nodeProb` for its head depends only on the `X` block and conditioning set. -/
theorem factorization_given_xReachableBlock_conditioning_of_scope_meets_xReachableBlock
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    {v u : V}
    (hv : v ∈ DSeparation.relevantVertices bn.graph X Y Z)
    (huBlock : u ∈ DSeparation.xReachableBlock bn.graph X Y Z)
    (huScope : u = v ∨ bn.graph.edges u v)
    (x y : bn.JointSpace)
    (hXYeq : ∀ s, s ∈ DSeparation.xReachableBlock bn.graph X Y Z ∪ Z → x s = y s) :
    cpt.nodeProb x v = cpt.nodeProb y v := by
  apply factorization_given_parents bn cpt v x y
  · intro w hwPar
    have hwRel : w ∈ DSeparation.relevantVertices bn.graph X Y Z :=
      DSeparation.edge_source_relevant bn.graph X Y Z hv hwPar
    by_cases hwZ : w ∈ Z
    · exact hXYeq w (Or.inr hwZ)
    · have hwW : w ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hwRel, hwZ⟩
      have hwX : w ∈ DSeparation.xReachableBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_xReachableBlock
          bn.graph X Y Z hirr hv huBlock huScope hwW (Or.inr hwPar)
      exact hXYeq w (Or.inl hwX)
  · by_cases hvZ : v ∈ Z
    · exact hXYeq v (Or.inr hvZ)
    · have hvW : v ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hv, hvZ⟩
      have hvX : v ∈ DSeparation.xReachableBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_xReachableBlock
          bn.graph X Y Z hirr hv huBlock huScope hvW (Or.inl rfl)
      exact hXYeq v (Or.inl hvX)

/-- Symmetric block factorization: if a relevant local factor scope meets the
`Y`-reachable outside-`Z` block, then `nodeProb` for its head depends only on
that block and the conditioning set. -/
theorem factorization_given_yReachableBlock_conditioning_of_scope_meets_yReachableBlock
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    {v u : V}
    (hv : v ∈ DSeparation.relevantVertices bn.graph X Y Z)
    (huBlock : u ∈ DSeparation.yReachableBlock bn.graph X Y Z)
    (huScope : u = v ∨ bn.graph.edges u v)
    (x y : bn.JointSpace)
    (hYZeq : ∀ s, s ∈ DSeparation.yReachableBlock bn.graph X Y Z ∪ Z → x s = y s) :
    cpt.nodeProb x v = cpt.nodeProb y v := by
  apply factorization_given_parents bn cpt v x y
  · intro w hwPar
    have hwRel : w ∈ DSeparation.relevantVertices bn.graph X Y Z :=
      DSeparation.edge_source_relevant bn.graph X Y Z hv hwPar
    by_cases hwZ : w ∈ Z
    · exact hYZeq w (Or.inr hwZ)
    · have hwW : w ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hwRel, hwZ⟩
      have hwY : w ∈ DSeparation.yReachableBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_yReachableBlock
          bn.graph X Y Z hirr hv huBlock huScope hwW (Or.inr hwPar)
      exact hYZeq w (Or.inl hwY)
  · by_cases hvZ : v ∈ Z
    · exact hYZeq v (Or.inr hvZ)
    · have hvW : v ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hv, hvZ⟩
      have hvY : v ∈ DSeparation.yReachableBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_yReachableBlock
          bn.graph X Y Z hirr hv huBlock huScope hvW (Or.inl rfl)
      exact hYZeq v (Or.inl hvY)

/-- Residual block factorization: if a relevant local factor scope meets neither
reachable endpoint block, then `nodeProb` for its head depends only on the
residual block and conditioning set. -/
theorem factorization_given_residualBlock_conditioning_of_scope_missing_xy
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    {v : V}
    (hv : v ∈ DSeparation.relevantVertices bn.graph X Y Z)
    (hNoX : ∀ {u : V}, u ∈ DSeparation.xReachableBlock bn.graph X Y Z →
      ¬ (u = v ∨ bn.graph.edges u v))
    (hNoY : ∀ {u : V}, u ∈ DSeparation.yReachableBlock bn.graph X Y Z →
      ¬ (u = v ∨ bn.graph.edges u v))
    (x y : bn.JointSpace)
    (hReq : ∀ s, s ∈ DSeparation.residualBlock bn.graph X Y Z ∪ Z → x s = y s) :
    cpt.nodeProb x v = cpt.nodeProb y v := by
  apply factorization_given_parents bn cpt v x y
  · intro w hwPar
    have hwRel : w ∈ DSeparation.relevantVertices bn.graph X Y Z :=
      DSeparation.edge_source_relevant bn.graph X Y Z hv hwPar
    by_cases hwZ : w ∈ Z
    · exact hReq w (Or.inr hwZ)
    · have hwW : w ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hwRel, hwZ⟩
      have hwR : w ∈ DSeparation.residualBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_residualBlock
          bn.graph X Y Z hNoX hNoY hwW (Or.inr hwPar)
      exact hReq w (Or.inl hwR)
  · by_cases hvZ : v ∈ Z
    · exact hReq v (Or.inr hvZ)
    · have hvW : v ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hv, hvZ⟩
      have hvR : v ∈ DSeparation.residualBlock bn.graph X Y Z :=
        DSeparation.same_headScope_relevantOutsideConditioning_subset_residualBlock
          bn.graph X Y Z hNoX hNoY hvW (Or.inl rfl)
      exact hReq v (Or.inl hvR)

/-- If a relevant local factor scope meets the residual outside-`Z` block, then
`nodeProb` for its head depends only on the residual block and conditioning set. -/
theorem factorization_given_residualBlock_conditioning_of_scope_meets_residualBlock
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    {v u : V}
    (hv : v ∈ DSeparation.relevantVertices bn.graph X Y Z)
    (huBlock : u ∈ DSeparation.residualBlock bn.graph X Y Z)
    (huScope : u = v ∨ bn.graph.edges u v)
    (x y : bn.JointSpace)
    (hReq : ∀ s, s ∈ DSeparation.residualBlock bn.graph X Y Z ∪ Z → x s = y s) :
    cpt.nodeProb x v = cpt.nodeProb y v := by
  apply factorization_given_residualBlock_conditioning_of_scope_missing_xy
    bn cpt X Y Z hv ?_ ?_ x y hReq
  · intro w hwX hwScope
    have huW : u ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := huBlock.1
    have huX : u ∈ DSeparation.xReachableBlock bn.graph X Y Z :=
      DSeparation.same_headScope_relevantOutsideConditioning_subset_xReachableBlock
        bn.graph X Y Z hirr hv hwX hwScope huW huScope
    exact huBlock.2 (Or.inl huX)
  · intro w hwY hwScope
    have huW : u ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := huBlock.1
    have huY : u ∈ DSeparation.yReachableBlock bn.graph X Y Z :=
      DSeparation.same_headScope_relevantOutsideConditioning_subset_yReachableBlock
        bn.graph X Y Z hirr hv hwY hwScope huW huScope
    exact huBlock.2 (Or.inr huY)

/-- The local scope of head `v` meets the `X`-reachable outside-`Z` block. -/
def scopeMeetsXReachableBlock (X Y Z : Set V) (v : V) : Prop :=
  ∃ u, u ∈ DSeparation.xReachableBlock bn.graph X Y Z ∧ (u = v ∨ bn.graph.edges u v)

/-- The local scope of head `v` meets the `Y`-reachable outside-`Z` block. -/
def scopeMeetsYReachableBlock (X Y Z : Set V) (v : V) : Prop :=
  ∃ u, u ∈ DSeparation.yReachableBlock bn.graph X Y Z ∧ (u = v ∨ bn.graph.edges u v)

/-- The local scope of head `v` meets the residual outside-`Z` block. -/
def scopeMeetsResidualBlock (X Y Z : Set V) (v : V) : Prop :=
  ∃ u, u ∈ DSeparation.residualBlock bn.graph X Y Z ∧ (u = v ∨ bn.graph.edges u v)

/-- Relevant heads whose local scopes stay entirely in the conditioning set. -/
def scopeOnlyConditioning (X Y Z : Set V) (v : V) : Prop :=
  v ∈ DSeparation.relevantVertices bn.graph X Y Z ∧
    ¬ scopeMeetsXReachableBlock bn X Y Z v ∧
    ¬ scopeMeetsYReachableBlock bn X Y Z v ∧
    ¬ scopeMeetsResidualBlock bn X Y Z v

/-- Relevant heads whose local scopes meet the `X`-reachable outside-`Z` block. -/
noncomputable def relevantHeadXFinset (X Y Z : Set V) : Finset V :=
  Finset.univ.filter (fun v =>
    v ∈ DSeparation.relevantVertices bn.graph X Y Z ∧
      scopeMeetsXReachableBlock bn X Y Z v)

/-- Relevant heads whose local scopes meet the `Y`-reachable outside-`Z` block. -/
noncomputable def relevantHeadYFinset (X Y Z : Set V) : Finset V :=
  Finset.univ.filter (fun v =>
    v ∈ DSeparation.relevantVertices bn.graph X Y Z ∧
      scopeMeetsYReachableBlock bn X Y Z v)

/-- Relevant heads whose local scopes meet the residual outside-`Z` block. -/
noncomputable def relevantHeadResidualFinset (X Y Z : Set V) : Finset V :=
  Finset.univ.filter (fun v =>
    v ∈ DSeparation.relevantVertices bn.graph X Y Z ∧
      scopeMeetsResidualBlock bn X Y Z v)

/-- Relevant heads whose local scopes stay in the conditioning set. -/
noncomputable def relevantHeadConditioningFinset (X Y Z : Set V) : Finset V :=
  Finset.univ.filter (scopeOnlyConditioning bn X Y Z)

/-- If a relevant local factor scope has no outside-`Z` witness in any endpoint
or residual block, then `nodeProb` for its head depends only on the conditioning
set. -/
theorem factorization_given_conditioning_of_scope_onlyConditioning
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    {v : V}
    (hCond : scopeOnlyConditioning bn X Y Z v)
    (x y : bn.JointSpace)
    (hZeq : ∀ s, s ∈ Z → x s = y s) :
    cpt.nodeProb x v = cpt.nodeProb y v := by
  rcases hCond with ⟨hv, hNoX, hNoY, hNoR⟩
  apply factorization_given_parents bn cpt v x y
  · intro w hwPar
    have hwRel : w ∈ DSeparation.relevantVertices bn.graph X Y Z :=
      DSeparation.edge_source_relevant bn.graph X Y Z hv hwPar
    by_cases hwZ : w ∈ Z
    · exact hZeq w hwZ
    · have hwW : w ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hwRel, hwZ⟩
      have hwBlocks :
          w ∈ DSeparation.xReachableBlock bn.graph X Y Z ∪
              (DSeparation.yReachableBlock bn.graph X Y Z ∪
                DSeparation.residualBlock bn.graph X Y Z) := by
        rw [← DSeparation.relevantOutsideConditioning_eq_blocks_union_residual
          bn.graph X Y Z]
        exact hwW
      rcases hwBlocks with hwX | hwYR
      · exact False.elim <| hNoX ⟨w, hwX, Or.inr hwPar⟩
      · rcases hwYR with hwY | hwR
        · exact False.elim <| hNoY ⟨w, hwY, Or.inr hwPar⟩
        · exact False.elim <| hNoR ⟨w, hwR, Or.inr hwPar⟩
  · by_cases hvZ : v ∈ Z
    · exact hZeq v hvZ
    · have hvW : v ∈ DSeparation.relevantOutsideConditioning bn.graph X Y Z := ⟨hv, hvZ⟩
      have hvBlocks :
          v ∈ DSeparation.xReachableBlock bn.graph X Y Z ∪
              (DSeparation.yReachableBlock bn.graph X Y Z ∪
                DSeparation.residualBlock bn.graph X Y Z) := by
        rw [← DSeparation.relevantOutsideConditioning_eq_blocks_union_residual
          bn.graph X Y Z]
        exact hvW
      rcases hvBlocks with hvX | hvYR
      · exact False.elim <| hNoX ⟨v, hvX, Or.inl rfl⟩
      · rcases hvYR with hvY | hvR
        · exact False.elim <| hNoY ⟨v, hvY, Or.inl rfl⟩
        · exact False.elim <| hNoR ⟨v, hvR, Or.inl rfl⟩

/-- The `X`-head factor product depends only on the `X` block and conditioning set. -/
theorem prod_relevantHeadXFinset_eq_of_agree
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (x y : bn.JointSpace)
    (hXYeq : ∀ s, s ∈ DSeparation.xReachableBlock bn.graph X Y Z ∪ Z → x s = y s) :
    ∏ v ∈ relevantHeadXFinset bn X Y Z, cpt.nodeProb x v =
      ∏ v ∈ relevantHeadXFinset bn X Y Z, cpt.nodeProb y v := by
  refine Finset.prod_congr rfl ?_
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨_, hvRel, hvX⟩
  rcases hvX with ⟨u, huBlock, huScope⟩
  exact factorization_given_xReachableBlock_conditioning_of_scope_meets_xReachableBlock
    bn cpt X Y Z hirr hvRel huBlock huScope x y hXYeq

/-- The `Y`-head factor product depends only on the `Y` block and conditioning set. -/
theorem prod_relevantHeadYFinset_eq_of_agree
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (x y : bn.JointSpace)
    (hYZeq : ∀ s, s ∈ DSeparation.yReachableBlock bn.graph X Y Z ∪ Z → x s = y s) :
    ∏ v ∈ relevantHeadYFinset bn X Y Z, cpt.nodeProb x v =
      ∏ v ∈ relevantHeadYFinset bn X Y Z, cpt.nodeProb y v := by
  refine Finset.prod_congr rfl ?_
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨_, hvRel, hvY⟩
  rcases hvY with ⟨u, huBlock, huScope⟩
  exact factorization_given_yReachableBlock_conditioning_of_scope_meets_yReachableBlock
    bn cpt X Y Z hirr hvRel huBlock huScope x y hYZeq

/-- The residual-head factor product depends only on the residual block and
conditioning set. -/
theorem prod_relevantHeadResidualFinset_eq_of_agree
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (x y : bn.JointSpace)
    (hReq : ∀ s, s ∈ DSeparation.residualBlock bn.graph X Y Z ∪ Z → x s = y s) :
    ∏ v ∈ relevantHeadResidualFinset bn X Y Z, cpt.nodeProb x v =
      ∏ v ∈ relevantHeadResidualFinset bn X Y Z, cpt.nodeProb y v := by
  refine Finset.prod_congr rfl ?_
  intro v hv
  rcases Finset.mem_filter.mp hv with ⟨_, hvRel, hvR⟩
  rcases hvR with ⟨u, huBlock, huScope⟩
  exact factorization_given_residualBlock_conditioning_of_scope_meets_residualBlock
    bn cpt X Y Z hirr hvRel huBlock huScope x y hReq

/-- The conditioning-head factor product depends only on the conditioning set. -/
theorem prod_relevantHeadConditioningFinset_eq_of_agree
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (x y : bn.JointSpace)
    (hZeq : ∀ s, s ∈ Z → x s = y s) :
    ∏ v ∈ relevantHeadConditioningFinset bn X Y Z, cpt.nodeProb x v =
      ∏ v ∈ relevantHeadConditioningFinset bn X Y Z, cpt.nodeProb y v := by
  refine Finset.prod_congr rfl ?_
  intro v hv
  exact factorization_given_conditioning_of_scope_onlyConditioning
    bn cpt X Y Z (by
      exact (Finset.mem_filter.mp hv).2) x y hZeq

/-- All relevant heads for the moral-ancestral factorization surface. -/
noncomputable def relevantHeadFinset (X Y Z : Set V) : Finset V :=
  Finset.univ.filter (fun v => v ∈ DSeparation.relevantVertices bn.graph X Y Z)

/-- Irrelevant heads, complementary to `relevantHeadFinset`. -/
noncomputable def irrelevantHeadFinset (X Y Z : Set V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ DSeparation.relevantVertices bn.graph X Y Z)

/-- A relevant local factor scope cannot meet both the `X`- and `Y`-reachable
outside-`Z` blocks. -/
theorem relevantHeadXFinset_disjoint_relevantHeadYFinset
    (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z) :
    Disjoint (relevantHeadXFinset bn X Y Z) (relevantHeadYFinset bn X Y Z) := by
  apply Finset.disjoint_left.2
  intro v hvX hvY
  rcases Finset.mem_filter.mp hvX with ⟨_, hvRel, ⟨u, huBlock, huScope⟩⟩
  rcases Finset.mem_filter.mp hvY with ⟨_, _, ⟨w, hwBlock, hwScope⟩⟩
  have huw : u ≠ w := by
    intro huw
    subst huw
    exact Set.disjoint_left.mp
      (DSeparation.xReachableBlock_disjoint_yReachableBlock
        bn.graph X Y Z hXY hSep) huBlock hwBlock
  exact DSeparation.same_headScope_not_across_reachableBlocks
    bn.graph X Y Z hirr hXY hSep hvRel huBlock hwBlock huScope hwScope huw

/-- A relevant local factor scope meeting the `X`-reachable block cannot also
meet the residual outside-`Z` block. -/
theorem relevantHeadXFinset_disjoint_relevantHeadResidualFinset
    (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v) :
    Disjoint (relevantHeadXFinset bn X Y Z)
      (relevantHeadResidualFinset bn X Y Z) := by
  apply Finset.disjoint_left.2
  intro v hvX hvR
  rcases Finset.mem_filter.mp hvX with ⟨_, hvRel, ⟨u, huBlock, huScope⟩⟩
  rcases Finset.mem_filter.mp hvR with ⟨_, _, ⟨w, hwBlock, hwScope⟩⟩
  have hwX : w ∈ DSeparation.xReachableBlock bn.graph X Y Z :=
    DSeparation.same_headScope_relevantOutsideConditioning_subset_xReachableBlock
      bn.graph X Y Z hirr hvRel huBlock huScope hwBlock.1 hwScope
  exact hwBlock.2 (Or.inl hwX)

/-- A relevant local factor scope meeting the `Y`-reachable block cannot also
meet the residual outside-`Z` block. -/
theorem relevantHeadYFinset_disjoint_relevantHeadResidualFinset
    (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v) :
    Disjoint (relevantHeadYFinset bn X Y Z)
      (relevantHeadResidualFinset bn X Y Z) := by
  apply Finset.disjoint_left.2
  intro v hvY hvR
  rcases Finset.mem_filter.mp hvY with ⟨_, hvRel, ⟨u, huBlock, huScope⟩⟩
  rcases Finset.mem_filter.mp hvR with ⟨_, _, ⟨w, hwBlock, hwScope⟩⟩
  have hwY : w ∈ DSeparation.yReachableBlock bn.graph X Y Z :=
    DSeparation.same_headScope_relevantOutsideConditioning_subset_yReachableBlock
      bn.graph X Y Z hirr hvRel huBlock huScope hwBlock.1 hwScope
  exact hwBlock.2 (Or.inr hwY)

/-- By definition, a conditioning-only scope cannot meet the `X`-reachable
block. -/
theorem relevantHeadXFinset_disjoint_relevantHeadConditioningFinset
    (X Y Z : Set V) :
    Disjoint (relevantHeadXFinset bn X Y Z)
      (relevantHeadConditioningFinset bn X Y Z) := by
  apply Finset.disjoint_left.2
  intro v hvX hvC
  exact (Finset.mem_filter.mp hvC).2.2.1 (Finset.mem_filter.mp hvX).2.2

/-- By definition, a conditioning-only scope cannot meet the `Y`-reachable
block. -/
theorem relevantHeadYFinset_disjoint_relevantHeadConditioningFinset
    (X Y Z : Set V) :
    Disjoint (relevantHeadYFinset bn X Y Z)
      (relevantHeadConditioningFinset bn X Y Z) := by
  apply Finset.disjoint_left.2
  intro v hvY hvC
  exact (Finset.mem_filter.mp hvC).2.2.2.1 (Finset.mem_filter.mp hvY).2.2

/-- By definition, a conditioning-only scope cannot meet the residual
outside-`Z` block. -/
theorem relevantHeadResidualFinset_disjoint_relevantHeadConditioningFinset
    (X Y Z : Set V) :
    Disjoint (relevantHeadResidualFinset bn X Y Z)
      (relevantHeadConditioningFinset bn X Y Z) := by
  apply Finset.disjoint_left.2
  intro v hvR hvC
  exact (Finset.mem_filter.mp hvC).2.2.2.2 (Finset.mem_filter.mp hvR).2.2

/-- The relevant factor heads partition into `X`-block, `Y`-block, residual,
and conditioning-only classes. -/
theorem relevantHeadFinset_eq_block_disjUnion
    (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z) :
    relevantHeadFinset bn X Y Z =
      (relevantHeadXFinset bn X Y Z).disjUnion
        ((relevantHeadYFinset bn X Y Z).disjUnion
          ((relevantHeadResidualFinset bn X Y Z).disjUnion
            (relevantHeadConditioningFinset bn X Y Z)
            (relevantHeadResidualFinset_disjoint_relevantHeadConditioningFinset bn X Y Z))
          (by
            rw [Finset.disjoint_disjUnion_right]
            exact ⟨relevantHeadYFinset_disjoint_relevantHeadResidualFinset bn X Y Z hirr,
              relevantHeadYFinset_disjoint_relevantHeadConditioningFinset bn X Y Z⟩))
        (by
          rw [Finset.disjoint_disjUnion_right]
          exact
            ⟨relevantHeadXFinset_disjoint_relevantHeadYFinset
                bn X Y Z hirr hXY hSep,
              by
                rw [Finset.disjoint_disjUnion_right]
                exact
                  ⟨relevantHeadXFinset_disjoint_relevantHeadResidualFinset
                      bn X Y Z hirr,
                    relevantHeadXFinset_disjoint_relevantHeadConditioningFinset
                      bn X Y Z⟩⟩) := by
  classical
  let hRC :=
    relevantHeadResidualFinset_disjoint_relevantHeadConditioningFinset bn X Y Z
  let hYRC :
      Disjoint (relevantHeadYFinset bn X Y Z)
        ((relevantHeadResidualFinset bn X Y Z).disjUnion
          (relevantHeadConditioningFinset bn X Y Z) hRC) := by
    rw [Finset.disjoint_disjUnion_right]
    exact
      ⟨relevantHeadYFinset_disjoint_relevantHeadResidualFinset bn X Y Z hirr,
        relevantHeadYFinset_disjoint_relevantHeadConditioningFinset bn X Y Z⟩
  let hAll :
      Disjoint (relevantHeadXFinset bn X Y Z)
        ((relevantHeadYFinset bn X Y Z).disjUnion
          ((relevantHeadResidualFinset bn X Y Z).disjUnion
            (relevantHeadConditioningFinset bn X Y Z) hRC) hYRC) := by
    rw [Finset.disjoint_disjUnion_right]
    exact
      ⟨relevantHeadXFinset_disjoint_relevantHeadYFinset
          bn X Y Z hirr hXY hSep,
        by
          rw [Finset.disjoint_disjUnion_right]
          exact
            ⟨relevantHeadXFinset_disjoint_relevantHeadResidualFinset
                bn X Y Z hirr,
              relevantHeadXFinset_disjoint_relevantHeadConditioningFinset
                bn X Y Z⟩⟩
  ext v
  constructor
  · intro hv
    have hvRel : v ∈ DSeparation.relevantVertices bn.graph X Y Z :=
      (Finset.mem_filter.mp hv).2
    by_cases hX : scopeMeetsXReachableBlock bn X Y Z v
    · simp [relevantHeadFinset, relevantHeadXFinset, relevantHeadYFinset,
        relevantHeadResidualFinset, relevantHeadConditioningFinset,
        scopeOnlyConditioning, hRC, hYRC, hAll, hvRel, hX]
    · by_cases hY : scopeMeetsYReachableBlock bn X Y Z v
      · simp [relevantHeadFinset, relevantHeadXFinset, relevantHeadYFinset,
          relevantHeadResidualFinset, relevantHeadConditioningFinset,
          scopeOnlyConditioning, hRC, hYRC, hAll, hvRel, hX, hY]
      · by_cases hR : scopeMeetsResidualBlock bn X Y Z v
        · simp [relevantHeadFinset, relevantHeadXFinset, relevantHeadYFinset,
            relevantHeadResidualFinset, relevantHeadConditioningFinset,
            scopeOnlyConditioning, hRC, hYRC, hAll, hvRel, hX, hY, hR]
        · simp [relevantHeadFinset, relevantHeadXFinset, relevantHeadYFinset,
            relevantHeadResidualFinset, relevantHeadConditioningFinset,
            scopeOnlyConditioning, hRC, hYRC, hAll, hvRel, hX, hY, hR]
  · intro hv
    have hv' := hv
    simp only [Finset.mem_disjUnion, relevantHeadXFinset, relevantHeadYFinset,
      relevantHeadResidualFinset, relevantHeadConditioningFinset,
      scopeOnlyConditioning, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
    have hvRel : v ∈ DSeparation.relevantVertices bn.graph X Y Z := by
      rcases hv' with hX | hrest
      · exact hX.1
      · rcases hrest with hY | hrest
        · exact hY.1
        · rcases hrest with hR | hC
          · exact hR.1
          · exact hC.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvRel⟩

/-- The product of `nodeProb`s over all relevant heads splits into the four
reachable/conditioning blocks. -/
theorem relevantHeadProd_eq_blockProducts
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (x : bn.JointSpace) :
    ∏ v ∈ relevantHeadFinset bn X Y Z, cpt.nodeProb x v =
      (∏ v ∈ relevantHeadXFinset bn X Y Z, cpt.nodeProb x v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z, cpt.nodeProb x v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z, cpt.nodeProb x v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z, cpt.nodeProb x v)) := by
  classical
  let hRC :=
    relevantHeadResidualFinset_disjoint_relevantHeadConditioningFinset bn X Y Z
  let hYRC :
      Disjoint (relevantHeadYFinset bn X Y Z)
        ((relevantHeadResidualFinset bn X Y Z).disjUnion
          (relevantHeadConditioningFinset bn X Y Z) hRC) := by
    rw [Finset.disjoint_disjUnion_right]
    exact
      ⟨relevantHeadYFinset_disjoint_relevantHeadResidualFinset bn X Y Z hirr,
        relevantHeadYFinset_disjoint_relevantHeadConditioningFinset bn X Y Z⟩
  let hAll :
      Disjoint (relevantHeadXFinset bn X Y Z)
        ((relevantHeadYFinset bn X Y Z).disjUnion
          ((relevantHeadResidualFinset bn X Y Z).disjUnion
            (relevantHeadConditioningFinset bn X Y Z) hRC) hYRC) := by
    rw [Finset.disjoint_disjUnion_right]
    exact
      ⟨relevantHeadXFinset_disjoint_relevantHeadYFinset
          bn X Y Z hirr hXY hSep,
        by
          rw [Finset.disjoint_disjUnion_right]
          exact
            ⟨relevantHeadXFinset_disjoint_relevantHeadResidualFinset
                bn X Y Z hirr,
              relevantHeadXFinset_disjoint_relevantHeadConditioningFinset
                bn X Y Z⟩⟩
  rw [relevantHeadFinset_eq_block_disjUnion bn X Y Z hirr hXY hSep]
  rw [Finset.prod_disjUnion hAll, Finset.prod_disjUnion hYRC, Finset.prod_disjUnion hRC]

/-- `jointWeight` splits into the product over relevant and irrelevant heads. -/
theorem jointWeight_eq_relevant_irrelevant_prod
    (cpt : bn.DiscreteCPT) (X Y Z : Set V) (x : bn.JointSpace) :
    cpt.jointWeight x =
      (∏ v ∈ relevantHeadFinset bn X Y Z, cpt.nodeProb x v) *
        ∏ v ∈ irrelevantHeadFinset bn X Y Z, cpt.nodeProb x v := by
  symm
  simpa [relevantHeadFinset, irrelevantHeadFinset, DiscreteCPT.jointWeight] using
    (Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
      (p := fun v => v ∈ DSeparation.relevantVertices bn.graph X Y Z)
      (f := fun v => cpt.nodeProb x v))

/-- `jointWeight` splits into `X`-block, `Y`-block, residual, conditioning,
and irrelevant head factors. -/
theorem jointWeight_eq_block_irrelevant_prod
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (x : bn.JointSpace) :
    cpt.jointWeight x =
      ((∏ v ∈ relevantHeadXFinset bn X Y Z, cpt.nodeProb x v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z, cpt.nodeProb x v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z, cpt.nodeProb x v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z, cpt.nodeProb x v))) *
        ∏ v ∈ irrelevantHeadFinset bn X Y Z, cpt.nodeProb x v := by
  calc
    cpt.jointWeight x
      = (∏ v ∈ relevantHeadFinset bn X Y Z, cpt.nodeProb x v) *
          ∏ v ∈ irrelevantHeadFinset bn X Y Z, cpt.nodeProb x v :=
        jointWeight_eq_relevant_irrelevant_prod bn cpt X Y Z x
    _ = ((∏ v ∈ relevantHeadXFinset bn X Y Z, cpt.nodeProb x v) *
          ((∏ v ∈ relevantHeadYFinset bn X Y Z, cpt.nodeProb x v) *
            ((∏ v ∈ relevantHeadResidualFinset bn X Y Z, cpt.nodeProb x v) *
              ∏ v ∈ relevantHeadConditioningFinset bn X Y Z, cpt.nodeProb x v))) *
          ∏ v ∈ irrelevantHeadFinset bn X Y Z, cpt.nodeProb x v := by
        rw [relevantHeadProd_eq_blockProducts bn cpt X Y Z hirr hXY hSep x]

/-- Finite-sum rearrangement for three multiplicatively separated block
families. This is the algebraic core used to turn a blockwise factorization of
`jointWeight` into the atomic event identity for separated constraint blocks. -/
theorem fintype_sum_mul_sum_mul_sum {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) (h : γ → ℝ≥0∞) :
    (∑ a, f a) * ((∑ b, g b) * (∑ c, h c)) =
      ∑ a, ∑ b, ∑ c, f a * (g b * h c) := by
  calc
    (∑ a, f a) * ((∑ b, g b) * (∑ c, h c))
        = ((∑ a, f a) * (∑ b, g b)) * (∑ c, h c) := by ac_rfl
    _ = (∑ a, ∑ b, f a * g b) * (∑ c, h c) := by
          rw [Fintype.sum_mul_sum]
    _ = (∑ p : α × β, f p.1 * g p.2) * (∑ c, h c) := by
          rw [← Fintype.sum_prod_type']
    _ = ∑ p : α × β, ∑ c, (f p.1 * g p.2) * h c := by
          rw [Fintype.sum_mul_sum]
    _ = ∑ a, ∑ b, ∑ c, f a * (g b * h c) := by
          rw [Fintype.sum_prod_type]
          simp [mul_assoc]

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

This theorem is the concrete marginalization engine for discrete CPT products.
It used to be the place where one might be tempted to introduce an axiom, but
the proof below now carries the sink-elimination argument directly: eliminate
acyclic sinks one at a time, use CPT normalization at each sink, and recurse on
the remaining finite vertex set. -/

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

/-- Summing `jointWeight` over all assignments to the irrelevant vertices
collapses to the product of the relevant block factors. This is the first
block-factorization bridge: the irrelevant tail of the BN contributes only a
unit telescoping sum once the relevant coordinates are fixed. -/
theorem sum_irrelevant_jointWeight_eq_relevantBlockProducts
    (cpt : bn.DiscreteCPT) (X Y Z : Set V)
    (hirr : ∀ v : V, ¬bn.graph.edges v v)
    (hXY : Disjoint X Y)
    (hSep : DSeparation.SeparatedInMoralAncestral bn.graph X Y Z)
    (x : bn.JointSpace) :
    (∑ xI : (∀ d : ↥(irrelevantHeadFinset bn X Y Z), bn.stateSpace d),
        cpt.jointWeight
          (patchConfig bn x (irrelevantHeadFinset bn X Y Z) xI))
      =
      (∏ v ∈ relevantHeadXFinset bn X Y Z, cpt.nodeProb x v) *
        ((∏ v ∈ relevantHeadYFinset bn X Y Z, cpt.nodeProb x v) *
          ((∏ v ∈ relevantHeadResidualFinset bn X Y Z, cpt.nodeProb x v) *
            ∏ v ∈ relevantHeadConditioningFinset bn X Y Z, cpt.nodeProb x v)) := by
  classical
  let D := irrelevantHeadFinset bn X Y Z
  let Crel :=
    (∏ v ∈ relevantHeadXFinset bn X Y Z, cpt.nodeProb x v) *
      ((∏ v ∈ relevantHeadYFinset bn X Y Z, cpt.nodeProb x v) *
        ((∏ v ∈ relevantHeadResidualFinset bn X Y Z, cpt.nodeProb x v) *
          ∏ v ∈ relevantHeadConditioningFinset bn X Y Z, cpt.nodeProb x v))
  have hPatchRelevant :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d) {s : V},
        s ∈ DSeparation.relevantVertices bn.graph X Y Z →
          patchConfig bn x D xI s = x s := by
    intro xI s hs
    apply patchConfig_outside (bn := bn) (x := x) (D := D) (xD := xI) (v := s)
    intro hsD
    exact (Finset.mem_filter.mp hsD).2 hs
  have hPatchX :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        ∀ s, s ∈ DSeparation.xReachableBlock bn.graph X Y Z ∪ Z →
          patchConfig bn x D xI s = x s := by
    intro xI s hs
    rcases hs with hsX | hsZ
    · exact hPatchRelevant xI hsX.1.1
    · exact hPatchRelevant xI (DSeparation.z_in_relevant bn.graph X Y Z hsZ)
  have hPatchY :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        ∀ s, s ∈ DSeparation.yReachableBlock bn.graph X Y Z ∪ Z →
          patchConfig bn x D xI s = x s := by
    intro xI s hs
    rcases hs with hsY | hsZ
    · exact hPatchRelevant xI hsY.1.1
    · exact hPatchRelevant xI (DSeparation.z_in_relevant bn.graph X Y Z hsZ)
  have hPatchR :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        ∀ s, s ∈ DSeparation.residualBlock bn.graph X Y Z ∪ Z →
          patchConfig bn x D xI s = x s := by
    intro xI s hs
    rcases hs with hsR | hsZ
    · exact hPatchRelevant xI hsR.1.1
    · exact hPatchRelevant xI (DSeparation.z_in_relevant bn.graph X Y Z hsZ)
  have hPatchZ :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        ∀ s, s ∈ Z →
          patchConfig bn x D xI s = x s := by
    intro xI s hsZ
    exact hPatchRelevant xI (DSeparation.z_in_relevant bn.graph X Y Z hsZ)
  have hBlockX :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        ∏ v ∈ relevantHeadXFinset bn X Y Z,
            cpt.nodeProb (patchConfig bn x D xI) v
          =
        ∏ v ∈ relevantHeadXFinset bn X Y Z, cpt.nodeProb x v := by
    intro xI
    exact prod_relevantHeadXFinset_eq_of_agree
      (bn := bn) (cpt := cpt) X Y Z hirr (patchConfig bn x D xI) x (hPatchX xI)
  have hBlockY :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        ∏ v ∈ relevantHeadYFinset bn X Y Z,
            cpt.nodeProb (patchConfig bn x D xI) v
          =
        ∏ v ∈ relevantHeadYFinset bn X Y Z, cpt.nodeProb x v := by
    intro xI
    exact prod_relevantHeadYFinset_eq_of_agree
      (bn := bn) (cpt := cpt) X Y Z hirr (patchConfig bn x D xI) x (hPatchY xI)
  have hBlockR :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        ∏ v ∈ relevantHeadResidualFinset bn X Y Z,
            cpt.nodeProb (patchConfig bn x D xI) v
          =
        ∏ v ∈ relevantHeadResidualFinset bn X Y Z, cpt.nodeProb x v := by
    intro xI
    exact prod_relevantHeadResidualFinset_eq_of_agree
      (bn := bn) (cpt := cpt) X Y Z hirr (patchConfig bn x D xI) x (hPatchR xI)
  have hBlockZ :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
            cpt.nodeProb (patchConfig bn x D xI) v
          =
        ∏ v ∈ relevantHeadConditioningFinset bn X Y Z, cpt.nodeProb x v := by
    intro xI
    exact prod_relevantHeadConditioningFinset_eq_of_agree
      (bn := bn) (cpt := cpt) X Y Z (patchConfig bn x D xI) x (hPatchZ xI)
  have hJoint :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        cpt.jointWeight (patchConfig bn x D xI)
          =
        Crel * ∏ v ∈ D, cpt.nodeProb (patchConfig bn x D xI) v := by
    intro xI
    calc
      cpt.jointWeight (patchConfig bn x D xI)
          =
        ((∏ v ∈ relevantHeadXFinset bn X Y Z,
            cpt.nodeProb (patchConfig bn x D xI) v) *
          ((∏ v ∈ relevantHeadYFinset bn X Y Z,
              cpt.nodeProb (patchConfig bn x D xI) v) *
            ((∏ v ∈ relevantHeadResidualFinset bn X Y Z,
                cpt.nodeProb (patchConfig bn x D xI) v) *
              ∏ v ∈ relevantHeadConditioningFinset bn X Y Z,
                cpt.nodeProb (patchConfig bn x D xI) v))) *
          ∏ v ∈ D, cpt.nodeProb (patchConfig bn x D xI) v := by
            simpa [D] using
              jointWeight_eq_block_irrelevant_prod
                (bn := bn) (cpt := cpt) X Y Z hirr hXY hSep (patchConfig bn x D xI)
      _ =
        Crel * ∏ v ∈ D, cpt.nodeProb (patchConfig bn x D xI) v := by
          simp [Crel, hBlockX xI, hBlockY xI, hBlockR xI, hBlockZ xI]
  have hProdAttach :
      ∀ (xI : ∀ d : ↥D, bn.stateSpace d),
        (∏ v ∈ D, cpt.nodeProb (patchConfig bn x D xI) v)
          =
        ∏ v : ↥D, cpt.nodeProb (patchConfig bn x D xI) v := by
    intro xI
    simpa using
      (Finset.prod_attach (s := D)
        (f := fun d => cpt.nodeProb (patchConfig bn x D xI) d)).symm
  calc
    (∑ xI : (∀ d : ↥D, bn.stateSpace d),
        cpt.jointWeight (patchConfig bn x D xI))
        =
      ∑ xI : (∀ d : ↥D, bn.stateSpace d),
        Crel * ∏ v ∈ D, cpt.nodeProb (patchConfig bn x D xI) v := by
          refine Finset.sum_congr rfl ?_
          intro xI _
          exact hJoint xI
    _ =
      ∑ xI : (∀ d : ↥D, bn.stateSpace d),
        Crel * ∏ v : ↥D, cpt.nodeProb (patchConfig bn x D xI) v := by
          refine Finset.sum_congr rfl ?_
          intro xI _
          rw [hProdAttach xI]
    _ =
      Crel *
        ∑ xI : (∀ d : ↥D, bn.stateSpace d),
          ∏ v : ↥D, cpt.nodeProb (patchConfig bn x D xI) v := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = Crel * 1 := by
          have htel := telescoping_sum (bn := bn) (cpt := cpt) (D := D) (x := x)
          simpa using congrArg (fun t => Crel * t) htel
    _ = Crel := by simp

set_option maxHeartbeats 800000


end Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov
