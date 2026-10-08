import Mettapedia.GSLT.Causality.DoCalculus.DoRules

/-!
# Intervention on a finite set of variables

`do` on one variable is already the truncated factorization. The same identity
holds for a finite set: the joint of the Bayesian network on the graph with
every arrow into the set deleted, with each intervened variable replaced by a
point mass, is the g-formula of that set.

Doing `X` and then `Z`, for disjoint `X` and `Z`, is the same weight as doing
`Z` and then `X`, and both are the g-formula of the union. The two mutilated
graphs delete the same edges.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open scoped BigOperators ENNReal

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]

variable (hAcyclic : graph.IsAcyclic)
variable {β : Type} [Fintype β] [DecidableEq β] [MeasurableSpace β]

instance deleteIncoming_decidableRel (G : DirectedGraph V) [DecidableRel G.edges]
    (forbidden : Finset V) :
    DecidableRel (deleteIncoming G forbidden).edges := fun _ _ => by
  unfold deleteIncoming
  infer_instance

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [DecidableEq β]
  [MeasurableSpace β] in
lemma deleteIncoming_deleteIncoming_iff (X Z : Finset V) (u v : V) :
    (deleteIncoming (deleteIncoming graph X) Z).edges u v ↔
      (deleteIncoming graph (X ∪ Z)).edges u v := by
  simp only [deleteIncoming, Finset.notMem_union]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma doFinset_eq_none {S : Finset V} {value : V → β} {v : V} (hv : v ∉ S) :
    doFinset S value v = none := by
  simp [doFinset, hv]

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma doFinset_eq_some {S : Finset V} {value : V → β} {v : V} (hv : v ∈ S) :
    doFinset S value v = some (value v) := by
  simp [doFinset, hv]

/-- Point masses on `forbidden`, original tables elsewhere.

Deleting arrows into `forbidden` does not change the parents of a vertex
outside the set, so those tables are copied.
-/
noncomputable def intervenedFinsetCPT
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (forbidden : Finset V) (value : V → β) :
    (network (β := β) (deleteIncoming graph forbidden)
      (deleteIncoming_acyclic graph hAcyclic forbidden)).DiscreteCPT where
  cpt v pa :=
    if hv : v ∈ forbidden then
      PMF.pure (value v)
    else
      cpt.cpt v fun u hu =>
        pa u <| by
          simp only [BayesianNetwork.parents] at hu ⊢
          exact (parents_eq_of_not_forbidden graph hv).symm ▸ hu

omit [Fintype β] in
lemma intervenedFinset_nodeProb_eq_truncatedFactor
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (forbidden : Finset V) (value : V → β) (f : V → β) (v : V) :
    DiscreteCPT.nodeProb (intervenedFinsetCPT graph hAcyclic cpt forbidden value) f v =
      truncatedFactor graph hAcyclic cpt (doFinset forbidden value) f v := by
  unfold DiscreteCPT.nodeProb DiscreteCPT.parentAssignOfConfig intervenedFinsetCPT
    truncatedFactor
  by_cases hv : v ∈ forbidden
  · simp [hv, doFinset]
  · simp only [dif_neg hv, doFinset_eq_none hv, cptAt_eq_nodeProb]
    unfold DiscreteCPT.nodeProb DiscreteCPT.parentAssignOfConfig
    rfl

omit [Fintype β] in
/-- **A finite intervention is the truncated factorization of that set.** -/
theorem intervenedFinset_jointWeight_eq_truncatedWeight
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (forbidden : Finset V) (value : V → β) (f : V → β) :
    (intervenedFinsetCPT graph hAcyclic cpt forbidden value).jointWeight f =
      truncatedWeight graph hAcyclic cpt (doFinset forbidden value) f := by
  unfold DiscreteCPT.jointWeight truncatedWeight
  refine Finset.prod_congr rfl fun v _ => ?_
  exact intervenedFinset_nodeProb_eq_truncatedFactor
    graph hAcyclic cpt forbidden value f v

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma doOne_eq_doFinset_singleton (treatment : V) (value : β) :
    doOne treatment value = doFinset ({treatment} : Finset V) (fun _ => value) := by
  funext v
  by_cases hv : v = treatment
  · simp [doOne, doFinset, hv]
  · simp [doOne, doFinset, hv]

omit [Fintype β] in
/-- The one-variable intervention is the finset intervention on a singleton. -/
theorem intervenedCPT_jointWeight_eq_finset_singleton
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (value : β) (f : V → β) :
    (intervenedCPT graph hAcyclic cpt treatment value).jointWeight f =
      (intervenedFinsetCPT graph hAcyclic cpt {treatment} (fun _ => value)).jointWeight f := by
  rw [intervened_jointWeight_eq_truncatedWeight,
    intervenedFinset_jointWeight_eq_truncatedWeight, doOne_eq_doFinset_singleton]

/-- Set `X` to `x` and, off `X`, set `Z` to `z`. -/
def doTwo (X Z : Finset V) (x z : V → β) : V → Option β :=
  fun v => if v ∈ X then some (x v) else if v ∈ Z then some (z v) else none

/-- Values used by the simultaneous intervention on `X ∪ Z`: `X` keeps `x`. -/
def mergeAssign (X : Finset V) (x z : V → β) : V → β :=
  fun v => if v ∈ X then x v else z v

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [DecidableEq β]
  [MeasurableSpace β] in
lemma doTwo_eq_doFinset_union {X Z : Finset V} {x z : V → β}
    (hdisj : Disjoint X Z) :
    doTwo X Z x z = doFinset (X ∪ Z) (mergeAssign X x z) := by
  funext v
  by_cases hX : v ∈ X
  · have hZ : v ∉ Z := fun hZ => Finset.disjoint_left.mp hdisj hX hZ
    simp [doTwo, doFinset, mergeAssign, hX, hZ, Finset.mem_union]
  · by_cases hZ : v ∈ Z
    · have hmerge : mergeAssign X x z v = z v := by
        unfold mergeAssign
        simp [hX]
      simp [doTwo, doFinset, hmerge, hX, hZ, Finset.mem_union]
    · simp [doTwo, doFinset, hX, hZ, Finset.mem_union]

omit [Fintype V] [DecidableRel graph.edges] [Fintype β] [DecidableEq β]
  [MeasurableSpace β] in
lemma doTwo_comm {X Z : Finset V} {x z : V → β} (hdisj : Disjoint X Z) :
    doTwo X Z x z = doTwo Z X z x := by
  funext v
  by_cases hX : v ∈ X
  · have hZ : v ∉ Z := fun hZ => Finset.disjoint_left.mp hdisj hX hZ
    simp [doTwo, hX, hZ]
  · by_cases hZ : v ∈ Z
    · simp [doTwo, hX, hZ]
    · simp [doTwo, hX, hZ]

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma doFinset_eq_doTwo_of_not_mem {X Z : Finset V} {x z : V → β} {v : V}
    (hv : v ∉ Z) :
    doFinset X x v = doTwo X Z x z v := by
  by_cases hX : v ∈ X
  · simp [doFinset, doTwo, hX]
  · simp [doFinset, doTwo, hX, hv]

omit [DecidableEq V] [Fintype β] in
lemma truncatedFactor_congr_assignment
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {a₁ a₂ : V → Option β} {f : V → β} {v : V} (h : a₁ v = a₂ v) :
    truncatedFactor graph hAcyclic cpt a₁ f v =
      truncatedFactor graph hAcyclic cpt a₂ f v := by
  simp [truncatedFactor, h]

omit [Fintype β] in
/-- One factor after doing `X` and then `Z` is the factor of the merged g-formula. -/
lemma do_then_do_factor
    {X Z : Finset V} (hdisj : Disjoint X Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z f : V → β) (v : V) :
    truncatedFactor (deleteIncoming graph X)
        (deleteIncoming_acyclic graph hAcyclic X)
        (intervenedFinsetCPT graph hAcyclic cpt X x)
        (doFinset Z z) f v =
      truncatedFactor graph hAcyclic cpt (doTwo X Z x z) f v := by
  by_cases hvZ : v ∈ Z
  · have hvX : v ∉ X := fun hvX => Finset.disjoint_left.mp hdisj hvX hvZ
    have hL : doFinset Z z v = some (z v) := doFinset_eq_some hvZ
    have hR : doTwo X Z x z v = some (z v) := by simp [doTwo, hvX, hvZ]
    simp [truncatedFactor, hL, hR]
  · have hfree : doFinset Z z v = none := doFinset_eq_none hvZ
    have hagree : doFinset X x v = doTwo X Z x z v :=
      doFinset_eq_doTwo_of_not_mem hvZ
    have hnode :
        truncatedFactor (deleteIncoming graph X)
            (deleteIncoming_acyclic graph hAcyclic X)
            (intervenedFinsetCPT graph hAcyclic cpt X x)
            (doFinset Z z) f v =
          DiscreteCPT.nodeProb (intervenedFinsetCPT graph hAcyclic cpt X x) f v := by
      simp [truncatedFactor, hfree, cptAt_eq_nodeProb]
    rw [hnode, intervenedFinset_nodeProb_eq_truncatedFactor,
      truncatedFactor_congr_assignment graph hAcyclic cpt hagree]

omit [Fintype β] in
/-- **Doing `X` and then `Z` is the merged truncated factorization.**

`X` and `Z` are disjoint, so the second intervention does not overwrite the
first. The resulting weight is the g-formula that sets both.
-/
theorem do_then_do_eq_truncatedWeight
    {X Z : Finset V} (hdisj : Disjoint X Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z f : V → β) :
    (intervenedFinsetCPT (deleteIncoming graph X)
        (deleteIncoming_acyclic graph hAcyclic X)
        (intervenedFinsetCPT graph hAcyclic cpt X x) Z z).jointWeight f =
      truncatedWeight graph hAcyclic cpt (doTwo X Z x z) f := by
  rw [intervenedFinset_jointWeight_eq_truncatedWeight]
  unfold truncatedWeight
  refine Finset.prod_congr rfl fun v _ => ?_
  exact do_then_do_factor graph hAcyclic hdisj cpt x z f v

omit [Fintype β] in
/-- **The two orders agree, and both agree with one intervention on the union.** -/
theorem do_then_do_comm_eq_union
    {X Z : Finset V} (hdisj : Disjoint X Z)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (x z f : V → β) :
    (intervenedFinsetCPT (deleteIncoming graph X)
        (deleteIncoming_acyclic graph hAcyclic X)
        (intervenedFinsetCPT graph hAcyclic cpt X x) Z z).jointWeight f =
      (intervenedFinsetCPT (deleteIncoming graph Z)
          (deleteIncoming_acyclic graph hAcyclic Z)
          (intervenedFinsetCPT graph hAcyclic cpt Z z) X x).jointWeight f ∧
    (intervenedFinsetCPT (deleteIncoming graph X)
        (deleteIncoming_acyclic graph hAcyclic X)
        (intervenedFinsetCPT graph hAcyclic cpt X x) Z z).jointWeight f =
      (intervenedFinsetCPT graph hAcyclic cpt (X ∪ Z) (mergeAssign X x z)).jointWeight f := by
  constructor
  · rw [do_then_do_eq_truncatedWeight graph hAcyclic hdisj cpt x z f,
      do_then_do_eq_truncatedWeight graph hAcyclic hdisj.symm cpt z x f,
      doTwo_comm hdisj]
  · rw [do_then_do_eq_truncatedWeight graph hAcyclic hdisj cpt x z f,
      intervenedFinset_jointWeight_eq_truncatedWeight graph hAcyclic cpt
        (X ∪ Z) (mergeAssign X x z) f,
      doTwo_eq_doFinset_union hdisj]

end Mettapedia.GSLT.Causality.DoCalculus
