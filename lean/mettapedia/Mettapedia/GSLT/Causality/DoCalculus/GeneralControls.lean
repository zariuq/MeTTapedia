import Mettapedia.GSLT.Causality.DoCalculus.BowArc
import Mettapedia.GSLT.Causality.DoCalculus.CheckerRules

/-!
# Controls for the general do-calculus rules

Rule 2's parent condition can fail while the checker still accepts the
separation premise. The example is `prior → mediator → response ← exposure`:
`prior` is a parent of `mediator` outside `{exposure, mediator}`. Rule 3's
no-outside-child condition can fail while `Z(W)` is a proper subset. The
example is `source → middle → response` with `spare` isolated:
`Z(W) = {spare}`.

Each rule also has a graph where the separation fails and the conditional
masses disagree. The fork `response ← confounder → copied` makes the rule-2
ratios `1/2` and `1`. The edge `cause → effect` makes the rule-3 ratios `1`
and `1/2`.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
open BayesianNetwork
open DirectedGraph
open DSeparation
open PMF
open scoped BigOperators ENNReal

/-! ## One positive configuration makes a slice positive -/

lemma slice_ne_zero_of_weight
    {V β : Type} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
    [MeasurableSpace β]
    {graph : DirectedGraph V} [DecidableRel graph.edges]
    (hAcyclic : graph.IsAcyclic)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (assignment : V → Option β) (S : Finset V) (anchor f0 : V → β)
    (hagree : agreesOn S anchor f0 = true)
    (hweight : truncatedWeight graph hAcyclic cpt assignment f0 ≠ 0) :
    truncSlice graph hAcyclic cpt assignment S anchor ≠ 0 := by
  intro hzero
  unfold truncSlice at hzero
  have hterm :
      (if agreesOn S anchor f0 = true then
        truncatedWeight graph hAcyclic cpt assignment f0 else 0) =
        truncatedWeight graph hAcyclic cpt assignment f0 := by
    simp [hagree]
  have hle :
      truncatedWeight graph hAcyclic cpt assignment f0 ≤
        ∑ f : V → β, if agreesOn S anchor f = true then
          truncatedWeight graph hAcyclic cpt assignment f else 0 := by
    have hsum :=
      Finset.single_le_sum
        (f := fun f : V → β => if agreesOn S anchor f = true then
          truncatedWeight graph hAcyclic cpt assignment f else 0)
        (fun _ _ => zero_le) (Finset.mem_univ f0)
    rw [hterm] at hsum
    exact hsum
  exact hweight (le_antisymm (hle.trans_eq hzero) bot_le)

/-! ## Rule 2, positive: a parent of `Z` lies outside `X ∪ Z` -/

/-- `prior → mediator → response ← exposure`. -/
inductive Med
  | prior
  | mediator
  | response
  | exposure
  deriving DecidableEq

instance : Fintype Med where
  elems := {Med.prior, Med.mediator, Med.response, Med.exposure}
  complete := by intro vertex; cases vertex <;> simp

def medGraph : DirectedGraph Med where
  edges source target :=
    (source = .prior ∧ target = .mediator) ∨
      (source = .mediator ∧ target = .response) ∨
        (source = .exposure ∧ target = .response)

instance : DecidableRel medGraph.edges := fun _ _ => by
  unfold medGraph
  infer_instance

def medRank : Med → ℕ
  | .prior => 0
  | .exposure => 0
  | .mediator => 1
  | .response => 2

lemma med_edge_increases {source target : Med} (hedge : medGraph.edges source target) :
    medRank source < medRank target := by
  cases source <;> cases target <;> simp [medGraph, medRank] at hedge ⊢

lemma med_reachable_rank {source target : Med} (hreach : medGraph.Reachable source target) :
    medRank source ≤ medRank target := by
  induction hreach with
  | refl => exact le_rfl
  | step hedge _ ih =>
      exact le_trans (Nat.le_of_lt (med_edge_increases hedge)) ih

lemma medAcyclic : medGraph.IsAcyclic := by
  intro vertex ⟨src, hedge, hreach⟩
  exact lt_irrefl _ <|
    lt_of_lt_of_le (med_edge_increases hedge) (med_reachable_rank hreach)

lemma med_prior_parent :
    Med.prior ∈ (network (β := Bool) medGraph medAcyclic).parents Med.mediator := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, medGraph]

lemma med_mediator_parent :
    Med.mediator ∈ (network (β := Bool) medGraph medAcyclic).parents Med.response := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, medGraph]

/-- `mediator` copies `prior`, and `response` copies `mediator`. -/
noncomputable def medCPT : (network (β := Bool) medGraph medAcyclic).DiscreteCPT where
  cpt := fun vertex pa =>
    match vertex with
    | .prior => fairBit
    | .exposure => fairBit
    | .mediator => PMF.pure (pa .prior med_prior_parent)
    | .response => PMF.pure (pa .mediator med_mediator_parent)

lemma prod_med (g : Med → ℝ≥0∞) :
    ∏ vertex, g vertex =
      g .prior * (g .mediator * (g .response * g .exposure)) := by
  have huniv : (Finset.univ : Finset Med) =
      insert .prior (insert .mediator (insert .response {.exposure})) := by
    ext vertex
    cases vertex <;> simp
  rw [huniv, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_insert (by simp), Finset.prod_singleton]

lemma med_doX_true_weight :
    truncatedWeight medGraph medAcyclic medCPT
        (doFinset ({.exposure} : Finset Med) (fun _ => true)) (fun _ => true) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold truncatedWeight
  rw [prod_med]
  have hprior : truncatedFactor medGraph medAcyclic medCPT
      (doFinset ({.exposure} : Finset Med) (fun _ => true)) (fun _ => true) .prior =
      fairBit true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb, medCPT]
  have hmed : truncatedFactor medGraph medAcyclic medCPT
      (doFinset ({.exposure} : Finset Med) (fun _ => true)) (fun _ => true) .mediator =
      PMF.pure true true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb,
      DiscreteCPT.parentAssignOfConfig, medCPT]
  have hresp : truncatedFactor medGraph medAcyclic medCPT
      (doFinset ({.exposure} : Finset Med) (fun _ => true)) (fun _ => true) .response =
      PMF.pure true true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb,
      DiscreteCPT.parentAssignOfConfig, medCPT]
  have hexp : truncatedFactor medGraph medAcyclic medCPT
      (doFinset ({.exposure} : Finset Med) (fun _ => true)) (fun _ => true) .exposure =
      1 := by
    simp [truncatedFactor, doFinset]
  simp [hprior, hmed, hresp, hexp, fairBit_apply, PMF.pure_apply, mul_one]

lemma med_parent_outside :
    ¬ ∀ vertex ∈ ({.mediator} : Finset Med), ∀ origin,
        medGraph.edges origin vertex →
          origin ∈ ({.exposure} ∪ {.mediator} ∪ (∅ : Finset Med)) := by
  decide

private def medSide : Med → Bool
  | .prior => false
  | .mediator => false
  | .response => true
  | .exposure => true

private lemma med_gout_edge_side {u v : Med}
    (hedge : (gout medGraph {.exposure} {.mediator}).edges u v) :
    medSide u = medSide v := by
  cases u <;> cases v <;>
    simp [gout, gx, deleteOutgoing, deleteIncoming, medGraph, medSide] at hedge ⊢

private lemma med_undirected_side {u v : Med}
    (hedge : UndirectedEdge (gout medGraph {.exposure} {.mediator}) u v) :
    medSide u = medSide v := by
  rcases hedge with hdir | hrev
  · exact med_gout_edge_side hdir
  · exact (med_gout_edge_side hrev).symm

private lemma med_isTrail_side {p : List Med}
    (htrail : IsTrail (gout medGraph {.exposure} {.mediator}) p) :
    ∀ a ∈ p, ∀ b ∈ p, medSide a = medSide b :=
  IsTrail.rec
    (motive := fun p _ => ∀ a ∈ p, ∀ b ∈ p, medSide a = medSide b)
    (fun vertex a ha b hb => by
      simp at ha hb
      rw [ha, hb])
    (fun {u v : Med} {_rest : List Med} hEdge _ ih a ha b hb => by
      have hpair : medSide u = medSide v := med_undirected_side hEdge
      rcases List.mem_cons.mp ha with ha | ha
      · rcases List.mem_cons.mp hb with hb | hb
        · rw [ha, hb]
        · rw [ha]
          exact hpair.trans (ih v List.mem_cons_self b hb)
      · rcases List.mem_cons.mp hb with hb | hb
        · rw [hb]
          exact (ih a ha v List.mem_cons_self).trans hpair.symm
        · exact ih a ha b hb)
    htrail

private lemma med_mem_of_endpoints {p : List Med} {s t : Med}
    (hp : p ≠ []) (hends : PathEndpoints p = some (s, t)) : s ∈ p ∧ t ∈ p := by
  match p, hp with
  | [], hp => exact absurd rfl hp
  | [vertex], _ =>
      simp [PathEndpoints] at hends
      rcases hends with ⟨rfl, rfl⟩
      simp
  | u :: v :: rest, _ =>
      simp [PathEndpoints] at hends
      rcases hends with ⟨rfl, ht⟩
      refine ⟨by simp, ?_⟩
      have hlast : t ∈ v :: rest := by
        rw [← ht]
        exact List.getLast_mem (by simp)
      simp [hlast]

private lemma med_rule2_compatible :
    (rule2Profile {.response} {.mediator}
      ({.exposure} ∪ (∅ : Finset Med))).Compatible := by
  rw [Condition.Compatible, rule2Profile]
  intro vertex hv
  exfalso
  simp only [Finset.mem_inter, Finset.mem_singleton] at hv
  rcases hv with ⟨rfl, hv⟩
  exact (by decide : Med.response ≠ Med.mediator) hv

private lemma med_rule2_supported :
    (rule2Profile {.response} {.mediator}
      ({.exposure} ∪ (∅ : Finset Med))).Supported := by
  refine ⟨?_, ?_⟩
  · rw [rule2Profile, Finset.disjoint_left]
    intro vertex hv hvZ
    simp only [Finset.mem_singleton] at hv
    subst hv
    simp only [Finset.mem_union] at hvZ
    rcases hvZ with hvZ | hvZ
    · simp only [Finset.mem_singleton] at hvZ
      exact (by decide : Med.response ≠ Med.exposure) hvZ
    · exact Finset.notMem_empty _ hvZ
  · rw [rule2Profile, Finset.disjoint_left]
    intro vertex hv hvZ
    simp only [Finset.mem_singleton] at hv
    subst hv
    simp only [Finset.mem_union] at hvZ
    rcases hvZ with hvZ | hvZ
    · simp only [Finset.mem_singleton] at hvZ
      exact (by decide : Med.mediator ≠ Med.exposure) hvZ
    · exact Finset.notMem_empty _ hvZ

private lemma med_rule2_separated :
    DSeparatedFull (gout medGraph {.exposure} {.mediator})
      (rule2Profile {.response} {.mediator} ({.exposure} ∪ (∅ : Finset Med))).X
      (rule2Profile {.response} {.mediator} ({.exposure} ∪ (∅ : Finset Med))).Y
      (rule2Profile {.response} {.mediator} ({.exposure} ∪ (∅ : Finset Med))).Z := by
  intro x hx y hy _ htrail
  rw [rule2Profile] at hx hy
  have hxEq : x = .response := Finset.mem_singleton.mp (Finset.mem_coe.mp hx)
  have hyEq : y = .mediator := Finset.mem_singleton.mp (Finset.mem_coe.mp hy)
  subst hxEq
  subst hyEq
  rcases htrail with ⟨p, hp, hends, hact⟩
  have hmem := med_mem_of_endpoints hp hends
  have hside := med_isTrail_side (activeTrail_isTrail _ _ hact)
    .response hmem.1 .mediator hmem.2
  exact (by decide : medSide .response ≠ medSide .mediator) hside

lemma med_rule2_check :
    FiniteDSeparation.check (gout medGraph {.exposure} {.mediator})
      (rule2Profile {.response} {.mediator}
        ({.exposure} ∪ (∅ : Finset Med))) = true := by
  apply (rule2_check_iff medGraph medAcyclic {.exposure} {.response} {.mediator}
    (∅ : Finset Med)).2
  exact ⟨⟨med_rule2_compatible, med_rule2_separated⟩, med_rule2_supported⟩

private lemma med_rule2_mass :
    truncSlice medGraph medAcyclic medCPT
        (doFinset ({.exposure} ∪ {.mediator})
          (mergeAssign {.exposure} (fun _ => true) (fun _ => true)))
        ({.exposure} ∪ {.response} ∪ {.mediator} ∪ (∅ : Finset Med))
        (fun _ => true) /
      truncSlice medGraph medAcyclic medCPT
        (doFinset ({.exposure} ∪ {.mediator})
          (mergeAssign {.exposure} (fun _ => true) (fun _ => true)))
        ({.exposure} ∪ {.mediator} ∪ (∅ : Finset Med)) (fun _ => true) =
      truncSlice medGraph medAcyclic medCPT
        (doFinset ({.exposure} : Finset Med) (fun _ => true))
        ({.exposure} ∪ {.response} ∪ {.mediator} ∪ (∅ : Finset Med))
        (fun _ => true) /
      truncSlice medGraph medAcyclic medCPT
        (doFinset ({.exposure} : Finset Med) (fun _ => true))
        ({.exposure} ∪ {.mediator} ∪ (∅ : Finset Med)) (fun _ => true) := by
  have hYZ : Disjoint ({.response} : Finset Med) {.mediator} := by
    have hcomp := med_rule2_compatible
    have hsup := med_rule2_supported
    rw [rule2Profile] at hcomp hsup
    exact disjoint_X_Y_of_compatible_supported _ hcomp hsup
  have hXZ : Disjoint ({.exposure} : Finset Med) {.mediator} := by
    have hsup := med_rule2_supported
    rw [rule2Profile] at hsup
    exact _root_.disjoint_comm.mp
      (Finset.disjoint_of_subset_right Finset.subset_union_left hsup.2)
  have hsep := med_rule2_separated
  rw [rule2Profile] at hsep
  have hpos : truncSlice medGraph medAcyclic medCPT
      (doFinset ({.exposure} : Finset Med) (fun _ => true))
      ({.exposure} ∪ {.mediator} ∪ (∅ : Finset Med)) (fun _ => true) ≠ 0 := by
    apply slice_ne_zero_of_weight medAcyclic medCPT
      (doFinset ({.exposure} : Finset Med) (fun _ => true))
      ({.exposure} ∪ {.mediator} ∪ (∅ : Finset Med)) (fun _ => true) (fun _ => true)
    · simp [agreesOn]
    · rw [med_doX_true_weight]
      exact ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  exact rule2_regime (β := Bool) (graph := medGraph) (hAcyclic := medAcyclic)
    hXZ hYZ hsep medCPT (fun _ => true) (fun _ => true) (fun _ => true)
    (by intro _ _; rfl) hpos

/-- `prior` is a parent of `mediator` outside `X ∪ Z`, and the checker accepts
separation of `response` from `mediator` given `exposure`. The resulting
conditional masses agree. -/
theorem med_rule2_general :
    (¬ ∀ vertex ∈ ({.mediator} : Finset Med), ∀ source,
        medGraph.edges source vertex →
          source ∈ ({.exposure} ∪ {.mediator} ∪ (∅ : Finset Med))) ∧
      FiniteDSeparation.check (gout medGraph {.exposure} {.mediator})
        (rule2Profile {.response} {.mediator}
          ({.exposure} ∪ (∅ : Finset Med))) = true ∧
      truncSlice medGraph medAcyclic medCPT
          (doFinset ({.exposure} ∪ {.mediator})
            (mergeAssign {.exposure} (fun _ => true) (fun _ => true)))
          ({.exposure} ∪ {.response} ∪ {.mediator} ∪ (∅ : Finset Med))
          (fun _ => true) /
        truncSlice medGraph medAcyclic medCPT
          (doFinset ({.exposure} ∪ {.mediator})
            (mergeAssign {.exposure} (fun _ => true) (fun _ => true)))
          ({.exposure} ∪ {.mediator} ∪ (∅ : Finset Med)) (fun _ => true) =
        truncSlice medGraph medAcyclic medCPT
          (doFinset ({.exposure} : Finset Med) (fun _ => true))
          ({.exposure} ∪ {.response} ∪ {.mediator} ∪ (∅ : Finset Med))
          (fun _ => true) /
        truncSlice medGraph medAcyclic medCPT
          (doFinset ({.exposure} : Finset Med) (fun _ => true))
          ({.exposure} ∪ {.mediator} ∪ (∅ : Finset Med)) (fun _ => true) :=
  ⟨med_parent_outside, med_rule2_check, med_rule2_mass⟩

/-! ## Rule 2, negative: the fork stays open -/

/-- `response ← confounder → copied`. -/
inductive ForkV
  | confounder
  | copied
  | response
  deriving DecidableEq

instance : Fintype ForkV where
  elems := {ForkV.confounder, ForkV.copied, ForkV.response}
  complete := by intro vertex; cases vertex <;> simp

def forkOf (bU bZ bY : Bool) : ForkV → Bool
  | .confounder => bU
  | .copied => bZ
  | .response => bY

def forkGraph : DirectedGraph ForkV where
  edges source target :=
    (source = .confounder ∧ target = .copied) ∨
      (source = .confounder ∧ target = .response)

instance : DecidableRel forkGraph.edges := fun _ _ => by
  unfold forkGraph
  infer_instance

def forkRank : ForkV → ℕ
  | .confounder => 0
  | .copied => 1
  | .response => 1

lemma fork_edge_increases {source target : ForkV}
    (hedge : forkGraph.edges source target) :
    forkRank source < forkRank target := by
  cases source <;> cases target <;> simp [forkGraph, forkRank] at hedge ⊢

lemma fork_reachable_rank {source target : ForkV}
    (hreach : forkGraph.Reachable source target) :
    forkRank source ≤ forkRank target := by
  induction hreach with
  | refl => exact le_rfl
  | step hedge _ ih =>
      exact le_trans (Nat.le_of_lt (fork_edge_increases hedge)) ih

lemma forkAcyclic : forkGraph.IsAcyclic := by
  intro vertex ⟨src, hedge, hreach⟩
  exact lt_irrefl _ <|
    lt_of_lt_of_le (fork_edge_increases hedge) (fork_reachable_rank hreach)

lemma fork_confounder_parent_copied :
    ForkV.confounder ∈
      (network (β := Bool) forkGraph forkAcyclic).parents ForkV.copied := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, forkGraph]

lemma fork_confounder_parent_response :
    ForkV.confounder ∈
      (network (β := Bool) forkGraph forkAcyclic).parents ForkV.response := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, forkGraph]

/-- Both children copy the confounder. -/
noncomputable def forkCPT : (network (β := Bool) forkGraph forkAcyclic).DiscreteCPT where
  cpt := fun vertex pa =>
    match vertex with
    | .confounder => fairBit
    | .copied => PMF.pure (pa .confounder fork_confounder_parent_copied)
    | .response => PMF.pure (pa .confounder fork_confounder_parent_response)

lemma prod_fork (g : ForkV → ℝ≥0∞) :
    ∏ vertex, g vertex = g .confounder * (g .copied * g .response) := by
  have huniv : (Finset.univ : Finset ForkV) =
      insert .confounder (insert .copied {.response}) := by
    ext vertex
    cases vertex <;> simp
  rw [huniv, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_singleton]

lemma sum_fork (g : (ForkV → Bool) → ℝ≥0∞) :
    ∑ f, g f = ∑ bU, ∑ bZ, ∑ bY, g (forkOf bU bZ bY) := by
  let e : (ForkV → Bool) ≃ Bool × Bool × Bool :=
    { toFun := fun f => (f .confounder, f .copied, f .response)
      invFun := fun p => forkOf p.1 p.2.1 p.2.2
      left_inv := by
        intro f
        ext vertex
        cases vertex <;> rfl
      right_inv := by
        rintro ⟨bU, bZ, bY⟩
        rfl }
  rw [← Equiv.sum_comp e.symm g]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bU _ => ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bZ _ => ?_
  refine Finset.sum_congr rfl fun bY _ => ?_
  rfl

def forkDoZ : ForkV → Option Bool
  | .confounder => none
  | .copied => some true
  | .response => none

lemma forkDoZ_eq :
    forkDoZ = doFinset ({.copied} : Finset ForkV) (fun _ => true) := by
  funext vertex
  cases vertex <;> simp [forkDoZ, doFinset]

def forkDoNone : ForkV → Option Bool := fun _ => none

lemma forkDoNone_eq :
    forkDoNone = doFinset (∅ : Finset ForkV) (fun _ => true) := by
  funext vertex
  cases vertex <;> simp [forkDoNone, doFinset]

lemma fork_node_confounder (f : ForkV → Bool) :
    DiscreteCPT.nodeProb forkCPT f .confounder = fairBit (f .confounder) := by
  simp [DiscreteCPT.nodeProb, forkCPT]

lemma fork_node_copied (f : ForkV → Bool) :
    DiscreteCPT.nodeProb forkCPT f .copied = PMF.pure (f .confounder) (f .copied) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, forkCPT]

lemma fork_node_response (f : ForkV → Bool) :
    DiscreteCPT.nodeProb forkCPT f .response =
      PMF.pure (f .confounder) (f .response) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, forkCPT]

lemma fork_doZ_weight (f : ForkV → Bool) :
    truncatedWeight forkGraph forkAcyclic forkCPT forkDoZ f =
      fairBit (f .confounder) *
        ((if f .copied = true then 1 else 0) *
          PMF.pure (f .confounder) (f .response)) := by
  unfold truncatedWeight
  rw [prod_fork]
  have hconf : truncatedFactor forkGraph forkAcyclic forkCPT forkDoZ f .confounder =
      fairBit (f .confounder) := by
    simp [truncatedFactor, forkDoZ, cptAt_eq_nodeProb, fork_node_confounder]
  have hcopy : truncatedFactor forkGraph forkAcyclic forkCPT forkDoZ f .copied =
      if f .copied = true then 1 else 0 := by
    simp [truncatedFactor, forkDoZ]
  have hresp : truncatedFactor forkGraph forkAcyclic forkCPT forkDoZ f .response =
      PMF.pure (f .confounder) (f .response) := by
    simp [truncatedFactor, forkDoZ, cptAt_eq_nodeProb, fork_node_response]
  simp [hconf, hcopy, hresp]

lemma fork_obs_weight (f : ForkV → Bool) :
    truncatedWeight forkGraph forkAcyclic forkCPT forkDoNone f =
      fairBit (f .confounder) *
        (PMF.pure (f .confounder) (f .copied) *
          PMF.pure (f .confounder) (f .response)) := by
  unfold truncatedWeight
  rw [prod_fork]
  have hconf : truncatedFactor forkGraph forkAcyclic forkCPT forkDoNone f .confounder =
      fairBit (f .confounder) := by
    simp [truncatedFactor, forkDoNone, cptAt_eq_nodeProb, fork_node_confounder]
  have hcopy : truncatedFactor forkGraph forkAcyclic forkCPT forkDoNone f .copied =
      PMF.pure (f .confounder) (f .copied) := by
    simp [truncatedFactor, forkDoNone, cptAt_eq_nodeProb, fork_node_copied]
  have hresp : truncatedFactor forkGraph forkAcyclic forkCPT forkDoNone f .response =
      PMF.pure (f .confounder) (f .response) := by
    simp [truncatedFactor, forkDoNone, cptAt_eq_nodeProb, fork_node_response]
  simp [hconf, hcopy, hresp]

noncomputable def forkMass (assignment : ForkV → Option Bool)
    (keep : (ForkV → Bool) → Bool) : ℝ≥0∞ :=
  ∑ f, if keep f = true then
    truncatedWeight forkGraph forkAcyclic forkCPT assignment f else 0

lemma fork_doZ_mass_both :
    forkMass forkDoZ (fun f => f .response && f .copied) = (2 : ℝ≥0∞)⁻¹ := by
  unfold forkMass
  rw [sum_fork]
  simp_rw [fork_doZ_weight, forkOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma fork_doZ_mass_copied :
    forkMass forkDoZ (fun f => f .copied) = 1 := by
  unfold forkMass
  rw [sum_fork]
  simp_rw [fork_doZ_weight, forkOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply, ENNReal.inv_two_add_inv_two]

lemma fork_obs_mass_both :
    forkMass forkDoNone (fun f => f .response && f .copied) = (2 : ℝ≥0∞)⁻¹ := by
  unfold forkMass
  rw [sum_fork]
  simp_rw [fork_obs_weight, forkOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma fork_obs_mass_copied :
    forkMass forkDoNone (fun f => f .copied) = (2 : ℝ≥0∞)⁻¹ := by
  unfold forkMass
  rw [sum_fork]
  simp_rw [fork_obs_weight, forkOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma fork_gout_to_confounder :
    UndirectedEdge (gout forkGraph (∅ : Finset ForkV) {.copied}) .response .confounder :=
  Or.inr ⟨⟨Or.inr ⟨rfl, rfl⟩, by decide⟩, by decide⟩

lemma fork_gout_to_copied :
    UndirectedEdge (gout forkGraph (∅ : Finset ForkV) {.copied}) .confounder .copied :=
  Or.inl ⟨⟨Or.inl ⟨rfl, rfl⟩, by decide⟩, by decide⟩

lemma fork_active :
    IsActive (gout forkGraph (∅ : Finset ForkV) {.copied}) (∅ : Set ForkV)
      ⟨.response, .confounder, .copied, fork_gout_to_confounder, fork_gout_to_copied,
        by decide⟩ := by
  intro hblocked
  rcases hblocked with ⟨_, hb⟩ | ⟨hcol, _, _⟩
  · simp at hb
  · simp [IsCollider, gout, gx, deleteOutgoing, deleteIncoming, forkGraph] at hcol

/-- The fork is an active trail after the arrows out of `copied` are deleted,
and the conditional masses are `1/2` and `1`. -/
theorem fork_rule2_fails :
    (¬ DSeparatedFull (gout forkGraph ∅ {.copied})
        ({.response} : Set ForkV) ({.copied} : Set ForkV) (∅ : Set ForkV)) ∧
      forkMass forkDoZ (fun f => f .response && f .copied) /
          forkMass forkDoZ (fun f => f .copied) ≠
        forkMass forkDoNone (fun f => f .response && f .copied) /
          forkMass forkDoNone (fun f => f .copied) := by
  refine ⟨?_, ?_⟩
  · intro hsep
    have htrail : HasActiveTrail (gout forkGraph ∅ {.copied}) (∅ : Set ForkV)
        .response .copied :=
      ⟨[.response, .confounder, .copied], List.cons_ne_nil _ _, by simp [PathEndpoints],
        ActiveTrail.cons fork_gout_to_confounder fork_gout_to_copied (by decide)
          fork_active (ActiveTrail.two fork_gout_to_copied)⟩
    exact hsep .response (Set.mem_singleton _) .copied (Set.mem_singleton _)
      (by decide) htrail
  · rw [fork_doZ_mass_both, fork_doZ_mass_copied, fork_obs_mass_both,
      fork_obs_mass_copied]
    have hleft : (2 : ℝ≥0∞)⁻¹ / 1 = (2 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.div_eq_inv_mul, inv_one, one_mul]
    have hright : (2 : ℝ≥0∞)⁻¹ / (2 : ℝ≥0∞)⁻¹ = 1 :=
      ENNReal.div_self (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
        (ENNReal.inv_ne_top.2 two_ne_zero)
    rw [hleft, hright]
    exact one_ne_inv_two.symm

/-! ## Rule 3, positive: `Z(W)` is a proper subset -/

/-- `source → middle → response`, and `spare` is isolated. -/
inductive Anc
  | source
  | middle
  | response
  | spare
  deriving DecidableEq

instance : Fintype Anc where
  elems := {Anc.source, Anc.middle, Anc.response, Anc.spare}
  complete := by intro vertex; cases vertex <;> simp

def ancGraph : DirectedGraph Anc where
  edges origin child :=
    (origin = .source ∧ child = .middle) ∨
      (origin = .middle ∧ child = .response)

instance : DecidableRel ancGraph.edges := fun _ _ => by
  unfold ancGraph
  infer_instance

def ancRank : Anc → ℕ
  | .source => 0
  | .spare => 0
  | .middle => 1
  | .response => 2

lemma anc_edge_increases {origin child : Anc} (hedge : ancGraph.edges origin child) :
    ancRank origin < ancRank child := by
  cases origin <;> cases child <;> simp [ancGraph, ancRank] at hedge ⊢

lemma anc_reachable_rank {origin child : Anc} (hreach : ancGraph.Reachable origin child) :
    ancRank origin ≤ ancRank child := by
  induction hreach with
  | refl => exact le_rfl
  | step hedge _ ih =>
      exact le_trans (Nat.le_of_lt (anc_edge_increases hedge)) ih

lemma ancAcyclic : ancGraph.IsAcyclic := by
  intro vertex ⟨src, hedge, hreach⟩
  exact lt_irrefl _ <|
    lt_of_lt_of_le (anc_edge_increases hedge) (anc_reachable_rank hreach)

lemma anc_source_parent :
    Anc.source ∈ (network (β := Bool) ancGraph ancAcyclic).parents Anc.middle := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, ancGraph]

lemma anc_middle_parent :
    Anc.middle ∈ (network (β := Bool) ancGraph ancAcyclic).parents Anc.response := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, ancGraph]

/-- `middle` copies `source`, and `response` copies `middle`. -/
noncomputable def ancCPT : (network (β := Bool) ancGraph ancAcyclic).DiscreteCPT where
  cpt := fun vertex pa =>
    match vertex with
    | .source => fairBit
    | .spare => fairBit
    | .middle => PMF.pure (pa .source anc_source_parent)
    | .response => PMF.pure (pa .middle anc_middle_parent)

lemma prod_anc (g : Anc → ℝ≥0∞) :
    ∏ vertex, g vertex =
      g .source * (g .middle * (g .response * g .spare)) := by
  have huniv : (Finset.univ : Finset Anc) =
      insert .source (insert .middle (insert .response {.spare})) := by
    ext vertex
    cases vertex <;> simp
  rw [huniv, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_insert (by simp), Finset.prod_singleton]

lemma anc_obs_true_weight :
    truncatedWeight ancGraph ancAcyclic ancCPT (doFinset (∅ : Finset Anc) (fun _ => true))
        (fun _ => true) =
      (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
  unfold truncatedWeight
  rw [prod_anc]
  have hsource : truncatedFactor ancGraph ancAcyclic ancCPT
      (doFinset (∅ : Finset Anc) (fun _ => true)) (fun _ => true) .source =
      fairBit true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb, ancCPT]
  have hmiddle : truncatedFactor ancGraph ancAcyclic ancCPT
      (doFinset (∅ : Finset Anc) (fun _ => true)) (fun _ => true) .middle =
      PMF.pure true true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb,
      DiscreteCPT.parentAssignOfConfig, ancCPT]
  have hresp : truncatedFactor ancGraph ancAcyclic ancCPT
      (doFinset (∅ : Finset Anc) (fun _ => true)) (fun _ => true) .response =
      PMF.pure true true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb,
      DiscreteCPT.parentAssignOfConfig, ancCPT]
  have hspare : truncatedFactor ancGraph ancAcyclic ancCPT
      (doFinset (∅ : Finset Anc) (fun _ => true)) (fun _ => true) .spare =
      fairBit true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb, ancCPT]
  simp [hsource, hmiddle, hresp, hspare, fairBit_apply, PMF.pure_apply]

lemma anc_doZ_true_weight :
    truncatedWeight ancGraph ancAcyclic ancCPT
        (doFinset ({.source, .spare} : Finset Anc) (fun _ => true)) (fun _ => true) = 1 := by
  unfold truncatedWeight
  rw [prod_anc]
  have hsource : truncatedFactor ancGraph ancAcyclic ancCPT
      (doFinset ({.source, .spare} : Finset Anc) (fun _ => true)) (fun _ => true) .source =
      1 := by
    simp [truncatedFactor, doFinset]
  have hmiddle : truncatedFactor ancGraph ancAcyclic ancCPT
      (doFinset ({.source, .spare} : Finset Anc) (fun _ => true)) (fun _ => true) .middle =
      PMF.pure true true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb,
      DiscreteCPT.parentAssignOfConfig, ancCPT]
  have hresp : truncatedFactor ancGraph ancAcyclic ancCPT
      (doFinset ({.source, .spare} : Finset Anc) (fun _ => true)) (fun _ => true) .response =
      PMF.pure true true := by
    simp [truncatedFactor, doFinset, cptAt_eq_nodeProb, DiscreteCPT.nodeProb,
      DiscreteCPT.parentAssignOfConfig, ancCPT]
  have hspare : truncatedFactor ancGraph ancAcyclic ancCPT
      (doFinset ({.source, .spare} : Finset Anc) (fun _ => true)) (fun _ => true) .spare =
      1 := by
    simp [truncatedFactor, doFinset]
  simp [hsource, hmiddle, hresp, hspare, PMF.pure_apply]

lemma anc_doZ_assign :
    doFinset ((∅ : Finset Anc) ∪ {.source, .spare})
        (mergeAssign (∅ : Finset Anc) (fun _ => true) (fun _ => true)) =
      doFinset ({.source, .spare} : Finset Anc) (fun _ => true) := by
  funext vertex
  simp [doFinset, mergeAssign]

lemma anc_z_witness :
    zOfFinset ancGraph (∅ : Finset Anc) ({.source, .spare} : Finset Anc) {.middle} =
      {.spare} := by
  decide

lemma anc_child_outside :
    ¬ ∀ origin ∈ ({.source, .spare} : Finset Anc), ∀ child,
        ancGraph.edges origin child →
          child ∈ (∅ ∪ {.source, .spare} : Finset Anc) := by
  decide

private lemma anc_not_from_spare {vertex : Anc}
    (hedge : (rule3Graph ancGraph (∅ : Finset Anc) {.source, .spare} {.middle}).edges
      .spare vertex) : False := by
  simp [rule3Graph, deleteIncoming, ancGraph] at hedge

private lemma anc_not_to_spare {vertex : Anc}
    (hedge : (rule3Graph ancGraph (∅ : Finset Anc) {.source, .spare} {.middle}).edges
      vertex .spare) : False := by
  simp [rule3Graph, deleteIncoming, ancGraph] at hedge

private lemma anc_response_out {vertex : Anc}
    (hedge : (rule3Graph ancGraph (∅ : Finset Anc) {.source, .spare} {.middle}).edges
      .response vertex) : False := by
  simp [rule3Graph, deleteIncoming, ancGraph] at hedge

private lemma anc_into_response {vertex : Anc}
    (hedge : (rule3Graph ancGraph (∅ : Finset Anc) {.source, .spare} {.middle}).edges
      vertex .response) : vertex = .middle := by
  cases vertex
  · simp [rule3Graph, deleteIncoming, ancGraph] at hedge
  · rfl
  · simp [rule3Graph, deleteIncoming, ancGraph] at hedge
  · simp [rule3Graph, deleteIncoming, ancGraph] at hedge

private lemma anc_from_response {cond : Set Anc} {p : List Anc} {target : Anc}
    (hmiddle : Anc.middle ∈ cond)
    (hact : ActiveTrail
      (rule3Graph ancGraph (∅ : Finset Anc) {.source, .spare} {.middle}) cond p)
    (hends : PathEndpoints p = some (.response, target)) :
    target = .response ∨ target = .middle :=
  ActiveTrail.rec
    (motive := fun p _ => ∀ target, PathEndpoints p = some (.response, target) →
      target = .response ∨ target = .middle)
    (fun _vertex target hends => by
      simp [PathEndpoints] at hends
      exact Or.inl (hends.1.symm.trans hends.2).symm)
    (fun {_u _v} hEdge target hends => by
      simp [PathEndpoints] at hends
      rcases hends with ⟨rfl, rfl⟩
      rcases hEdge with hdir | hrev
      · exact absurd hdir anc_response_out
      · exact Or.inr (anc_into_response hrev))
    (fun {a b _c} {_rest} hab _ _ hAct _ _ target hends => by
      simp [PathEndpoints] at hends
      rcases hends with ⟨rfl, _⟩
      rcases hab with hdir | hrev
      · exact absurd hdir anc_response_out
      · have hmid : b = Anc.middle := anc_into_response hrev
        subst hmid
        exfalso
        apply hAct
        refine Or.inl ⟨?_, ?_⟩
        · intro hcol
          simp [IsCollider, rule3Graph, deleteIncoming, ancGraph] at hcol
        · exact hmiddle)
    hact target hends

private lemma anc_rule3_compatible :
    (rule3Profile {.response} {.source, .spare}
      ((∅ : Finset Anc) ∪ {.middle})).Compatible := by
  rw [Condition.Compatible, rule3Profile]
  intro vertex hv
  exfalso
  simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_insert] at hv
  rcases hv with ⟨rfl, hv | hv⟩
  · exact (by decide : Anc.response ≠ Anc.source) hv
  · exact (by decide : Anc.response ≠ Anc.spare) hv

private lemma anc_rule3_supported :
    (rule3Profile {.response} {.source, .spare}
      ((∅ : Finset Anc) ∪ {.middle})).Supported := by
  refine ⟨?_, ?_⟩
  · rw [rule3Profile, Finset.disjoint_left]
    intro vertex hv hvZ
    simp only [Finset.mem_singleton] at hv
    subst hv
    simp only [Finset.mem_union] at hvZ
    rcases hvZ with hvZ | hvZ
    · exact Finset.notMem_empty _ hvZ
    · simp only [Finset.mem_singleton] at hvZ
      exact (by decide : Anc.response ≠ Anc.middle) hvZ
  · rw [rule3Profile, Finset.disjoint_left]
    intro vertex hv hvZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp only [Finset.mem_union] at hvZ
      rcases hvZ with hvZ | hvZ
      · exact Finset.notMem_empty _ hvZ
      · simp only [Finset.mem_singleton] at hvZ
        exact (by decide : Anc.source ≠ Anc.middle) hvZ
    · simp only [Finset.mem_union] at hvZ
      rcases hvZ with hvZ | hvZ
      · exact Finset.notMem_empty _ hvZ
      · simp only [Finset.mem_singleton] at hvZ
        exact (by decide : Anc.spare ≠ Anc.middle) hvZ

private lemma anc_rule3_separated :
    DSeparatedFull
      (rule3Graph ancGraph (∅ : Finset Anc) ({.source, .spare} : Finset Anc) {.middle})
      (rule3Profile {.response} {.source, .spare} ((∅ : Finset Anc) ∪ {.middle})).X
      (rule3Profile {.response} {.source, .spare} ((∅ : Finset Anc) ∪ {.middle})).Y
      (rule3Profile {.response} {.source, .spare} ((∅ : Finset Anc) ∪ {.middle})).Z := by
  intro x hx y hy _ htrail
  have hmiddle : Anc.middle ∈
      ((rule3Profile {.response} {.source, .spare}
        ((∅ : Finset Anc) ∪ {.middle})).Z : Set Anc) := by
    rw [rule3Profile]
    exact Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  rw [rule3Profile] at hx hy
  have hxEq : x = .response := Finset.mem_singleton.mp (Finset.mem_coe.mp hx)
  subst hxEq
  rcases htrail with ⟨_p, _hp, hends, hact⟩
  have htarget := anc_from_response hmiddle hact hends
  have hyFin : y ∈ ({.source, .spare} : Finset Anc) := Finset.mem_coe.mp hy
  have hyMem : y = .source ∨ y = .spare := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hyFin
  rcases htarget with htr | htr <;> rcases hyMem with hym | hym
  · rw [htr] at hym
    exact (by decide : Anc.response ≠ Anc.source) hym
  · rw [htr] at hym
    exact (by decide : Anc.response ≠ Anc.spare) hym
  · rw [htr] at hym
    exact (by decide : Anc.middle ≠ Anc.source) hym
  · rw [htr] at hym
    exact (by decide : Anc.middle ≠ Anc.spare) hym

lemma anc_rule3_check :
    FiniteDSeparation.check
      (rule3Graph ancGraph (∅ : Finset Anc) ({.source, .spare} : Finset Anc) {.middle})
      (rule3Profile {.response} {.source, .spare}
        ((∅ : Finset Anc) ∪ {.middle})) = true := by
  apply (rule3_check_iff ancGraph ancAcyclic (∅ : Finset Anc) {.response}
    {.source, .spare} {.middle}).2
  exact ⟨⟨anc_rule3_compatible, anc_rule3_separated⟩, anc_rule3_supported⟩

private lemma anc_rule3_mass :
    truncSlice ancGraph ancAcyclic ancCPT
        (doFinset ((∅ : Finset Anc) ∪ {.source, .spare})
          (mergeAssign (∅ : Finset Anc) (fun _ => true) (fun _ => true)))
        ((∅ : Finset Anc) ∪ {.response} ∪ {.middle}) (fun _ => true) /
      truncSlice ancGraph ancAcyclic ancCPT
        (doFinset ((∅ : Finset Anc) ∪ {.source, .spare})
          (mergeAssign (∅ : Finset Anc) (fun _ => true) (fun _ => true)))
        ((∅ : Finset Anc) ∪ {.middle}) (fun _ => true) =
      truncSlice ancGraph ancAcyclic ancCPT
        (doFinset (∅ : Finset Anc) (fun _ => true))
        ((∅ : Finset Anc) ∪ {.response} ∪ {.middle}) (fun _ => true) /
      truncSlice ancGraph ancAcyclic ancCPT
        (doFinset (∅ : Finset Anc) (fun _ => true))
        ((∅ : Finset Anc) ∪ {.middle}) (fun _ => true) := by
  have hYZ : Disjoint ({.response} : Finset Anc) {.source, .spare} := by
    have hcomp := anc_rule3_compatible
    have hsup := anc_rule3_supported
    rw [rule3Profile] at hcomp hsup
    exact disjoint_X_Y_of_compatible_supported _ hcomp hsup
  have hXZ : Disjoint (∅ : Finset Anc) {.source, .spare} :=
    Finset.disjoint_empty_left _
  have hWZ : Disjoint ({.middle} : Finset Anc) {.source, .spare} := by
    have hsup := anc_rule3_supported
    rw [rule3Profile] at hsup
    exact _root_.disjoint_comm.mp
      (Finset.disjoint_of_subset_right Finset.subset_union_right hsup.2)
  have hsep := anc_rule3_separated
  rw [rule3Graph_eq_g3] at hsep
  dsimp only [rule3Profile] at hsep
  have hpos : truncSlice ancGraph ancAcyclic ancCPT
      (doFinset (∅ : Finset Anc) (fun _ => true))
      ((∅ : Finset Anc) ∪ {.middle}) (fun _ => true) ≠ 0 := by
    apply slice_ne_zero_of_weight ancAcyclic ancCPT
      (doFinset (∅ : Finset Anc) (fun _ => true))
      ((∅ : Finset Anc) ∪ {.middle}) (fun _ => true) (fun _ => true)
    · simp [agreesOn]
    · rw [anc_obs_true_weight]
      exact mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
        (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  have hposZ : truncSlice ancGraph ancAcyclic ancCPT
      (doFinset ((∅ : Finset Anc) ∪ {.source, .spare})
        (mergeAssign (∅ : Finset Anc) (fun _ => true) (fun _ => true)))
      ((∅ : Finset Anc) ∪ {.middle}) (fun _ => true) ≠ 0 := by
    apply slice_ne_zero_of_weight ancAcyclic ancCPT
      (doFinset ((∅ : Finset Anc) ∪ {.source, .spare})
        (mergeAssign (∅ : Finset Anc) (fun _ => true) (fun _ => true)))
      ((∅ : Finset Anc) ∪ {.middle}) (fun _ => true) (fun _ => true)
    · simp [agreesOn]
    · rw [anc_doZ_assign, anc_doZ_true_weight]
      exact one_ne_zero
  exact rule3_regime (β := Bool) (graph := ancGraph) (hAcyclic := ancAcyclic)
    hXZ hYZ hWZ hsep ancCPT (fun _ => true) (fun _ => true) (fun _ => true)
    hpos hposZ

/-- `Z(W) = {spare}`, a proper subset of `{source, spare}`. The checker accepts
separation of `response` from both members of `Z` given `middle`, and the
conditional masses agree. -/
theorem anc_rule3_general :
    zOfFinset ancGraph (∅ : Finset Anc) ({.source, .spare} : Finset Anc) {.middle} =
        {.spare} ∧
      (¬ ∀ origin ∈ ({.source, .spare} : Finset Anc), ∀ child,
          ancGraph.edges origin child →
            child ∈ (∅ ∪ {.source, .spare} : Finset Anc)) ∧
      FiniteDSeparation.check
        (rule3Graph ancGraph (∅ : Finset Anc) ({.source, .spare} : Finset Anc) {.middle})
        (rule3Profile {.response} {.source, .spare}
          ((∅ : Finset Anc) ∪ {.middle})) = true ∧
      truncSlice ancGraph ancAcyclic ancCPT
          (doFinset ((∅ : Finset Anc) ∪ {.source, .spare})
            (mergeAssign (∅ : Finset Anc) (fun _ => true) (fun _ => true)))
          ((∅ : Finset Anc) ∪ {.response} ∪ {.middle}) (fun _ => true) /
        truncSlice ancGraph ancAcyclic ancCPT
          (doFinset ((∅ : Finset Anc) ∪ {.source, .spare})
            (mergeAssign (∅ : Finset Anc) (fun _ => true) (fun _ => true)))
          ((∅ : Finset Anc) ∪ {.middle}) (fun _ => true) =
        truncSlice ancGraph ancAcyclic ancCPT
          (doFinset (∅ : Finset Anc) (fun _ => true))
          ((∅ : Finset Anc) ∪ {.response} ∪ {.middle}) (fun _ => true) /
        truncSlice ancGraph ancAcyclic ancCPT
          (doFinset (∅ : Finset Anc) (fun _ => true))
          ((∅ : Finset Anc) ∪ {.middle}) (fun _ => true) :=
  ⟨anc_z_witness, anc_child_outside, anc_rule3_check, anc_rule3_mass⟩

/-! ## Rule 3, negative: `Z → Y` and `W` is empty -/

/-- `cause → effect`. -/
inductive LineV
  | cause
  | effect
  deriving DecidableEq

instance : Fintype LineV where
  elems := {LineV.cause, LineV.effect}
  complete := by intro vertex; cases vertex <;> simp

def lineOf (bZ bY : Bool) : LineV → Bool
  | .cause => bZ
  | .effect => bY

def lineGraph : DirectedGraph LineV where
  edges source target := source = .cause ∧ target = .effect

instance : DecidableRel lineGraph.edges := fun _ _ => by
  unfold lineGraph
  infer_instance

def lineRank : LineV → ℕ
  | .cause => 0
  | .effect => 1

lemma line_edge_increases {source target : LineV}
    (hedge : lineGraph.edges source target) :
    lineRank source < lineRank target := by
  cases source <;> cases target <;> simp [lineGraph, lineRank] at hedge ⊢

lemma line_reachable_rank {source target : LineV}
    (hreach : lineGraph.Reachable source target) :
    lineRank source ≤ lineRank target := by
  induction hreach with
  | refl => exact le_rfl
  | step hedge _ ih =>
      exact le_trans (Nat.le_of_lt (line_edge_increases hedge)) ih

lemma lineAcyclic : lineGraph.IsAcyclic := by
  intro vertex ⟨src, hedge, hreach⟩
  exact lt_irrefl _ <|
    lt_of_lt_of_le (line_edge_increases hedge) (line_reachable_rank hreach)

lemma line_cause_parent :
    LineV.cause ∈ (network (β := Bool) lineGraph lineAcyclic).parents LineV.effect := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, lineGraph]

/-- `effect` copies `cause`. -/
noncomputable def lineCPT : (network (β := Bool) lineGraph lineAcyclic).DiscreteCPT where
  cpt := fun vertex pa =>
    match vertex with
    | .cause => fairBit
    | .effect => PMF.pure (pa .cause line_cause_parent)

lemma prod_line (g : LineV → ℝ≥0∞) :
    ∏ vertex, g vertex = g .cause * g .effect := by
  have huniv : (Finset.univ : Finset LineV) = insert .cause {.effect} := by
    ext vertex
    cases vertex <;> simp
  rw [huniv, Finset.prod_insert (by simp), Finset.prod_singleton]

lemma sum_line (g : (LineV → Bool) → ℝ≥0∞) :
    ∑ f, g f = ∑ bZ, ∑ bY, g (lineOf bZ bY) := by
  let e : (LineV → Bool) ≃ Bool × Bool :=
    { toFun := fun f => (f .cause, f .effect)
      invFun := fun p => lineOf p.1 p.2
      left_inv := by
        intro f
        ext vertex
        cases vertex <;> rfl
      right_inv := by
        rintro ⟨bZ, bY⟩
        rfl }
  rw [← Equiv.sum_comp e.symm g]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bZ _ => ?_
  refine Finset.sum_congr rfl fun bY _ => ?_
  rfl

def lineDoZ : LineV → Option Bool
  | .cause => some true
  | .effect => none

lemma lineDoZ_eq :
    lineDoZ = doFinset ({.cause} : Finset LineV) (fun _ => true) := by
  funext vertex
  cases vertex <;> simp [lineDoZ, doFinset]

def lineDoNone : LineV → Option Bool := fun _ => none

lemma lineDoNone_eq :
    lineDoNone = doFinset (∅ : Finset LineV) (fun _ => true) := by
  funext vertex
  cases vertex <;> simp [lineDoNone, doFinset]

lemma line_node_cause (f : LineV → Bool) :
    DiscreteCPT.nodeProb lineCPT f .cause = fairBit (f .cause) := by
  simp [DiscreteCPT.nodeProb, lineCPT]

lemma line_node_effect (f : LineV → Bool) :
    DiscreteCPT.nodeProb lineCPT f .effect = PMF.pure (f .cause) (f .effect) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, lineCPT]

lemma line_doZ_weight (f : LineV → Bool) :
    truncatedWeight lineGraph lineAcyclic lineCPT lineDoZ f =
      (if f .cause = true then 1 else 0) * PMF.pure (f .cause) (f .effect) := by
  unfold truncatedWeight
  rw [prod_line]
  have hcause : truncatedFactor lineGraph lineAcyclic lineCPT lineDoZ f .cause =
      if f .cause = true then 1 else 0 := by
    simp [truncatedFactor, lineDoZ]
  have heffect : truncatedFactor lineGraph lineAcyclic lineCPT lineDoZ f .effect =
      PMF.pure (f .cause) (f .effect) := by
    simp [truncatedFactor, lineDoZ, cptAt_eq_nodeProb, line_node_effect]
  simp [hcause, heffect]

lemma line_obs_weight (f : LineV → Bool) :
    truncatedWeight lineGraph lineAcyclic lineCPT lineDoNone f =
      fairBit (f .cause) * PMF.pure (f .cause) (f .effect) := by
  unfold truncatedWeight
  rw [prod_line]
  have hcause : truncatedFactor lineGraph lineAcyclic lineCPT lineDoNone f .cause =
      fairBit (f .cause) := by
    simp [truncatedFactor, lineDoNone, cptAt_eq_nodeProb, line_node_cause]
  have heffect : truncatedFactor lineGraph lineAcyclic lineCPT lineDoNone f .effect =
      PMF.pure (f .cause) (f .effect) := by
    simp [truncatedFactor, lineDoNone, cptAt_eq_nodeProb, line_node_effect]
  simp [hcause, heffect]

noncomputable def lineMass (assignment : LineV → Option Bool)
    (keep : (LineV → Bool) → Bool) : ℝ≥0∞ :=
  ∑ f, if keep f = true then
    truncatedWeight lineGraph lineAcyclic lineCPT assignment f else 0

lemma line_doZ_mass_effect :
    lineMass lineDoZ (fun f => f .effect) = 1 := by
  unfold lineMass
  rw [sum_line]
  simp_rw [line_doZ_weight, lineOf, sum_bool]
  simp [PMF.pure_apply]

lemma line_doZ_mass_all :
    lineMass lineDoZ (fun _ => true) = 1 := by
  unfold lineMass
  rw [sum_line]
  simp_rw [line_doZ_weight, lineOf, sum_bool]
  simp [PMF.pure_apply]

lemma line_obs_mass_effect :
    lineMass lineDoNone (fun f => f .effect) = (2 : ℝ≥0∞)⁻¹ := by
  unfold lineMass
  rw [sum_line]
  simp_rw [line_obs_weight, lineOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma line_obs_mass_all :
    lineMass lineDoNone (fun _ => true) = 1 := by
  unfold lineMass
  rw [sum_line]
  simp_rw [line_obs_weight, lineOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply, ENNReal.inv_two_add_inv_two]

lemma line_rule3_edge :
    UndirectedEdge (rule3Graph lineGraph (∅ : Finset LineV) {.cause} (∅ : Finset LineV))
      .effect .cause := by
  have hz : zOfFinset lineGraph (∅ : Finset LineV) {.cause} (∅ : Finset LineV) = {.cause} := by
    decide
  simp only [rule3Graph, hz, deleteIncoming]
  exact Or.inr ⟨⟨⟨rfl, rfl⟩, by decide⟩, by decide⟩

/-- `W` is empty, so `Z(W) = Z`. The arrow `cause → effect` remains, and the
conditional masses are `1` and `1/2`. -/
theorem line_rule3_fails :
    zOfFinset lineGraph (∅ : Finset LineV) {.cause} (∅ : Finset LineV) = {.cause} ∧
      (¬ DSeparatedFull
        (rule3Graph lineGraph (∅ : Finset LineV) {.cause} (∅ : Finset LineV))
        ({.effect} : Set LineV) ({.cause} : Set LineV) (∅ : Set LineV)) ∧
      lineMass lineDoZ (fun f => f .effect) / lineMass lineDoZ (fun _ => true) ≠
        lineMass lineDoNone (fun f => f .effect) / lineMass lineDoNone (fun _ => true) := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro hsep
    have htrail : HasActiveTrail
        (rule3Graph lineGraph (∅ : Finset LineV) {.cause} (∅ : Finset LineV))
        (∅ : Set LineV) .effect .cause :=
      ⟨[.effect, .cause], List.cons_ne_nil _ _, by simp [PathEndpoints],
        ActiveTrail.two line_rule3_edge⟩
    exact hsep .effect (Set.mem_singleton _) .cause (Set.mem_singleton _)
      (by decide) htrail
  · rw [line_doZ_mass_effect, line_doZ_mass_all, line_obs_mass_effect,
      line_obs_mass_all]
    have hleft : (1 : ℝ≥0∞) / 1 = 1 := by
      rw [ENNReal.div_eq_inv_mul, inv_one, one_mul]
    have hright : (2 : ℝ≥0∞)⁻¹ / 1 = (2 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.div_eq_inv_mul, inv_one, one_mul]
    rw [hleft, hright]
    exact one_ne_inv_two

end Mettapedia.GSLT.Causality.DoCalculus
