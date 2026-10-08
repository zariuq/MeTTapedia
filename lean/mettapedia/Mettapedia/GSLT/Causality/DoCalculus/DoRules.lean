import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mettapedia.GSLT.Causality.DoCalculus.Adjustment
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov

/-!
# Do-calculus on a finite causal model

An intervention `do(treatment = value)` is the truncated factorization of Stage 1.
The same weights are the joint of the Bayesian network on the graph with the
arrows into the treatment deleted, the treatment's conditional table replaced
by a point mass, and every other table left as it was.

Pearl's first rule is conditional independence in that intervened joint. Its
premise is full d-separation in the graph with the arrows into the treatment
deleted, and the treatment belongs to the conditioning set. Full d-separation
in the graph with the arrows out of the treatment deleted implies that premise
for the endpoints that remain after the conditioning set is removed: those
endpoints lie outside the treatment, so an active trail in the incoming-deleted
graph is an active trail in the outgoing-deleted graph. The global Markov
property of the intervened network (`discrete_dSeparationSoundness`) turns the
incoming-deleted separation into conditional independence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open MeasureTheory
open BayesianNetwork
open DirectedGraph
open DSeparation
open scoped BigOperators ENNReal

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]

/-! ## Edges that avoid an intervention -/

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- Outside an intervention, deleting incoming arrows and deleting outgoing
arrows leave the same edges. -/
lemma edges_incoming_iff_outgoing {forbidden : Finset V} {u v : V}
    (hu : u ∉ forbidden) (hv : v ∉ forbidden) :
    (deleteIncoming graph forbidden).edges u v ↔
      (deleteOutgoing graph forbidden).edges u v := by
  simp only [deleteIncoming, deleteOutgoing]
  exact ⟨fun h => ⟨h.1, hu⟩, fun h => ⟨h.1, hv⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
lemma undirected_outgoing_of_incoming {forbidden : Finset V} {u v : V}
    (hu : u ∉ forbidden) (hv : v ∉ forbidden)
    (hedge : UndirectedEdge (deleteIncoming graph forbidden) u v) :
    UndirectedEdge (deleteOutgoing graph forbidden) u v := by
  rcases hedge with h | h
  · exact Or.inl ((edges_incoming_iff_outgoing graph hu hv).1 h)
  · exact Or.inr ((edges_incoming_iff_outgoing graph hv hu).1 h)

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- A directed path in the incoming-deleted graph that starts outside the
intervention never enters it, and it is a path of the outgoing-deleted graph. -/
lemma reachable_outgoing_of_incoming {forbidden : Finset V} {a b : V}
    (ha : a ∉ forbidden)
    (hpath : (deleteIncoming graph forbidden).Reachable a b) :
    (deleteOutgoing graph forbidden).Reachable a b ∧ b ∉ forbidden := by
  induction hpath with
  | refl =>
    exact ⟨reachable_refl (deleteOutgoing graph forbidden) _, ha⟩
  | step hedge _ ih =>
    have hv := And.right hedge
    have htail := ih hv
    exact ⟨Path.step (G := deleteOutgoing graph forbidden) ⟨And.left hedge, ha⟩ htail.1, htail.2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
lemma descendant_outgoing_of_incoming {forbidden : Finset V} {b d : V}
    (hb : b ∉ forbidden)
    (hd : d ∈ (deleteIncoming graph forbidden).descendants b) :
    d ∈ (deleteOutgoing graph forbidden).descendants b := by
  rcases hd with ⟨hreach, hne⟩
  rcases reachable_outgoing_of_incoming graph hb hreach with ⟨hreach', _⟩
  exact ⟨hreach', hne⟩

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- Parents of a vertex outside the intervention are unchanged by deleting
arrows into the intervention. -/
lemma parents_eq_of_not_forbidden {forbidden : Finset V} {v : V} (hv : v ∉ forbidden) :
    (deleteIncoming graph forbidden).parents v = graph.parents v := by
  ext u
  simp only [DirectedGraph.parents, deleteIncoming]
  exact ⟨fun h => h.1, fun h => ⟨h, hv⟩⟩

/-! ## Active trails avoid a conditioned intervention -/

omit [Fintype V] [DecidableEq V] in
lemma pathEndpoints_of_cons {a b c : V} {rest : List V} {s e : V}
    (h : PathEndpoints (a :: b :: c :: rest) = some (s, e)) :
    s = a ∧ PathEndpoints (b :: c :: rest) = some (b, e) := by
  simp only [PathEndpoints] at h
  injection h with hpair
  refine ⟨((Prod.ext_iff.mp hpair).1).symm, ?_⟩
  simp only [PathEndpoints]
  have he : e = (b :: c :: rest).getLast (by simp) := ((Prod.ext_iff.mp hpair).2).symm
  have hlast : (b :: c :: rest).getLast (by simp) = (c :: rest).getLast (by simp) := by
    simp [List.getLast_cons]
  simp [he, hlast]

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- Conditioning on the intervention blocks every visit to it in the
incoming-deleted graph, so an active trail between outside endpoints stays
outside. -/
lemma trail_vertices_outside {forbidden : Finset V} {Z : Set V}
    (hZ : (forbidden : Set V) ⊆ Z) {p : List V}
    (hact : ActiveTrail (deleteIncoming graph forbidden) Z p) :
    ∀ s e : V, PathEndpoints p = some (s, e) → s ∉ forbidden → e ∉ forbidden →
      ∀ v, v ∈ p → v ∉ forbidden :=
  ActiveTrail.rec
    (motive := fun p _ => ∀ s e : V, PathEndpoints p = some (s, e) →
      s ∉ forbidden → e ∉ forbidden → ∀ v, v ∈ p → v ∉ forbidden)
    (fun vtx s e hpe hs _ v hv => by
      simp only [PathEndpoints] at hpe
      injection hpe with hpair
      have hsv : s = vtx := ((Prod.ext_iff.mp hpair).1).symm
      have hvtx : v = vtx := by simpa [List.mem_singleton] using hv
      exact hvtx.symm ▸ hsv ▸ hs)
    (fun {u vNode} _ s e hpe hs he vtx hv => by
      simp only [PathEndpoints, List.getLast_singleton] at hpe
      injection hpe with hpair
      have hsu : s = u := ((Prod.ext_iff.mp hpair).1).symm
      have hev : e = vNode := ((Prod.ext_iff.mp hpair).2).symm
      rcases List.mem_cons.mp hv with heq | hv
      · exact heq.symm ▸ hsu ▸ hs
      · have heq : vtx = vNode := List.mem_singleton.mp hv
        exact heq.symm ▸ hev ▸ he)
    (fun {a b c : V} {rest : List V} hab hbc hac hAct _ ih s e hpe hs he vtx hv => by
      have hsplit := pathEndpoints_of_cons (V := V) hpe
      have haOut : a ∉ forbidden := hsplit.1 ▸ hs
      have hbOut : b ∉ forbidden := by
        intro hbIn
        have hbZ : b ∈ Z := hZ (Finset.mem_coe.mpr hbIn)
        have hnotCol :
            ¬ IsCollider (deleteIncoming graph forbidden)
              ⟨a, b, c, hab, hbc, hac⟩ := by
          intro hcol
          exact hcol.1.2 hbIn
        exact hAct (Or.inl ⟨hnotCol, hbZ⟩)
      have htail := ih b e hsplit.2 hbOut he
      rcases List.mem_cons.mp hv with heq | hv
      · exact heq.symm ▸ haOut
      · exact htail vtx hv)
    hact

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
lemma isActive_outgoing_of_incoming {forbidden : Finset V} {Z : Set V}
    {a b c : V} (ha : a ∉ forbidden) (hb : b ∉ forbidden) (hc : c ∉ forbidden)
    (hab : UndirectedEdge (deleteIncoming graph forbidden) a b)
    (hbc : UndirectedEdge (deleteIncoming graph forbidden) b c)
    (hac : a ≠ c)
    (hAct : IsActive (deleteIncoming graph forbidden) Z ⟨a, b, c, hab, hbc, hac⟩) :
    IsActive (deleteOutgoing graph forbidden) Z
      ⟨a, b, c, undirected_outgoing_of_incoming graph ha hb hab,
        undirected_outgoing_of_incoming graph hb hc hbc, hac⟩ := by
  intro hblocked
  have hab' := undirected_outgoing_of_incoming graph ha hb hab
  have hbc' := undirected_outgoing_of_incoming graph hb hc hbc
  have hcolIff :
      IsCollider (deleteIncoming graph forbidden) ⟨a, b, c, hab, hbc, hac⟩ ↔
        IsCollider (deleteOutgoing graph forbidden)
          ⟨a, b, c, hab', hbc', hac⟩ := by
    simp only [IsCollider, edges_incoming_iff_outgoing graph ha hb,
      edges_incoming_iff_outgoing graph hc hb]
  rcases hblocked with ⟨hnon, hbZ⟩ | ⟨hcol, hbZ, hdesc⟩
  · exact hAct (Or.inl ⟨fun hcol => hnon ((hcolIff).1 hcol), hbZ⟩)
  · have hcolIn : IsCollider (deleteIncoming graph forbidden) ⟨a, b, c, hab, hbc, hac⟩ :=
      (hcolIff).2 hcol
    have hdescIn : ∀ d ∈ (deleteIncoming graph forbidden).descendants b, d ∉ Z := by
      intro d hd
      exact hdesc d (descendant_outgoing_of_incoming graph hb hd)
    exact hAct (Or.inr ⟨hcolIn, hbZ, hdescIn⟩)

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
lemma activeTrail_outgoing_of_incoming {forbidden : Finset V} {Z : Set V}
    {p : List V}
    (hvertices : ∀ v, v ∈ p → v ∉ forbidden)
    (hact : ActiveTrail (deleteIncoming graph forbidden) Z p) :
    ActiveTrail (deleteOutgoing graph forbidden) Z p :=
  ActiveTrail.rec
    (motive := fun p h => (∀ v, v ∈ p → v ∉ forbidden) →
      ActiveTrail (deleteOutgoing graph forbidden) Z p)
    (fun vtx _ => ActiveTrail.single vtx)
    (fun {u v} hedge hvertices =>
      ActiveTrail.two (undirected_outgoing_of_incoming graph
        (hvertices u (by simp)) (hvertices v (by simp)) hedge))
    (fun {a b c} {rest} hab hbc hac hAct hTail ih hvertices =>
      have ha : a ∉ forbidden := hvertices a (by simp)
      have hb : b ∉ forbidden := hvertices b (by simp)
      have hc : c ∉ forbidden := hvertices c (by simp)
      ActiveTrail.cons
        (undirected_outgoing_of_incoming graph ha hb hab)
        (undirected_outgoing_of_incoming graph hb hc hbc)
        hac
        (isActive_outgoing_of_incoming graph ha hb hc hab hbc hac hAct)
        (ih fun v hv => hvertices v (List.mem_cons_of_mem _ hv)))
    hact hvertices

omit [Fintype V] [DecidableEq V] [DecidableRel graph.edges] in
/-- D-separation after deleting arrows out of `forbidden` implies d-separation
after deleting arrows into `forbidden`, when `forbidden` is conditioned on and
neither side of the query meets it. -/
theorem dsep_incoming_of_dsep_outgoing {forbidden : Finset V} {A B Z : Set V}
    (hZ : (forbidden : Set V) ⊆ Z)
    (hA : ∀ a ∈ A, a ∉ forbidden) (hB : ∀ b ∈ B, b ∉ forbidden)
    (hsep : DSeparatedFull (deleteOutgoing graph forbidden) A B Z) :
    DSeparatedFull (deleteIncoming graph forbidden) A B Z := by
  intro a ha b hb hab htrail
  rcases htrail with ⟨p, hne, hends, hact⟩
  have hvertices :=
    trail_vertices_outside graph hZ hact a b hends (hA a ha) (hB b hb)
  exact hsep a ha b hb hab
    ⟨p, hne, hends, activeTrail_outgoing_of_incoming graph hvertices hact⟩

variable (hAcyclic : graph.IsAcyclic)
variable {β : Type} [Fintype β] [DecidableEq β] [MeasurableSpace β]

/-- Set one variable and leave the others free. -/
def doOne (treatment : V) (value : β) : V → Option β :=
  fun v => if v = treatment then some value else none

/-- The conditional tables of `do(treatment = value)`.

The treatment becomes a point mass. Every other table is the original table,
read on the same parents: deleting arrows into the treatment does not change
the parents of any other vertex.
-/
noncomputable def intervenedCPT
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (value : β) :
    (network (β := β) (deleteIncoming graph {treatment})
      (deleteIncoming_acyclic graph hAcyclic {treatment})).DiscreteCPT where
  cpt v pa :=
    if hv : v = treatment then
      PMF.pure value
    else
      cpt.cpt v fun u hu =>
        pa u <| by
          have hvFin : v ∉ ({treatment} : Finset V) := by
            simpa [Finset.mem_singleton] using hv
          simp only [BayesianNetwork.parents] at hu ⊢
          exact (parents_eq_of_not_forbidden graph hvFin).symm ▸ hu

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma doOne_eq_none {treatment : V} {value : β} {v : V} (hv : v ≠ treatment) :
    doOne treatment value v = none := by
  simp [doOne, hv]

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma doOne_eq_some {treatment : V} {value : β} :
    doOne treatment value treatment = some value := by
  simp [doOne]

omit [Fintype β] in
/-- One factor of the intervened joint is the corresponding g-formula factor. -/
lemma intervened_nodeProb_eq_truncatedFactor
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (value : β) (f : V → β) (v : V) :
    DiscreteCPT.nodeProb (intervenedCPT graph hAcyclic cpt treatment value) f v =
      truncatedFactor graph hAcyclic cpt (doOne treatment value) f v := by
  unfold DiscreteCPT.nodeProb DiscreteCPT.parentAssignOfConfig intervenedCPT truncatedFactor
  by_cases hv : v = treatment
  · simp [hv, doOne]
  · simp only [dif_neg hv, doOne_eq_none hv, cptAt_eq_nodeProb]
    unfold DiscreteCPT.nodeProb DiscreteCPT.parentAssignOfConfig
    rfl

omit [Fintype β] in
/-- **The intervened Bayesian network is the truncated factorization.** -/
theorem intervened_jointWeight_eq_truncatedWeight
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (value : β) (f : V → β) :
    (intervenedCPT graph hAcyclic cpt treatment value).jointWeight f =
      truncatedWeight graph hAcyclic cpt (doOne treatment value) f := by
  unfold DiscreteCPT.jointWeight truncatedWeight
  refine Finset.prod_congr rfl fun v _ => ?_
  exact intervened_nodeProb_eq_truncatedFactor graph hAcyclic cpt treatment value f v

/-! ## Rule 1 -/

omit [DecidableEq β] [DecidableRel graph.edges] in
/-- **Do-calculus, rule 1.**

If `outcome` and `covariate` are fully d-separated by `conditioning` in the
graph with the arrows into `treatment` deleted, and `conditioning` contains
`treatment`, then those two sets are conditionally independent given
`conditioning` under `do(treatment = value)`.

The independence is `CondIndepVertices` for the joint of `intervenedCPT`: the
σ-algebras of the two vertex sets in the intervened measure. Overlap between
the sets is allowed when it already sits inside `conditioning`. Membership of
the treatment is what writes `conditioning` as Pearl's set `X, W`.
-/
theorem rule1_condIndep
    [Nonempty β] [StandardBorelSpace β] [StandardBorelSpace (V → β)]
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (value : β)
    (outcome covariate conditioning : Set V)
    (hTreat : treatment ∈ conditioning)
    (hOverlap : outcome ∩ covariate ⊆ conditioning)
    (hsep : DSeparatedFull (deleteIncoming graph {treatment})
      outcome covariate conditioning) :
    CondIndepVertices
      (network (β := β) (deleteIncoming graph {treatment})
        (deleteIncoming_acyclic graph hAcyclic {treatment}))
      (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
      outcome covariate conditioning := by
  let net := network (β := β) (deleteIncoming graph {treatment})
    (deleteIncoming_acyclic graph hAcyclic {treatment})
  let μ : Measure net.JointSpace :=
    (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
  let _ : StandardBorelSpace net.JointSpace := by
    simpa [net, network, BayesianNetwork.JointSpace] using
      (inferInstance : StandardBorelSpace (V → β))
  have hCond : insert treatment conditioning = conditioning := by
    apply Set.eq_of_subset_of_subset
    · intro v hv
      rcases Set.mem_insert_iff.mp hv with hv | hv
      · exact hv ▸ hTreat
      · exact hv
    · exact Set.subset_insert treatment conditioning
  have hOverlapInsert : outcome ∩ covariate ⊆ insert treatment conditioning := by
    rw [hCond]
    exact hOverlap
  have hsepInsert :
      DSeparatedFull (deleteIncoming graph {treatment})
        outcome covariate (insert treatment conditioning) := by
    rw [hCond]
    exact hsep
  rw [← hCond]
  exact dsep_implies_condIndepVertices (bn := net) (μ := μ) hOverlapInsert hsepInsert

omit [DecidableEq β] [DecidableRel graph.edges] in
/-- **Do-calculus, rule 1, from outgoing separation.**

Full d-separation in the graph with the arrows out of `treatment` deleted
implies rule 1 when `conditioning` contains `treatment`. The transferred
separation is the incoming-deleted separation of the endpoints that remain
after `conditioning` is removed. Those endpoints lie outside the treatment, so
the hypothesis of `dsep_incoming_of_dsep_outgoing` applies to them. Rule 1 on
those endpoints, together with
`condIndepVertices_iff_diff_conditioning`, restores the original sets.
-/
theorem rule1_condIndep_of_outgoing
    [Nonempty β] [StandardBorelSpace β] [StandardBorelSpace (V → β)]
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (value : β)
    (outcome covariate conditioning : Set V)
    (hTreat : treatment ∈ conditioning)
    (hOverlap : outcome ∩ covariate ⊆ conditioning)
    (hsep : DSeparatedFull (deleteOutgoing graph {treatment})
      outcome covariate conditioning) :
    CondIndepVertices
      (network (β := β) (deleteIncoming graph {treatment})
        (deleteIncoming_acyclic graph hAcyclic {treatment}))
      (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
      outcome covariate conditioning := by
  let net := network (β := β) (deleteIncoming graph {treatment})
    (deleteIncoming_acyclic graph hAcyclic {treatment})
  let μ : Measure net.JointSpace :=
    (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
  let _ : StandardBorelSpace net.JointSpace := by
    simpa [net, network, BayesianNetwork.JointSpace] using
      (inferInstance : StandardBorelSpace (V → β))
  have hForbid : (({treatment} : Finset V) : Set V) ⊆ conditioning := by
    intro z hz
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hz
    exact hz ▸ hTreat
  have hDsepDiff :
      DSeparatedFull (deleteIncoming graph {treatment})
        (outcome \ conditioning) (covariate \ conditioning) conditioning := by
    refine dsep_incoming_of_dsep_outgoing graph hForbid ?hA ?hB ?hsepOut
    · intro a ha hmem
      have haTreat : a = treatment := by simpa [Finset.mem_singleton] using hmem
      exact ha.2 (haTreat ▸ hTreat)
    · intro b hb hmem
      have hbTreat : b = treatment := by simpa [Finset.mem_singleton] using hmem
      exact hb.2 (hbTreat ▸ hTreat)
    · intro a ha b hb hab htrail
      exact hsep a ha.1 b hb.1 hab htrail
  have hOvDiff :
      (outcome \ conditioning) ∩ (covariate \ conditioning) ⊆ conditioning := by
    intro v hv
    exact hOverlap ⟨hv.1.1, hv.2.1⟩
  have hCIDiff :
      CondIndepVertices net μ (outcome \ conditioning) (covariate \ conditioning)
        conditioning :=
    rule1_condIndep graph hAcyclic cpt treatment value
      (outcome \ conditioning) (covariate \ conditioning) conditioning
      hTreat hOvDiff hDsepDiff
  exact (condIndepVertices_iff_diff_conditioning (bn := net) (μ := μ)).2 hCIDiff

end Mettapedia.GSLT.Causality.DoCalculus
