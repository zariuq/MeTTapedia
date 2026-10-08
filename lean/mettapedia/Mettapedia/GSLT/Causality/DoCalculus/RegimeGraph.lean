import Mettapedia.GSLT.Causality.DoCalculus.Adjustment
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation

/-!
# Regime variables for the do-calculus

Every vertex `v` of an intervention set `Z` gains a parent `F_v`, a regime
node. The only new edge is `F_v → v`. Rule 2 asks for `Y ⫫ F_Z | X, Z, W` in
the graph with the arrows into `X` deleted. Rule 3 asks for `Y ⫫ F_Z | X, W`
in that same augmented graph. Both independences are read off the ordinary
separation premises by the transfer lemmas below.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open DirectedGraph
open DSeparation

variable {V : Type} [DecidableEq V]

/-- An observed vertex, or the regime parent of an observed vertex. -/
inductive AugV (V : Type) where
  | obs (v : V)
  | regime (v : V)
  deriving DecidableEq

instance augV_fintype [Fintype V] : Fintype (AugV V) where
  elems := Finset.univ.image AugV.obs ∪ Finset.univ.image AugV.regime
  complete := by
    intro node
    cases node <;> simp

variable (graph : DirectedGraph V)

/-- `G` plus one regime parent for every vertex of `Z`. -/
def regimeGraph (Z : Finset V) : DirectedGraph (AugV V) where
  edges
    | .obs u, .obs v => graph.edges u v
    | .regime u, .obs v => u ∈ Z ∧ u = v
    | _, _ => False

/-- The original graph with the arrows into `X` deleted. -/
def gx (X : Finset V) : DirectedGraph V :=
  deleteIncoming graph X

/-- The rule 2 premise graph: arrows into `X` and out of `Z` deleted. -/
def gout (X Z : Finset V) : DirectedGraph V :=
  deleteOutgoing (gx graph X) Z

/-- The augmented graph with the arrows into `X` deleted. -/
def ga (X Z : Finset V) : DirectedGraph (AugV V) :=
  deleteIncoming (regimeGraph graph Z) (Finset.image AugV.obs X)

/-- Delete arrows into a set that is not presented as a finset. -/
def deleteIncomingSet (G : DirectedGraph V) (forbidden : Set V) : DirectedGraph V where
  edges u v := G.edges u v ∧ v ∉ forbidden

omit [DecidableEq V] in
lemma regimeGraph_obs_edge (Z : Finset V) {u v : V} :
    (regimeGraph graph Z).edges (.obs u) (.obs v) ↔ graph.edges u v := Iff.rfl

omit [DecidableEq V] in
lemma regimeGraph_regime_edge (Z : Finset V) {u v : V} :
    (regimeGraph graph Z).edges (.regime u) (.obs v) ↔ u ∈ Z ∧ u = v := Iff.rfl

omit [DecidableEq V] in
lemma regimeGraph_no_edge_to_regime (Z : Finset V) (a : AugV V) (v : V) :
    ¬ (regimeGraph graph Z).edges a (.regime v) := by
  cases a <;> simp [regimeGraph]

lemma obs_mem_image {S : Finset V} {v : V} :
    AugV.obs v ∈ Finset.image AugV.obs S ↔ v ∈ S := by
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨u, hu, heq⟩
    cases heq
    exact hu
  · intro hmem
    exact Finset.mem_image.mpr ⟨v, hmem, rfl⟩

omit [DecidableEq V] in
lemma mem_obs_image {S : Set V} {v : V} :
    AugV.obs v ∈ AugV.obs '' S ↔ v ∈ S := by
  constructor
  · intro hmem
    rcases hmem with ⟨u, hu, heq⟩
    cases heq
    exact hu
  · intro hmem
    exact ⟨v, hmem, rfl⟩

/-- Observed vertices that land in an augmented conditioning set. -/
def obsPreimage (C : Set (AugV V)) : Set V :=
  {v | AugV.obs v ∈ C}

omit [DecidableEq V] in
lemma obsPreimage_image (S : Set V) :
    obsPreimage (AugV.obs '' S) = S := by
  ext v
  simp [obsPreimage]

lemma ga_obs_edge (X Z : Finset V) {u v : V} :
    (ga graph X Z).edges (.obs u) (.obs v) ↔ (gx graph X).edges u v := by
  show (regimeGraph graph Z).edges (.obs u) (.obs v) ∧
      AugV.obs v ∉ Finset.image AugV.obs X ↔
    graph.edges u v ∧ v ∉ X
  rw [regimeGraph_obs_edge, obs_mem_image]

lemma ga_regime_edge (X Z : Finset V) {u v : V} :
    (ga graph X Z).edges (.regime u) (.obs v) ↔
      u ∈ Z ∧ u = v ∧ v ∉ X := by
  show (regimeGraph graph Z).edges (.regime u) (.obs v) ∧
      AugV.obs v ∉ Finset.image AugV.obs X ↔
    u ∈ Z ∧ u = v ∧ v ∉ X
  rw [regimeGraph_regime_edge, obs_mem_image]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

lemma ga_no_edge_to_regime (X Z : Finset V) (a : AugV V) (v : V) :
    ¬ (ga graph X Z).edges a (.regime v) := by
  intro hedge
  exact regimeGraph_no_edge_to_regime graph Z a v hedge.1

lemma ga_regime_at (X Z : Finset V) {b : V} (hb : b ∈ Z) (hbX : b ∉ X) :
    (ga graph X Z).edges (.regime b) (.obs b) :=
  (ga_regime_edge graph X Z).2 ⟨hb, rfl, hbX⟩

lemma undirected_ga_obs (X Z : Finset V) {u v : V} :
    UndirectedEdge (ga graph X Z) (.obs u) (.obs v) ↔
      UndirectedEdge (gx graph X) u v := by
  constructor
  · intro hedge
    rcases hedge with hdir | hrev
    · exact Or.inl ((ga_obs_edge graph X Z).1 hdir)
    · exact Or.inr ((ga_obs_edge graph X Z).1 hrev)
  · intro hedge
    rcases hedge with hdir | hrev
    · exact Or.inl ((ga_obs_edge graph X Z).2 hdir)
    · exact Or.inr ((ga_obs_edge graph X Z).2 hrev)

omit [DecidableEq V] in
lemma reachable_obs_proj (Z : Finset V) {u : V} {a : AugV V}
    (hreach : (regimeGraph graph Z).Reachable (.obs u) a) :
    ∃ v : V, a = .obs v ∧ graph.Reachable u v :=
  DirectedGraph.Path.rec (motive := fun src tgt _ =>
      ∀ s : V, src = .obs s → ∃ t : V, tgt = .obs t ∧ graph.Reachable s t)
    (fun vtx s hs => by
      subst hs
      exact ⟨s, rfl, reachable_refl graph s⟩)
    (fun {src mid tgt} hedge _ ih s hs => by
      subst hs
      cases mid with
      | regime r =>
          exact absurd hedge (regimeGraph_no_edge_to_regime graph Z (.obs s) r)
      | obs m =>
          rcases ih m rfl with ⟨t, ht, hmid⟩
          exact ⟨t, ht, DirectedGraph.Path.step
            ((regimeGraph_obs_edge graph Z).1 hedge) hmid⟩)
    hreach u rfl

omit [DecidableEq V] in
lemma reachable_regime_eq (Z : Finset V) {a : AugV V} {v : V}
    (hreach : (regimeGraph graph Z).Reachable a (.regime v)) :
    a = .regime v :=
  DirectedGraph.Path.rec
    (motive := fun src tgt _ => tgt = .regime v → src = .regime v)
    (fun _ htgt => htgt)
    (fun {src mid tgt} hedge _ ih htgt => by
      have hmid : mid = .regime v := ih htgt
      subst hmid
      exact absurd hedge (regimeGraph_no_edge_to_regime graph Z src v))
    hreach rfl

omit [DecidableEq V] in
lemma regimeGraph_acyclic (hAcyclic : graph.IsAcyclic) (Z : Finset V) :
    (regimeGraph graph Z).IsAcyclic := by
  intro vertex ⟨next, hedge, hreach⟩
  cases vertex with
  | regime r =>
      cases next with
      | regime s =>
          exact absurd hedge (regimeGraph_no_edge_to_regime graph Z (.regime r) s)
      | obs o =>
          rcases (regimeGraph_regime_edge graph Z).1 hedge with ⟨_, hro⟩
          have hback := reachable_regime_eq graph Z hreach
          cases hro
          cases hback
  | obs o =>
      cases next with
      | regime s =>
          exact absurd hedge (regimeGraph_no_edge_to_regime graph Z (.obs o) s)
      | obs p =>
          rcases reachable_obs_proj graph Z hreach with ⟨_, ht, hreachG⟩
          cases ht
          exact hAcyclic o ⟨p, (regimeGraph_obs_edge graph Z).1 hedge, hreachG⟩

lemma ga_acyclic (hAcyclic : graph.IsAcyclic) (X Z : Finset V) :
    (ga graph X Z).IsAcyclic :=
  deleteIncoming_acyclic (regimeGraph graph Z)
    (regimeGraph_acyclic graph hAcyclic Z) (Finset.image AugV.obs X)

omit [DecidableEq V] in
lemma gx_acyclic (hAcyclic : graph.IsAcyclic) (X : Finset V) :
    (gx graph X).IsAcyclic :=
  deleteIncoming_acyclic graph hAcyclic X

omit [DecidableEq V] in
lemma gout_acyclic (hAcyclic : graph.IsAcyclic) (X Z : Finset V) :
    (gout graph X Z).IsAcyclic :=
  deleteOutgoing_acyclic (gx graph X) (gx_acyclic graph hAcyclic X) Z

lemma ga_reachable_of_gx (X Z : Finset V) {u v : V}
    (hreach : (gx graph X).Reachable u v) :
    (ga graph X Z).Reachable (.obs u) (.obs v) := by
  induction hreach with
  | refl => exact DirectedGraph.Path.refl _
  | step hedge _ ih =>
      exact DirectedGraph.Path.step ((ga_obs_edge graph X Z).2 hedge) ih

lemma gx_reachable_of_ga (X Z : Finset V) {u : V} {a : AugV V}
    (hreach : (ga graph X Z).Reachable (.obs u) a) :
    ∃ v : V, a = .obs v ∧ (gx graph X).Reachable u v :=
  DirectedGraph.Path.rec (motive := fun src tgt _ =>
      ∀ s : V, src = .obs s → ∃ t : V, tgt = .obs t ∧ (gx graph X).Reachable s t)
    (fun vtx s hs => by
      subst hs
      exact ⟨s, rfl, reachable_refl _ s⟩)
    (fun {src mid tgt} hedge _ ih s hs => by
      subst hs
      cases mid with
      | regime r =>
          exact absurd hedge (ga_no_edge_to_regime graph X Z (.obs s) r)
      | obs m =>
          rcases ih m rfl with ⟨t, ht, hmid⟩
          exact ⟨t, ht, DirectedGraph.Path.step
            ((ga_obs_edge graph X Z).1 hedge) hmid⟩)
    hreach u rfl

lemma ga_descendants_obs (X Z : Finset V) {m d : V} :
    .obs d ∈ (ga graph X Z).descendants (.obs m) ↔
      d ∈ (gx graph X).descendants m := by
  constructor
  · intro hdesc
    rcases hdesc with ⟨hreach, hne⟩
    rcases gx_reachable_of_ga graph X Z hreach with ⟨v, hv, hreachG⟩
    cases hv
    exact ⟨hreachG, fun heq => hne (congrArg AugV.obs heq)⟩
  · intro hdesc
    rcases hdesc with ⟨hreach, hne⟩
    exact ⟨ga_reachable_of_gx graph X Z hreach,
      fun heq => hne (AugV.obs.inj heq)⟩

lemma ga_obs_not_reach_regime (X Z : Finset V) {u v : V} :
    ¬ (ga graph X Z).Reachable (.obs u) (.regime v) := by
  intro hreach
  have hbig :=
    reachable_of_edge_subset (regimeGraph graph Z)
      (fun _ _ hedge => And.left hedge) hreach
  cases reachable_regime_eq graph Z hbig

omit [DecidableEq V] in
lemma gx_only_self_reaches_forbidden (X : Finset V) {u v : V}
    (hv : v ∈ X) (hreach : (gx graph X).Reachable u v) : u = v :=
  DirectedGraph.Path.rec (motive := fun src tgt _ => tgt ∈ X → src = tgt)
    (fun _ _ => rfl)
    (fun {src mid tgt} hedge _ ih hmem => by
      have hmid : mid = tgt := ih hmem
      subst hmid
      exact absurd hmem hedge.2)
    hreach hv

omit [DecidableEq V] in
lemma gx_not_ancestor_of_forbidden (X : Finset V) {x z : V} (hx : x ∈ X) :
    z ∉ (gx graph X).ancestors x := by
  intro hanc
  rcases hanc with ⟨hreach, hne⟩
  exact hne (gx_only_self_reaches_forbidden graph X hx hreach)

/-! ## Trail prefixes -/

omit [DecidableEq V] in
private lemma augEndpointsOfCons {a b c : V} {rest : List V} {s e : V}
    (h : PathEndpoints (a :: b :: c :: rest) = some (s, e)) :
    s = a ∧ PathEndpoints (b :: c :: rest) = some (b, e) := by
  simp only [PathEndpoints] at h
  injection h with hpair
  refine ⟨((Prod.ext_iff.mp hpair).1).symm, ?_⟩
  simp only [PathEndpoints]
  have he : e = (b :: c :: rest).getLast (by simp) := ((Prod.ext_iff.mp hpair).2).symm
  have hlast : (b :: c :: rest).getLast (by simp) =
      (c :: rest).getLast (by simp) := by
    simp [List.getLast_cons]
  simp [he, hlast]

omit [DecidableEq V] in
lemma activeTrail_take {G : DirectedGraph V} {C : Set V} {p : List V}
    (hact : ActiveTrail G C p) :
    ∀ n, 0 < n → n ≤ p.length → ActiveTrail G C (p.take n) :=
  ActiveTrail.rec
    (motive := fun p _ => ∀ n, 0 < n → n ≤ p.length → ActiveTrail G C (p.take n))
    (fun vtx n hn hle => by
      have hlen : ([vtx] : List V).length = 1 := rfl
      have hn1 : n = 1 := by omega
      subst hn1
      simp only [List.take_succ_cons, List.take_zero]
      exact ActiveTrail.single vtx)
    (fun {u v} hedge n hn hle => by
      have hlen : ([u, v] : List V).length = 2 := rfl
      have hn2 : n = 1 ∨ n = 2 := by omega
      rcases hn2 with hn1 | hn2
      · subst hn1
        simp [List.take]
        exact ActiveTrail.single u
      · subst hn2
        simp [List.take]
        exact ActiveTrail.two hedge)
    (fun {a b c} {rest} hab hbc hac hAct _ ih n hn hle => by
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              simp [List.take]
              exact ActiveTrail.single a
          | succ n =>
              cases n with
              | zero =>
                  simp [List.take]
                  exact ActiveTrail.two hab
              | succ n =>
                  have htail := ih (n + 2) (by omega) (by
                    have hlen :
                        (a :: b :: c :: rest).length =
                          (b :: c :: rest).length + 1 := rfl
                    omega)
                  have htake :
                      (a :: b :: c :: rest).take (n + 3) =
                        a :: (b :: c :: rest).take (n + 2) := by
                    simp [List.take]
                  rw [htake]
                  exact ActiveTrail.cons hab hbc hac hAct htail)
    hact

/-- The first vertex of a list that lies in `Z`. -/
def firstHit (Z : Finset V) : List V → Option (List V × V × List V)
  | [] => none
  | v :: rest =>
      if v ∈ Z then some ([], v, rest)
      else
        match firstHit Z rest with
        | none => none
        | some (front, hit, back) => some (v :: front, hit, back)

lemma firstHit_spec (Z : Finset V) (p : List V) :
    match firstHit Z p with
    | none => ∀ v ∈ p, v ∉ Z
    | some (front, hit, back) =>
        p = front ++ [hit] ++ back ∧ hit ∈ Z ∧ ∀ v ∈ front, v ∉ Z := by
  induction p with
  | nil => simp [firstHit]
  | cons head tail ih =>
      unfold firstHit
      by_cases hhead : head ∈ Z
      · simp [hhead]
      · simp only [hhead, ite_false]
        cases htail : firstHit Z tail with
        | none =>
            intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact hhead
            · have hnone := ih
              simp only [htail] at hnone
              exact hnone v hv
        | some triple =>
            rcases triple with ⟨front, hit, back⟩
            have hspec := ih
            simp only [htail] at hspec
            rcases hspec with ⟨heq, hhit, hfront⟩
            refine ⟨?_, hhit, ?_⟩
            · simp [heq]
            · intro v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact hhead
              · exact hfront v hv

lemma firstHit_of_mem (Z : Finset V) {p : List V} {b : V}
    (hb : b ∈ p) (hbZ : b ∈ Z) :
    ∃ front hit back, firstHit Z p = some (front, hit, back) := by
  induction p with
  | nil => cases hb
  | cons head tail ih =>
      unfold firstHit
      by_cases hhead : head ∈ Z
      · exact ⟨[], head, tail, by simp [hhead]⟩
      · have htail : b ∈ tail := by
          rcases List.mem_cons.mp hb with rfl | hb
          · exact absurd hbZ hhead
          · exact hb
        rcases ih htail with ⟨front, hit, back, hsome⟩
        simp [hhead, hsome]

omit [DecidableEq V] in
private lemma take_append_succ (front : List V) (hit : V) (back : List V) :
    (front ++ [hit] ++ back).take (front.length + 1) = front ++ [hit] := by
  induction front with
  | nil => simp [List.take]
  | cons head tail ih =>
      have hstep :
          ((head :: tail) ++ [hit] ++ back).take ((head :: tail).length + 1) =
            head :: (tail ++ [hit] ++ back).take (tail.length + 1) := by
        simp [List.take_succ_cons]
      rw [hstep, ih]
      rfl

lemma take_firstHit {Z : Finset V} {p front : List V} {hit : V} {back : List V}
    (h : firstHit Z p = some (front, hit, back)) :
    p.take (front.length + 1) = front ++ [hit] := by
  have hspec := firstHit_spec Z p
  simp only [h] at hspec
  rcases hspec with ⟨rfl, _, _⟩
  exact take_append_succ front hit back

/-! ## Regime transfer -/

/-- Vertices of `Z` that are not ancestors of any vertex of `W` once the
arrows into `X` have been deleted. This is Pearl's set `Z(W)`. -/
def zWitness (X Z W : Finset V) : Set V :=
  {z | z ∈ (Z : Set V) ∧ ∀ w ∈ (W : Set V), z ∉ (gx graph X).ancestors w}

/-- Rule 3's premise graph: arrows into `X` and into `Z(W)` deleted. -/
def g3 (X Z W : Finset V) : DirectedGraph V :=
  deleteIncomingSet (gx graph X) (zWitness graph X Z W)

omit [DecidableEq V] in
lemma g3_edge_of_gx {X Z W : Finset V} {u v : V}
    (hv : v ∉ zWitness graph X Z W)
    (hedge : (gx graph X).edges u v) :
    (g3 graph X Z W).edges u v :=
  ⟨hedge, hv⟩

omit [DecidableEq V] in
lemma g3_acyclic (hAcyclic : graph.IsAcyclic) (X Z W : Finset V) :
    (g3 graph X Z W).IsAcyclic := by
  intro vertex ⟨nxt, hedge, hreach⟩
  have hsub : ∀ a b, (g3 graph X Z W).edges a b → (gx graph X).edges a b :=
    fun _ _ hab => hab.1
  exact gx_acyclic graph hAcyclic X vertex
    ⟨nxt, hedge.1, reachable_of_edge_subset (gx graph X) hsub hreach⟩

/-- A vertex is sterile for `C` when neither it nor any descendant lies in `C`. -/
def Sterile (G : DirectedGraph V) (C : Set V) (s : V) : Prop :=
  s ∉ C ∧ ∀ d ∈ G.descendants s, d ∉ C

lemma zWitness_outside {X Z W : Finset V} {z : V}
    (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    (hz : z ∈ zWitness graph X Z W) :
    z ∉ ((X ∪ W : Finset V) : Set V) := by
  intro hzXW
  have hzZ : z ∈ Z := Finset.mem_coe.mp hz.1
  rw [Finset.coe_union] at hzXW
  rcases hzXW with hzX | hzW
  · exact Finset.disjoint_left.mp hXZ (Finset.mem_coe.mp hzX) hzZ
  · exact Finset.disjoint_left.mp hWZ (Finset.mem_coe.mp hzW) hzZ

lemma zWitness_sterile {X Z W : Finset V} {z : V}
    (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    (hz : z ∈ zWitness graph X Z W) :
    Sterile (ga graph X Z) (AugV.obs '' ((X ∪ W : Finset V) : Set V)) (.obs z) := by
  refine ⟨?_, ?_⟩
  · intro hzC
    exact zWitness_outside graph hXZ hWZ hz ((mem_obs_image).1 hzC)
  · intro dNode hd hdC
    rcases hd with ⟨hreach, hne⟩
    rcases gx_reachable_of_ga graph X Z hreach with ⟨d, hdEq, hreachG⟩
    cases hdEq
    have hdSet : d ∈ ((X ∪ W : Finset V) : Set V) := (mem_obs_image).1 hdC
    have hdne : d ≠ z := by
      intro heq
      exact hne (congrArg AugV.obs heq)
    rw [Finset.coe_union] at hdSet
    rcases hdSet with hdX | hdW
    · exact hdne
        (gx_only_self_reaches_forbidden graph X (Finset.mem_coe.mp hdX) hreachG).symm
    · exact hz.2 d hdW ⟨hreachG, hdne.symm⟩

/-- The first step of an augmented trail leaves its observed start. -/
def firstLeaves (G : DirectedGraph (AugV V)) : List (AugV V) → Prop
  | .obs s :: m :: _ => G.edges (.obs s) m
  | _ => False

lemma sterile_of_outgoing
    (hAcyclic : graph.IsAcyclic) (X Z : Finset V)
    {C : Set (AugV V)} {s : V} {m : AugV V}
    (hsterile : Sterile (ga graph X Z) C (.obs s))
    (hedge : (ga graph X Z).edges (.obs s) m)
    (hmC : m ∉ C) :
    ∃ t : V, m = .obs t ∧ Sterile (ga graph X Z) C (.obs t) := by
  cases m with
  | regime r =>
      exact absurd hedge (ga_no_edge_to_regime graph X Z (.obs s) r)
  | obs t =>
      refine ⟨t, rfl, hmC, ?_⟩
      intro d hd
      rcases hd with ⟨hreach, _⟩
      have hfrom : (ga graph X Z).Reachable (.obs s) d :=
        reachable_trans (ga graph X Z)
          (edge_reachable (ga graph X Z) hedge) hreach
      have hneS : d ≠ .obs s := by
        intro heq
        exact ga_acyclic graph hAcyclic X Z (.obs s)
          ⟨.obs t, hedge, heq ▸ hreach⟩
      exact hsterile.2 d ⟨hfrom, hneS⟩

/-- An active trail that leaves a sterile observed vertex cannot reach a regime
vertex. A chain of outgoing steps ends at the regime attachment, and that
attachment is a collider whose activating descendant would also descend from
the sterile start. -/
lemma no_leaving_trail_to_regime
    (hAcyclic : graph.IsAcyclic) (X Z : Finset V)
    {C : Set (AugV V)} {p : List (AugV V)}
    (hact : ActiveTrail (ga graph X Z) C p) :
    ∀ {s b : V}, PathEndpoints p = some (.obs s, .regime b) →
      Sterile (ga graph X Z) C (.obs s) →
      firstLeaves (ga graph X Z) p →
      False :=
  ActiveTrail.rec
    (motive := fun trail _ =>
      ∀ {s b : V}, PathEndpoints trail = some (.obs s, .regime b) →
        Sterile (ga graph X Z) C (.obs s) →
        firstLeaves (ga graph X Z) trail →
        False)
    (fun vtx {s b} hpe _ _ => by
      simp only [PathEndpoints] at hpe
      injection hpe with hpair
      have hsv : .obs s = vtx := ((Prod.ext_iff.mp hpair).1).symm
      have hbv : .regime b = vtx := ((Prod.ext_iff.mp hpair).2).symm
      cases hsv.trans hbv.symm)
    (fun {_u _v} _hedge {s b} hpe _ hleave => by
      simp only [PathEndpoints, List.getLast_singleton] at hpe
      injection hpe with hpair
      have hsu : .obs s = _u := ((Prod.ext_iff.mp hpair).1).symm
      have hbv : .regime b = _v := ((Prod.ext_iff.mp hpair).2).symm
      subst hsu
      subst hbv
      exact ga_no_edge_to_regime graph X Z (.obs s) b
        (by simpa [firstLeaves] using hleave))
    (fun {a mid nxt} {rest} hab hbc hac hAct _ ih {s bend} hpe hsterile hleave => by
      have hsplit := augEndpointsOfCons (V := AugV V) hpe
      have ha : a = .obs s := hsplit.1.symm
      subst ha
      have hleaveEdge : (ga graph X Z).edges (.obs s) mid := by
        simpa [firstLeaves] using hleave
      have habU : UndirectedEdge (ga graph X Z) (.obs s) mid := hab
      have hbcU : UndirectedEdge (ga graph X Z) mid nxt := hbc
      rcases habU with habOut | habIn
      · rcases hbcU with hbcOut | hbcIn
        · have hnon : IsNonCollider (ga graph X Z)
              ⟨.obs s, mid, nxt, hab, hbc, hac⟩ := by
            intro hcol
            exact (ga graph X Z).isAcyclic_no_two_cycle
              (ga_acyclic graph hAcyclic X Z) mid nxt hbcOut hcol.2
          have hmidC : mid ∉ C :=
            active_nonCollider_not_in_Z (ga graph X Z) C
              ⟨.obs s, mid, nxt, hab, hbc, hac⟩ hAct hnon
          rcases sterile_of_outgoing graph hAcyclic X Z hsterile hleaveEdge hmidC with
            ⟨t, ht, hsterileT⟩
          subst ht
          have hleaveTail : firstLeaves (ga graph X Z) (.obs t :: nxt :: rest) := by
            simpa [firstLeaves] using hbcOut
          exact ih hsplit.2 hsterileT hleaveTail
        · have hOr := active_collider_desc_in_Z (ga graph X Z) C
            ⟨.obs s, mid, nxt, hab, hbc, hac⟩ hAct ⟨habOut, hbcIn⟩
          rcases hOr with hmidC | ⟨d, hdDesc, hdC⟩
          · have hne : mid ≠ .obs s := by
              intro heq
              exact (ga graph X Z).isAcyclic_irrefl
                (ga_acyclic graph hAcyclic X Z) mid (heq ▸ habOut)
            exact hsterile.2 mid
              ⟨edge_reachable (ga graph X Z) habOut, hne⟩ hmidC
          · rcases hdDesc with ⟨hreach, _⟩
            have hfrom := reachable_trans (ga graph X Z)
              (edge_reachable (ga graph X Z) habOut) hreach
            have hneS : d ≠ .obs s := by
              intro heq
              exact ga_acyclic graph hAcyclic X Z (.obs s)
                ⟨mid, habOut, heq ▸ hreach⟩
            exact hsterile.2 d ⟨hfrom, hneS⟩ hdC
      · exact (ga graph X Z).isAcyclic_no_two_cycle
          (ga_acyclic graph hAcyclic X Z) (.obs s) mid hleaveEdge habIn)
    hact

omit [DecidableEq V] in
lemma endpoint_last {q : List V} {s e : V} (hq : q ≠ [])
    (h : PathEndpoints q = some (s, e)) :
    q.getLast hq = e := by
  match q with
  | [] => exact absurd rfl hq
  | [v] =>
      simp only [PathEndpoints] at h
      injection h with hpair
      exact (Prod.ext_iff.mp hpair).2
  | v :: w :: rest =>
      simp only [PathEndpoints] at h
      injection h with hpair
      simpa [List.getLast_cons] using (Prod.ext_iff.mp hpair).2

omit [DecidableEq V] in
lemma endpoints_cons_last {a : V} {q : List V} {e : V}
    (hq : q ≠ []) (h : q.getLast hq = e) :
    PathEndpoints (a :: q) = some (a, e) := by
  match q with
  | [] => exact absurd rfl hq
  | v :: rest =>
      cases rest with
      | nil => simp [PathEndpoints, h]
      | cons w more => simp [PathEndpoints, h]

/-- An all-observed triple is active in the augmented graph exactly when the
same triple is active in the graph with the arrows into `X` deleted. -/
lemma isActive_obs_iff (X Z : Finset V) {C : Set (AugV V)} {u v w : V}
    (hab : UndirectedEdge (ga graph X Z) (.obs u) (.obs v))
    (hbc : UndirectedEdge (ga graph X Z) (.obs v) (.obs w))
    (hac : AugV.obs u ≠ AugV.obs w) :
    IsActive (ga graph X Z) C ⟨.obs u, .obs v, .obs w, hab, hbc, hac⟩ ↔
      IsActive (gx graph X) (obsPreimage C)
        ⟨u, v, w, (undirected_ga_obs graph X Z).1 hab,
          (undirected_ga_obs graph X Z).1 hbc,
          fun h => hac (congrArg AugV.obs h)⟩ := by
  let tA : PathTriple (ga graph X Z) :=
    ⟨.obs u, .obs v, .obs w, hab, hbc, hac⟩
  let tG : PathTriple (gx graph X) :=
    ⟨u, v, w, (undirected_ga_obs graph X Z).1 hab,
      (undirected_ga_obs graph X Z).1 hbc,
      fun h => hac (congrArg AugV.obs h)⟩
  have hcol : IsCollider (ga graph X Z) tA ↔ IsCollider (gx graph X) tG := by
    constructor
    · intro hcolA
      exact ⟨(ga_obs_edge graph X Z).1 hcolA.1, (ga_obs_edge graph X Z).1 hcolA.2⟩
    · intro hcolG
      exact ⟨(ga_obs_edge graph X Z).2 hcolG.1, (ga_obs_edge graph X Z).2 hcolG.2⟩
  constructor
  · intro hAct hblocked
    rcases hblocked with ⟨hnon, hvS⟩ | ⟨hcolG, hvS, hdesc⟩
    · exact hAct (Or.inl ⟨fun hcolA => hnon (hcol.1 hcolA), hvS⟩)
    · have hdescA : ∀ d ∈ (ga graph X Z).descendants (.obs v), d ∉ C := by
        intro d hd hdC
        rcases hd with ⟨hreachA, hneA⟩
        rcases gx_reachable_of_ga graph X Z hreachA with ⟨d0, rfl, hreach⟩
        exact hdesc d0 ⟨hreach, fun heq => hneA (congrArg AugV.obs heq)⟩ hdC
      exact hAct (Or.inr ⟨hcol.2 hcolG, hvS, hdescA⟩)
  · intro hAct hblocked
    rcases hblocked with ⟨hnon, hvA⟩ | ⟨hcolA, hvA, hdescA⟩
    · exact hAct (Or.inl ⟨fun hcolG => hnon (hcol.2 hcolG), hvA⟩)
    · have hdescG : ∀ d ∈ (gx graph X).descendants v, d ∉ obsPreimage C := by
        intro d hd
        exact hdescA (.obs d)
          ⟨ga_reachable_of_gx graph X Z hd.1,
            fun h => hd.2 (AugV.obs.inj h)⟩
      exact hAct (Or.inr ⟨hcol.1 hcolA, hvA, hdescG⟩)

/-- An active augmented trail from an observed vertex to a regime vertex is an
observed trail followed by the regime edge `F_b → b`. -/
lemma augTrail_project (X Z : Finset V) {C : Set (AugV V)} {p : List (AugV V)}
    (hact : ActiveTrail (ga graph X Z) C p) :
    ∀ {s b : V}, PathEndpoints p = some (.obs s, .regime b) →
      ∃ q : List V, q ≠ [] ∧
        p = q.map AugV.obs ++ [.regime b] ∧
        PathEndpoints q = some (s, b) ∧
        ActiveTrail (gx graph X) (obsPreimage C) q :=
  ActiveTrail.rec
    (motive := fun trail _ =>
      ∀ {s b : V}, PathEndpoints trail = some (.obs s, .regime b) →
        ∃ q : List V, q ≠ [] ∧
          trail = q.map AugV.obs ++ [.regime b] ∧
          PathEndpoints q = some (s, b) ∧
          ActiveTrail (gx graph X) (obsPreimage C) q)
    (fun vtx {s b} hpe => by
      simp only [PathEndpoints] at hpe
      injection hpe with hpair
      have hsv : .obs s = vtx := ((Prod.ext_iff.mp hpair).1).symm
      have hbv : .regime b = vtx := ((Prod.ext_iff.mp hpair).2).symm
      cases hsv.trans hbv.symm)
    (fun {u v} hedge {s b} hpe => by
      simp only [PathEndpoints, List.getLast_singleton] at hpe
      injection hpe with hpair
      have hsu : .obs s = u := ((Prod.ext_iff.mp hpair).1).symm
      have hbv : .regime b = v := ((Prod.ext_iff.mp hpair).2).symm
      subst hsu
      subst hbv
      rcases hedge with hdir | hrev
      · exact absurd hdir (ga_no_edge_to_regime graph X Z (.obs s) b)
      · have hmem := (ga_regime_edge graph X Z).1 hrev
        have hb : b = s := hmem.2.1
        subst hb
        exact ⟨[b], by simp, rfl, rfl, ActiveTrail.single b⟩)
    (fun {a mid nxt} {rest} hab hbc hac hAct _ ih {s bend} hpe => by
      have hsplit := augEndpointsOfCons (V := AugV V) hpe
      have ha : a = .obs s := hsplit.1.symm
      subst ha
      have hmidObs : ∃ sMid : V, mid = .obs sMid := by
        cases mid with
        | obs sMid => exact ⟨sMid, rfl⟩
        | regime r =>
            rcases hab with hdir | hrev
            · exact absurd hdir (ga_no_edge_to_regime graph X Z (.obs s) r)
            · have hmem := (ga_regime_edge graph X Z).1 hrev
              rcases hbc with hfwd | hback
              · cases nxt with
                | regime r2 =>
                    exact absurd hfwd (ga_no_edge_to_regime graph X Z (.regime r) r2)
                | obs o =>
                    have hmem2 := (ga_regime_edge graph X Z).1 hfwd
                    have ho : r = o := hmem2.2.1
                    have hsEq : r = s := hmem.2.1
                    subst ho
                    subst hsEq
                    exact absurd rfl hac
              · exact absurd hback (ga_no_edge_to_regime graph X Z nxt r)
      rcases hmidObs with ⟨sMid, hmid⟩
      subst hmid
      rcases ih hsplit.2 with ⟨qTail, hqNe, hpTail, hpeQ, hactQ⟩
      refine ⟨s :: qTail, ?_, ?_, ?_, ?_⟩
      · simp
      · simp [List.map, hpTail]
      · exact endpoints_cons_last (a := s) hqNe (endpoint_last hqNe hpeQ)
      · cases qTail with
        | nil => exact absurd rfl hqNe
        | cons head tail2 =>
            cases tail2 with
            | nil =>
                have hlist : .obs sMid :: nxt :: rest =
                    .obs head :: .regime bend :: [] := by
                  simpa [List.map] using hpTail
                injection hlist with hsEq hrest
                have hsMidEq : sMid = head := AugV.obs.inj hsEq
                subst hsMidEq
                have hbend : sMid = bend := by
                  have hpeHead := hpeQ
                  simp only [PathEndpoints] at hpeHead
                  injection hpeHead with hpair
                  exact (Prod.ext_iff.mp hpair).2
                subst hbend
                injection hrest with hnxt _
                subst hnxt
                exact ActiveTrail.two ((undirected_ga_obs graph X Z).1 hab)
            | cons nxtV tail3 =>
                have hlist : .obs sMid :: nxt :: rest =
                    .obs head :: .obs nxtV ::
                      (tail3.map AugV.obs ++ [.regime bend]) := by
                  simpa [List.map] using hpTail
                injection hlist with hsEq hrest
                have hsMidEq : sMid = head := AugV.obs.inj hsEq
                subst hsMidEq
                injection hrest with hnxt _
                subst hnxt
                exact ActiveTrail.cons
                  ((undirected_ga_obs graph X Z).1 hab)
                  ((undirected_ga_obs graph X Z).1 hbc)
                  (fun h => hac (congrArg AugV.obs h))
                  ((isActive_obs_iff graph X Z hab hbc hac).1 hAct)
                  hactQ)
    hact

omit [DecidableEq V] in
lemma pathEndpoints_head_last {p : List V} (hp : p ≠ []) :
    PathEndpoints p = some (p.head hp, p.getLast hp) := by
  match p with
  | [] => exact absurd rfl hp
  | [v] => simp [PathEndpoints]
  | _ :: _ :: _ => simp [PathEndpoints, List.getLast_cons]

omit [DecidableEq V] in
lemma active_cons_of_long {G : DirectedGraph V} {C : Set V} {p : List V}
    (hact : ActiveTrail G C p) (hlen : 3 ≤ p.length) :
    ∃ (a b c : V) (rest : List V) (hab : UndirectedEdge G a b)
      (hbc : UndirectedEdge G b c) (hac : a ≠ c),
      p = a :: b :: c :: rest ∧
      IsActive G C ⟨a, b, c, hab, hbc, hac⟩ ∧
      ActiveTrail G C (b :: c :: rest) :=
  ActiveTrail.rec
    (motive := fun trail _ => 3 ≤ trail.length →
      ∃ (a b c : V) (rest : List V) (hab : UndirectedEdge G a b)
        (hbc : UndirectedEdge G b c) (hac : a ≠ c),
        trail = a :: b :: c :: rest ∧
        IsActive G C ⟨a, b, c, hab, hbc, hac⟩ ∧
        ActiveTrail G C (b :: c :: rest))
    (fun vtx hlen => by
      have : ([vtx] : List V).length = 1 := rfl
      omega)
    (fun {u v} _ hlen => by
      have : ([u, v] : List V).length = 2 := rfl
      omega)
    (fun {a b c} {rest} hab hbc hac hAct hTail _ _ =>
      ⟨a, b, c, rest, hab, hbc, hac, rfl, hAct, hTail⟩)
    hact hlen

omit [DecidableEq V] in
/-- A collider at a sterile vertex is blocked. -/
lemma sterile_blocks_collider {G : DirectedGraph V} {C : Set V} {a b c : V}
    {hab : UndirectedEdge G a b} {hbc : UndirectedEdge G b c} {hac : a ≠ c}
    (hsterile : Sterile G C b)
    (hcol : IsCollider G ⟨a, b, c, hab, hbc, hac⟩)
    (hAct : IsActive G C ⟨a, b, c, hab, hbc, hac⟩) :
    False := by
  rcases active_collider_desc_in_Z G C ⟨a, b, c, hab, hbc, hac⟩ hAct hcol with
    hmem | ⟨d, hd, hdC⟩
  · exact hsterile.1 hmem
  · exact hsterile.2 d hd hdC

lemma g3_reachable_of_reaches_TW {X Z W : Finset V} {u v : V}
    (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    (hv : v ∈ ((X ∪ W : Finset V) : Set V))
    (hreach : (gx graph X).Reachable u v) :
    (g3 graph X Z W).Reachable u v :=
  DirectedGraph.Path.rec
    (motive := fun src tgt _ => tgt ∈ ((X ∪ W : Finset V) : Set V) →
      (g3 graph X Z W).Reachable src tgt)
    (fun _ _ => DirectedGraph.Path.refl _)
    (fun {_src mid tgt} hedge tail ih hmem => by
      have hmid : mid ∉ zWitness graph X Z W := by
        intro hzw
        by_cases hEq : mid = tgt
        · exact zWitness_outside graph hXZ hWZ hzw (hEq ▸ hmem)
        · rw [Finset.coe_union] at hmem
          rcases hmem with hX | hW
          · exact hEq (gx_only_self_reaches_forbidden graph X
              (Finset.mem_coe.mp hX) tail)
          · exact hzw.2 tgt hW ⟨tail, hEq⟩
      exact DirectedGraph.Path.step (g3_edge_of_gx graph hmid hedge) (ih hmem))
    hreach hv

/-! ## Rule 3 separation -/

omit [DecidableEq V] in
/-- Every vertex of `p` except possibly the last lies outside `forbidden`. -/
def exceptLastOutside (forbidden : Set V) : List V → Prop
  | [] => True
  | [_] => True
  | head :: tail => head ∉ forbidden ∧ exceptLastOutside forbidden tail

omit [DecidableEq V] in
lemma exceptLast_snoc {forbidden : Set V} {front : List V} {hit : V}
    (h : ∀ v ∈ front, v ∉ forbidden) :
    exceptLastOutside forbidden (front ++ [hit]) := by
  induction front with
  | nil => trivial
  | cons head tail ih =>
      cases tail with
      | nil =>
          exact ⟨h head List.mem_cons_self, trivial⟩
      | cons _neck _rest =>
          exact ⟨h head List.mem_cons_self,
            ih (fun v hv => h v (List.mem_cons_of_mem head hv))⟩

omit [DecidableEq V] in
/-- If the last vertex of `p` lies in `forbidden`, the final edge leaves it. -/
def LastLeaves (G : DirectedGraph V) (forbidden : Set V) (p : List V) : Prop :=
  ∀ pred hit front, p = front ++ [pred, hit] → hit ∈ forbidden → G.edges hit pred

omit [DecidableEq V] in
lemma lastLeaves_tail {G : DirectedGraph V} {forbidden : Set V} {head : V}
    {tail : List V} (h : LastLeaves G forbidden (head :: tail)) :
    LastLeaves G forbidden tail := by
  intro pred hit front heq hmem
  exact h pred hit (head :: front) (by rw [heq]; rfl) hmem

/-- A triple active in `gx` given `X ∪ W` stays active after the arrows into
`Z(W)` are deleted, when its middle vertex lies outside `Z(W)`. -/
lemma isActive_g3_of_gx {X Z W : Finset V} {a b c : V}
    {hab : UndirectedEdge (gx graph X) a b}
    {hbc : UndirectedEdge (gx graph X) b c}
    {hac : a ≠ c}
    (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    (hb : b ∉ zWitness graph X Z W)
    (hab3 : UndirectedEdge (g3 graph X Z W) a b)
    (hbc3 : UndirectedEdge (g3 graph X Z W) b c)
    (hAct : IsActive (gx graph X) ((X ∪ W : Finset V) : Set V)
        ⟨a, b, c, hab, hbc, hac⟩) :
    IsActive (g3 graph X Z W) ((X ∪ W : Finset V) : Set V)
        ⟨a, b, c, hab3, hbc3, hac⟩ := by
  intro hblocked
  rcases hblocked with ⟨hnon, hbT⟩ | ⟨hcol, hbOut, hdesc⟩
  · exact hAct (Or.inl ⟨fun hcolGx =>
      hnon ⟨g3_edge_of_gx graph hb hcolGx.1, g3_edge_of_gx graph hb hcolGx.2⟩,
      hbT⟩)
  · exact hAct (Or.inr ⟨⟨hcol.1.1, hcol.2.1⟩, hbOut, fun d hd hdT => by
      rcases hd with ⟨hreach, hne⟩
      exact hdesc d
        ⟨g3_reachable_of_reaches_TW graph hXZ hWZ hdT hreach, hne⟩ hdT⟩)

/-- Activity in `gx` given `X ∪ W` survives deletion of the arrows into `Z(W)`
when every vertex but the last lies outside `Z(W)` and a final vertex in
`Z(W)` is left by the last edge. -/
lemma activeTrail_g3_except_last
    (hAcyclic : graph.IsAcyclic) (X Z W : Finset V)
    (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    {p : List V}
    (hact : ActiveTrail (gx graph X) ((X ∪ W : Finset V) : Set V) p)
    (hout : exceptLastOutside (zWitness graph X Z W) p)
    (hlast : LastLeaves (gx graph X) (zWitness graph X Z W) p) :
    ActiveTrail (g3 graph X Z W) ((X ∪ W : Finset V) : Set V) p :=
  ActiveTrail.rec
    (motive := fun trail _ =>
      exceptLastOutside (zWitness graph X Z W) trail →
      LastLeaves (gx graph X) (zWitness graph X Z W) trail →
      ActiveTrail (g3 graph X Z W) ((X ∪ W : Finset V) : Set V) trail)
    (fun vtx _ _ => ActiveTrail.single vtx)
    (fun {u v} hedge hout hlast => by
      have hu : u ∉ zWitness graph X Z W := hout.1
      rcases hedge with hdir | hrev
      · have hv : v ∉ zWitness graph X Z W := by
          intro hvMem
          exact (gx graph X).isAcyclic_no_two_cycle
            (gx_acyclic graph hAcyclic X) u v hdir
            (hlast u v [] rfl hvMem)
        exact ActiveTrail.two (Or.inl (g3_edge_of_gx graph hv hdir))
      · exact ActiveTrail.two (Or.inr (g3_edge_of_gx graph hu hrev)))
    (fun {a b c} {rest} hab hbc hac hAct _ ih hout hlast => by
      have ha : a ∉ zWitness graph X Z W := hout.1
      have htailOut := hout.2
      have hb : b ∉ zWitness graph X Z W := htailOut.1
      have habU := hab
      have hbcU := hbc
      have hab3 : UndirectedEdge (g3 graph X Z W) a b := by
        rcases habU with hdir | hrev
        · exact Or.inl (g3_edge_of_gx graph hb hdir)
        · exact Or.inr (g3_edge_of_gx graph ha hrev)
      have hbc3 : UndirectedEdge (g3 graph X Z W) b c := by
        rcases hbcU with hdir | hrev
        · have hc : c ∉ zWitness graph X Z W := by
            intro hcMem
            cases rest with
            | nil =>
                exact (gx graph X).isAcyclic_no_two_cycle
                  (gx_acyclic graph hAcyclic X) b c hdir
                  (hlast b c [a] rfl hcMem)
            | cons d _rest =>
                exact htailOut.2.1 hcMem
          exact Or.inl (g3_edge_of_gx graph hc hdir)
        · exact Or.inr (g3_edge_of_gx graph hb hrev)
      have hAct3 :=
        isActive_g3_of_gx graph hXZ hWZ hb hab3 hbc3 hAct
      exact ActiveTrail.cons hab3 hbc3 hac hAct3
        (ih htailOut (lastLeaves_tail hlast)))
    hact hout hlast

omit [DecidableEq V] in
private lemma augTrail_long (front : List V) (pred hit b : V) (back : List V) :
    3 ≤ (((front ++ [pred]) ++ [hit] ++ back).map AugV.obs ++ [AugV.regime b]).length := by
  simp [List.length_append, List.length_map]
  omega

/-- The edge from the predecessor of a `Z(W)` vertex toward the outcome leaves
that vertex. Entering it would be a sterile collider or the start of a leaving
trail to a regime node. -/
lemma aug_boundary_leaves
    (hAcyclic : graph.IsAcyclic) (X Z W : Finset V)
    (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    {pred hit b : V} {back : List V}
    (hact : ActiveTrail (ga graph X Z)
        (AugV.obs '' ((X ∪ W : Finset V) : Set V))
        ((([] ++ [pred]) ++ [hit] ++ back).map AugV.obs ++ [.regime b]))
    (hhit : hit ∈ zWitness graph X Z W) :
    (gx graph X).edges hit pred := by
  rcases active_cons_of_long hact
      (augTrail_long [] pred hit b back) with
    ⟨a0, m0, n0, rest0, hab, hbc, _hac, hlist, hAct, hTail⟩
  have hshape :
      ((([] ++ [pred]) ++ [hit] ++ back).map AugV.obs ++ [.regime b]) =
        AugV.obs pred :: AugV.obs hit ::
          (back.map AugV.obs ++ [.regime b]) := rfl
  have hlist' := hshape.symm.trans hlist
  injection hlist' with ha hrest
  subst ha
  injection hrest with hm htailEq
  subst hm
  have habU := hab
  rcases habU with hdir | hrev
  · cases back with
    | nil =>
        injection htailEq with hn hr
        subst hn
        subst hr
        have hbcU := hbc
        rcases hbcU with hfwd | hbackE
        · exact absurd hfwd (ga_no_edge_to_regime graph X Z (AugV.obs hit) b)
        · exact False.elim (sterile_blocks_collider (V := AugV V)
            (G := ga graph X Z)
            (zWitness_sterile graph hXZ hWZ hhit) ⟨hdir, hbackE⟩ hAct)
    | cons nxt back' =>
        injection htailEq with hn hr
        subst hn
        subst hr
        have hbcU := hbc
        rcases hbcU with hbcOut | hbcIn
        · have hpeS : PathEndpoints
              (AugV.obs hit :: AugV.obs nxt ::
                (back'.map AugV.obs ++ [.regime b])) =
              some (AugV.obs hit, AugV.regime b) := by
            have hne : (AugV.obs hit :: AugV.obs nxt ::
                (back'.map AugV.obs ++ [.regime b])) ≠ [] := by simp
            have hpl := pathEndpoints_head_last (V := AugV V) hne
            have hh : (AugV.obs hit :: AugV.obs nxt ::
                (back'.map AugV.obs ++ [.regime b])).head hne =
                AugV.obs hit := by simp
            have hg : (AugV.obs hit :: AugV.obs nxt ::
                (back'.map AugV.obs ++ [.regime b])).getLast hne =
                AugV.regime b := by
              simp
            rw [hh, hg] at hpl
            exact hpl
          have hleave : firstLeaves (ga graph X Z)
              (AugV.obs hit :: AugV.obs nxt ::
                (back'.map AugV.obs ++ [.regime b])) := hbcOut
          exact False.elim (no_leaving_trail_to_regime graph hAcyclic X Z hTail
            hpeS (zWitness_sterile graph hXZ hWZ hhit) hleave)
        · exact False.elim (sterile_blocks_collider (V := AugV V)
            (G := ga graph X Z)
            (zWitness_sterile graph hXZ hWZ hhit) ⟨hdir, hbcIn⟩ hAct)
  · exact (ga_obs_edge graph X Z).1 hrev

/-- Along an active augmented trail, the edge that first reaches a vertex of
`Z(W)` leaves that vertex toward the outcome. -/
lemma aug_hit_leaves
    (hAcyclic : graph.IsAcyclic) (X Z W : Finset V)
    (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    {front : List V} {pred hit b : V} {back : List V}
    (hact : ActiveTrail (ga graph X Z)
        (AugV.obs '' ((X ∪ W : Finset V) : Set V))
        (((front ++ [pred]) ++ [hit] ++ back).map AugV.obs ++ [.regime b]))
    (hhit : hit ∈ zWitness graph X Z W) :
    (gx graph X).edges hit pred := by
  suffices hrec : ∀ front',
      ActiveTrail (ga graph X Z)
        (AugV.obs '' ((X ∪ W : Finset V) : Set V))
        (((front' ++ [pred]) ++ [hit] ++ back).map AugV.obs ++ [.regime b]) →
      (gx graph X).edges hit pred by
    exact hrec front hact
  intro front'
  induction front' with
  | nil =>
      intro hact'
      exact aug_boundary_leaves graph hAcyclic X Z W hXZ hWZ hact' hhit
  | cons head tail ih =>
      intro hact'
      rcases active_cons_of_long hact'
          (augTrail_long (head :: tail) pred hit b back) with
        ⟨_a0, _m0, _n0, _rest0, _hab, _hbc, _hac, hlist, _hAct, hTail⟩
      have hshape :
          ((((head :: tail) ++ [pred]) ++ [hit] ++ back).map AugV.obs ++
              [.regime b]) =
            AugV.obs head ::
              (((tail ++ [pred]) ++ [hit] ++ back).map AugV.obs ++
                [.regime b]) := rfl
      have hlist' := hshape.symm.trans hlist
      injection hlist' with _ha hsuf
      rw [← hsuf] at hTail
      exact ih hTail

omit [DecidableEq V] in
private lemma append_pair_eq {α : Type} {front frontV : List α} {hit pred hitV : α}
    (h : front ++ [hit] = frontV ++ [pred, hitV]) :
    hit = hitV ∧ front = frontV ++ [pred] := by
  have h' : front ++ [hit] = (frontV ++ [pred]) ++ [hitV] := by
    simpa [List.append_assoc] using h
  rcases List.append_inj' h' rfl with ⟨hfront, hlast⟩
  injection hlast with hhit
  exact ⟨hhit, hfront⟩

/-- Rule 3, separation half. Separation of `Y` from `Z` given `X ∪ W` in the
graph with the arrows into `X` and into `Z(W)` deleted yields separation of
the observed copy of `Y` from the regime parents of `Z` given the observed
copy of `X ∪ W`. -/
theorem dsep_regime_rule3
    (hAcyclic : graph.IsAcyclic) {X Y Z W : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hWZ : Disjoint W Z)
    (hsep : DSeparatedFull (g3 graph X Z W) (Y : Set V) (Z : Set V)
        ((X ∪ W : Finset V) : Set V)) :
    DSeparatedFull (ga graph X Z)
      (AugV.obs '' (Y : Set V))
      (AugV.regime '' (Z : Set V))
      (AugV.obs '' ((X ∪ W : Finset V) : Set V)) := by
  intro yNode hyY fNode hfZ _hne htrail
  rcases hyY with ⟨y0, hy0, rfl⟩
  rcases hfZ with ⟨zv, hzv, rfl⟩
  rcases htrail with ⟨p, _hp, hpe, hact⟩
  rcases augTrail_project graph X Z hact hpe with ⟨q, hqNe, hqEq, hpeq, hactQ⟩
  have hpre : obsPreimage (AugV.obs '' ((X ∪ W : Finset V) : Set V)) =
      ((X ∪ W : Finset V) : Set V) :=
    obsPreimage_image _
  rw [hpre] at hactQ
  have hzLast : q.getLast hqNe = zv := endpoint_last hqNe hpeq
  have hzMem : zv ∈ q := by
    rw [← hzLast]
    exact List.getLast_mem hqNe
  rcases firstHit_of_mem Z hzMem (Finset.mem_coe.mp hzv) with
    ⟨front, hit, back, hfh⟩
  have hspec := firstHit_spec Z q
  simp only [hfh] at hspec
  rcases hspec with ⟨hqSplit, hhitZ, hfrontOut⟩
  have hyNot : y0 ∉ Z :=
    (Finset.disjoint_left.mp hYZ) (Finset.mem_coe.mp hy0)
  have hheadEq : q.head hqNe = y0 := by
    have hends := pathEndpoints_head_last hqNe
    have hjoin : some (q.head hqNe, q.getLast hqNe) = some (y0, zv) := by
      rw [← hends, hpeq]
    injection hjoin with hp
    exact (Prod.ext_iff.mp hp).1
  have hfrontNe : front ≠ [] := by
    intro hnil
    rw [hnil] at hqSplit
    have hhd : q.head hqNe = hit := by
      simp [hqSplit, List.head_cons]
    exact hyNot (hheadEq.symm.trans hhd ▸ hhitZ)
  have hyNe : y0 ≠ hit := by
    intro heq
    exact hyNot (heq ▸ hhitZ)
  have hpNe : front ++ [hit] ≠ [] := by simp
  have hpeP : PathEndpoints (front ++ [hit]) = some (y0, hit) := by
    have hends := pathEndpoints_head_last hpNe
    have hhd : (front ++ [hit]).head hpNe = y0 := by
      cases front with
      | nil => exact absurd rfl hfrontNe
      | cons a tail =>
          have hqa : q.head hqNe = a := by
            simp [hqSplit, List.head_cons]
          exact hqa.symm.trans hheadEq
    have hgl : (front ++ [hit]).getLast hpNe = hit := by
      simp
    rw [hhd, hgl] at hends
    exact hends
  have htake := activeTrail_take hactQ (front.length + 1) (by omega) (by
    have hlen : q.length = front.length + back.length + 1 := by
      simp [hqSplit, List.length_append]
      omega
    omega)
  rw [take_firstHit hfh] at htake
  have hout : exceptLastOutside (zWitness graph X Z W) (front ++ [hit]) :=
    exceptLast_snoc (fun v hv hz =>
      hfrontOut v hv (Finset.mem_coe.mp hz.1))
  have hlast : LastLeaves (gx graph X) (zWitness graph X Z W) (front ++ [hit]) := by
    intro pred hitV frontV heq hmem
    rcases append_pair_eq heq with ⟨rfl, hfrontEq⟩
    have hactA : ActiveTrail (ga graph X Z)
        (AugV.obs '' ((X ∪ W : Finset V) : Set V))
        (((frontV ++ [pred]) ++ [hit] ++ back).map AugV.obs ++ [.regime zv]) := by
      rw [hqEq, hqSplit, hfrontEq] at hact
      exact hact
    exact aug_hit_leaves graph hAcyclic X Z W hXZ hWZ hactA hmem
  have hact3 := activeTrail_g3_except_last graph hAcyclic X Z W hXZ hWZ
    htake hout hlast
  exact hsep y0 hy0 hit (Finset.mem_coe.mpr hhitZ) hyNe
    ⟨front ++ [hit], hpNe, hpeP, hact3⟩

/-! ## Rule 2 separation -/

/-- A directed path whose vertices before the end lie outside `avoid`. -/
inductive ChainOut (G : DirectedGraph V) (avoid : Finset V) : V → V → Prop where
  | edge {u v : V} (huv : G.edges u v) (hu : u ∉ avoid) : ChainOut G avoid u v
  | step {u v w : V} (huv : G.edges u v) (hu : u ∉ avoid) (hv : v ∉ avoid)
      (tail : ChainOut G avoid v w) : ChainOut G avoid u w

/-- The final edge of `p` points into the final vertex. -/
def Enters (G : DirectedGraph V) (p : List V) : Prop :=
  ∀ pred last front, p = front ++ [pred, last] → G.edges pred last

omit [DecidableEq V] in
lemma enters_tail {G : DirectedGraph V} {head : V} {tail : List V}
    (h : Enters G (head :: tail)) : Enters G tail := by
  intro pred last front heq
  exact h pred last (head :: front) (by rw [heq]; rfl)

/-- Reachability into `avoid` yields a directed path that first meets `avoid`
at its end. -/
lemma chainOut_first {G : DirectedGraph V} {avoid : Finset V} {u v : V}
    (hreach : G.Reachable u v) (hv : v ∈ avoid) (hu : u ∉ avoid) :
    ∃ w, w ∈ avoid ∧ ChainOut G avoid u w :=
  DirectedGraph.Path.rec
    (motive := fun src tgt _ => tgt ∈ avoid → src ∉ avoid →
      ∃ w, w ∈ avoid ∧ ChainOut G avoid src w)
    (fun _ htgt hsrc => absurd htgt hsrc)
    (fun {_src mid _tgt} hedge _ ih htgt hsrc => by
      by_cases hmid : mid ∈ avoid
      · exact ⟨mid, hmid, ChainOut.edge hedge hsrc⟩
      · rcases ih htgt hmid with ⟨w, hw, hchain⟩
        exact ⟨w, hw, ChainOut.step hedge hsrc hmid hchain⟩)
    hreach hv hu

omit [DecidableEq V] in
lemma gout_edge_outside {X Z : Finset V} {u v : V}
    (hu : u ∉ Z) (hedge : (gx graph X).edges u v) :
    (gout graph X Z).edges u v :=
  ⟨hedge, hu⟩

omit [DecidableEq V] in
lemma chain_reachable_gout (X Z : Finset V) {avoid : Finset V} {u w : V}
    (hZ : ∀ v ∈ Z, v ∈ avoid)
    (h : ChainOut (gx graph X) avoid u w) :
    (gout graph X Z).Reachable u w :=
  ChainOut.rec (motive := fun src tgt _ => (gout graph X Z).Reachable src tgt)
    (fun huv hu => edge_reachable _ (gout_edge_outside graph (fun h => hu (hZ _ h)) huv))
    (fun huv hu _ _ ih => reachable_trans _
      (edge_reachable _ (gout_edge_outside graph (fun h => hu (hZ _ h)) huv)) ih)
    h

omit [DecidableEq V] in
/-- An outgoing edge at the middle vertex rules out a collider. -/
lemma noncollider_of_out {G : DirectedGraph V} (hAcyclic : G.IsAcyclic)
    {a b c : V} {hab : UndirectedEdge G a b} {hbc : UndirectedEdge G b c}
    {hac : a ≠ c} (hout : G.edges b a ∨ G.edges b c) :
    IsNonCollider G ⟨a, b, c, hab, hbc, hac⟩ := by
  intro hcol
  rcases hout with hba | hbcOut
  · exact G.isAcyclic_no_two_cycle hAcyclic b a hba hcol.1
  · exact G.isAcyclic_no_two_cycle hAcyclic b c hbcOut hcol.2

omit [DecidableEq V] in
lemma active_noncollider_outside {G : DirectedGraph V} {T : Set V} {a b c : V}
    {hab : UndirectedEdge G a b} {hbc : UndirectedEdge G b c} {hac : a ≠ c}
    (hnon : IsNonCollider G ⟨a, b, c, hab, hbc, hac⟩) (hb : b ∉ T) :
    IsActive G T ⟨a, b, c, hab, hbc, hac⟩ := by
  intro hblocked
  rcases hblocked with ⟨_, hbMem⟩ | ⟨hcol, _, _⟩
  · exact hb hbMem
  · exact hnon hcol

omit [DecidableEq V] in
lemma active_collider_in_set {G : DirectedGraph V} {T : Set V} {a b c : V}
    {hab : UndirectedEdge G a b} {hbc : UndirectedEdge G b c} {hac : a ≠ c}
    (hcol : IsCollider G ⟨a, b, c, hab, hbc, hac⟩) (hb : b ∈ T) :
    IsActive G T ⟨a, b, c, hab, hbc, hac⟩ := by
  intro hblocked
  rcases hblocked with ⟨hnon, _⟩ | ⟨_, hbNot, _⟩
  · exact hnon hcol
  · exact hbNot hb

omit [DecidableEq V] in
lemma active_collider_via_desc {G : DirectedGraph V} {T : Set V} {a b c : V}
    {hab : UndirectedEdge G a b} {hbc : UndirectedEdge G b c} {hac : a ≠ c}
    (hcol : IsCollider G ⟨a, b, c, hab, hbc, hac⟩)
    (hd : ∃ d ∈ G.descendants b, d ∈ T) :
    IsActive G T ⟨a, b, c, hab, hbc, hac⟩ := by
  intro hblocked
  rcases hblocked with ⟨hnon, _⟩ | ⟨_, _, hno⟩
  · exact hnon hcol
  · rcases hd with ⟨d, hdDesc, hdT⟩
    exact hno d hdDesc hdT

/-- `X ∪ Z ∪ W` and `X ∪ W ∪ Z` contain the same vertices. -/
lemma mem_XWZ_of_XZW {X Z W : Finset V} {a : V}
    (h : a ∈ X ∪ Z ∪ W) : a ∈ X ∪ W ∪ Z := by
  rcases Finset.mem_union.mp h with hXZ | hW
  · rcases Finset.mem_union.mp hXZ with hX | hZ
    · exact Finset.mem_union_left Z (Finset.mem_union_left W hX)
    · exact Finset.mem_union_right (X ∪ W) hZ
  · exact Finset.mem_union_left Z (Finset.mem_union_right X hW)

omit [DecidableEq V] in
lemma gout_undirected_outside {X Z : Finset V} {u v : V}
    (hu : u ∉ Z) (hv : v ∉ Z)
    (h : UndirectedEdge (gx graph X) u v) :
    UndirectedEdge (gout graph X Z) u v := by
  rcases h with hdir | hrev
  · exact Or.inl (gout_edge_outside graph hu hdir)
  · exact Or.inr (gout_edge_outside graph hv hrev)

omit [DecidableEq V] in
lemma exceptLast_dropLast {forbidden : Set V} :
    ∀ {p : List V}, exceptLastOutside forbidden p →
      ∀ v ∈ p.dropLast, v ∉ forbidden
  | [], _, v, hv => by simp at hv
  | [_], _, v, hv => by simp at hv
  | a :: b :: rest, h, v, hv => by
      have hdrop : (a :: b :: rest).dropLast = a :: (b :: rest).dropLast :=
        List.dropLast_cons_of_ne_nil (by simp)
      rw [hdrop] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact h.1
      · exact exceptLast_dropLast h.2 v hv

/-- An active trail in the outgoing-deleted graph. The vertex after `src` is
`nxt`, so an outer step can reuse the triple it already has. -/
structure GoutHit (X Z W : Finset V) (src nxt : V) where
  z : V
  tail : List V
  hz : z ∈ Z
  hpe : PathEndpoints (src :: nxt :: tail) = some (src, z)
  hact : ActiveTrail (gout graph X Z) ((X ∪ W : Finset V) : Set V)
    (src :: nxt :: tail)

/-- Add one vertex in front of an active outgoing-deleted trail. -/
lemma extend_gout {X Z W : Finset V} {a b c : V}
    (hit : GoutHit (graph := graph) X Z W b c)
    (hab : UndirectedEdge (gout graph X Z) a b)
    (hbc : UndirectedEdge (gout graph X Z) b c)
    (hac : a ≠ c)
    (hAct : IsActive (gout graph X Z) ((X ∪ W : Finset V) : Set V)
        ⟨a, b, c, hab, hbc, hac⟩) :
    ∃ hit' : GoutHit (graph := graph) X Z W a b, hit'.z = hit.z := by
  let hq : (b :: c :: hit.tail) ≠ [] := List.cons_ne_nil _ _
  exact ⟨{
    z := hit.z
    tail := c :: hit.tail
    hz := hit.hz
    hpe := endpoints_cons_last hq (endpoint_last hq hit.hpe)
    hact := ActiveTrail.cons hab hbc hac hAct hit.hact
  }, rfl⟩

/-- A directed path that first meets `X ∪ W ∪ Z` at a vertex of `Z` is an
active trail after the arrows out of `Z` are deleted. -/
lemma goutHit_of_chain (hAcyclic : graph.IsAcyclic) (X Z W : Finset V)
    {u w : V} (hw : w ∈ Z)
    (h : ChainOut (gx graph X) (X ∪ W ∪ Z) u w) :
    ∃ nxt, ∃ hit : GoutHit (graph := graph) X Z W u nxt,
      hit.z = w ∧ (gout graph X Z).edges u nxt :=
  ChainOut.rec
    (motive := fun src tgt _ => tgt ∈ Z →
      ∃ nxt, ∃ hit : GoutHit (graph := graph) X Z W src nxt,
        hit.z = tgt ∧ (gout graph X Z).edges src nxt)
    (fun {src tgt} huv hu htgt =>
      have hsrcZ : src ∉ Z := fun hz => hu (Finset.mem_union_right _ hz)
      have hdir := gout_edge_outside graph hsrcZ huv
      ⟨tgt, {
        z := tgt
        tail := []
        hz := htgt
        hpe := by simp [PathEndpoints]
        hact := ActiveTrail.two (Or.inl hdir)
      }, rfl, hdir⟩)
    (fun {src mid tgt} huv hu hmid _ ih htgt => by
      rcases ih htgt with ⟨nxt, hit, hzEq, hleave⟩
      have hsrcZ : src ∉ Z := fun hz => hu (Finset.mem_union_right _ hz)
      have hmidT : mid ∉ ((X ∪ W : Finset V) : Set V) := by
        intro hmem
        exact hmid (Finset.mem_union_left Z (Finset.mem_coe.mp hmem))
      have hdir := gout_edge_outside graph hsrcZ huv
      have hac : src ≠ nxt := by
        intro heq
        subst heq
        exact (gout graph X Z).isAcyclic_no_two_cycle
          (gout_acyclic graph hAcyclic X Z) src mid hdir hleave
      have habU : UndirectedEdge (gout graph X Z) src mid := Or.inl hdir
      have hbcU : UndirectedEdge (gout graph X Z) mid nxt := Or.inl hleave
      have hnon : IsNonCollider (gout graph X Z)
          ⟨src, mid, nxt, habU, hbcU, hac⟩ :=
        noncollider_of_out (gout_acyclic graph hAcyclic X Z)
          (hab := habU) (hbc := hbcU) (hac := hac) (Or.inr hleave)
      have hAct := active_noncollider_outside hnon hmidT
      rcases extend_gout graph hit habU hbcU hac hAct with ⟨hit', hz'⟩
      exact ⟨mid, hit', hz'.trans hzEq, hdir⟩)
    h hw

omit [DecidableEq V] in
lemma enters_snoc {G : DirectedGraph V} {front : List V} {hit : V}
    (hne : front ≠ []) (hedge : G.edges (front.getLast hne) hit) :
    Enters G (front ++ [hit]) := by
  intro pred last front' heq
  rcases append_pair_eq heq with ⟨rfl, hfront⟩
  simpa [hfront, List.getLast_append, List.getLast_singleton] using hedge

omit [DecidableEq V] in
lemma prefix_with_succ {front : List V} {hit nxt : V} {back : List V}
    (hne : front ≠ []) :
    front.dropLast ++ [front.getLast hne, hit, nxt] ++ back =
      front ++ [hit] ++ (nxt :: back) := by
  have hfront := List.dropLast_concat_getLast (l := front) hne
  calc
    front.dropLast ++ [front.getLast hne, hit, nxt] ++ back
        = (front.dropLast ++ [front.getLast hne]) ++ [hit, nxt] ++ back := by
          simp [List.append_assoc]
    _ = front ++ [hit, nxt] ++ back := by rw [hfront]
    _ = front ++ [hit] ++ (nxt :: back) := by simp [List.append_assoc]

/-- The observed edge in front of a regime parent points into that observed
vertex: the other direction is a non-collider at a conditioned vertex. -/
lemma gx_enters_before_regime
    (hAcyclic : graph.IsAcyclic) (X Z : Finset V)
    {C : Set (AugV V)} {pred b : V}
    (hbC : AugV.obs b ∈ C) :
    ∀ front,
      ActiveTrail (ga graph X Z) C
        (((front ++ [pred]) ++ [b]).map AugV.obs ++ [AugV.regime b]) →
      (gx graph X).edges pred b := by
  intro front
  induction front with
  | nil =>
      intro hact
      rcases active_cons_of_long hact (by simp) with
        ⟨a0, m0, n0, rest0, hab, hbc, hac, hlist, hAct, _⟩
      have hshape :
          ((([] ++ [pred]) ++ [b]).map AugV.obs ++ [AugV.regime b]) =
            AugV.obs pred :: AugV.obs b :: AugV.regime b :: [] := rfl
      have hlist' := hshape.symm.trans hlist
      injection hlist' with ha hrest
      subst ha
      injection hrest with hm hrest2
      subst hm
      injection hrest2 with hn hr
      subst hn
      subst hr
      rcases hbc with hfwd | hbackE
      · exact absurd hfwd (ga_no_edge_to_regime graph X Z (AugV.obs b) b)
      · rcases hab with hdir | hrev
        · exact (ga_obs_edge graph X Z).1 hdir
        · have hnon : IsNonCollider (ga graph X Z)
              ⟨AugV.obs pred, AugV.obs b, AugV.regime b,
                Or.inr hrev, Or.inr hbackE, hac⟩ :=
            noncollider_of_out (ga_acyclic graph hAcyclic X Z)
              (hab := Or.inr hrev) (hbc := Or.inr hbackE) (hac := hac)
              (Or.inl hrev)
          exact absurd hbC (active_nonCollider_not_in_Z (ga graph X Z) C
            ⟨AugV.obs pred, AugV.obs b, AugV.regime b, Or.inr hrev, Or.inr hbackE, hac⟩
            hAct hnon)
  | cons head tail ih =>
      intro hact
      rcases active_cons_of_long hact (by simp) with
        ⟨_, _, _, _, _, _, _, hlist, _, hTail⟩
      have hshape :
          ((((head :: tail) ++ [pred]) ++ [b]).map AugV.obs ++ [AugV.regime b]) =
            AugV.obs head ::
              (((tail ++ [pred]) ++ [b]).map AugV.obs ++ [AugV.regime b]) := rfl
      have hlist' := hshape.symm.trans hlist
      injection hlist' with _ha hsuf
      rw [← hsuf] at hTail
      exact ih hTail

/-- At a conditioned vertex the active triple is a collider, so the preceding
edge points in. -/
lemma gx_junction_enters
    (hAcyclic : graph.IsAcyclic) (X Z W : Finset V)
    {pred hit nxt : V} {back : List V}
    (hhit : hit ∈ ((X ∪ Z ∪ W : Finset V) : Set V)) :
    ∀ front,
      ActiveTrail (gx graph X) ((X ∪ Z ∪ W : Finset V) : Set V)
        (front ++ [pred, hit, nxt] ++ back) →
      (gx graph X).edges pred hit := by
  intro front
  induction front with
  | nil =>
      intro hact
      rcases active_cons_of_long hact (by simp) with
        ⟨a0, m0, n0, rest0, hab, hbc, hac, hlist, hAct, _⟩
      have hshape : ([] ++ [pred, hit, nxt] ++ back) =
          pred :: hit :: nxt :: back := rfl
      have hlist' := hshape.symm.trans hlist
      injection hlist' with ha hrest
      subst ha
      injection hrest with hm hrest2
      subst hm
      injection hrest2 with hn _
      subst hn
      rcases hab with hdir | hrev
      · exact hdir
      · have hnon : IsNonCollider (gx graph X)
            ⟨pred, hit, nxt, Or.inr hrev, hbc, hac⟩ :=
          noncollider_of_out (gx_acyclic graph hAcyclic X)
            (hab := Or.inr hrev) (hbc := hbc) (hac := hac) (Or.inl hrev)
        exact absurd hhit (active_nonCollider_not_in_Z (gx graph X)
          ((X ∪ Z ∪ W : Finset V) : Set V)
          ⟨pred, hit, nxt, Or.inr hrev, hbc, hac⟩ hAct hnon)
  | cons head tail ih =>
      intro hact
      rcases active_cons_of_long hact (by
        simp
        omega) with
        ⟨_, _, _, _, _, _, _, hlist, _, hTail⟩
      have hshape : ((head :: tail) ++ [pred, hit, nxt] ++ back) =
          head :: (tail ++ [pred, hit, nxt] ++ back) := rfl
      have hlist' := hshape.symm.trans hlist
      injection hlist' with _ha hsuf
      rw [← hsuf] at hTail
      exact ih hTail

/-- The edge that first reaches `Z` points into `Z`. -/
lemma enters_of_first_hit
    (hAcyclic : graph.IsAcyclic) (X Z W : Finset V)
    {q front : List V} {hit b : V} {back : List V}
    (hqNe : q ≠ []) (hfrontNe : front ≠ [])
    (hhit : hit ∈ Z)
    (hqSplit : q = front ++ [hit] ++ back)
    (hlast : q.getLast hqNe = b)
    (hactG : ActiveTrail (gx graph X) ((X ∪ Z ∪ W : Finset V) : Set V) q)
    (hactA : ActiveTrail (ga graph X Z)
        (AugV.obs '' ((X ∪ Z ∪ W : Finset V) : Set V))
        (q.map AugV.obs ++ [AugV.regime b])) :
    Enters (gx graph X) (front ++ [hit]) := by
  have hpred : (gx graph X).edges (front.getLast hfrontNe) hit := by
    cases hback : back with
    | nil =>
        have hqEq : q = front ++ [hit] := by
          simpa [hback, List.append_nil] using hqSplit
        have hgl : q.getLast hqNe = hit := by
          simp [hqEq, List.getLast_singleton]
        have hbHit : hit = b := hgl.symm.trans hlast
        subst hbHit
        have hactR := hactA
        rw [hqEq] at hactR
        rw [← List.dropLast_concat_getLast hfrontNe] at hactR
        have hbC : AugV.obs hit ∈
            AugV.obs '' ((X ∪ Z ∪ W : Finset V) : Set V) :=
          ⟨hit, Finset.mem_coe.mpr
              (Finset.mem_union_left W (Finset.mem_union_right X hhit)), rfl⟩
        exact gx_enters_before_regime graph hAcyclic X Z hbC
          front.dropLast hactR
    | cons nxt back' =>
        have hactJ := hactG
        rw [hqSplit, hback] at hactJ
        rw [← prefix_with_succ hfrontNe] at hactJ
        exact gx_junction_enters graph hAcyclic X Z W
          (Finset.mem_coe.mpr
            (Finset.mem_union_left W (Finset.mem_union_right X hhit)))
          front.dropLast hactJ
  exact enters_snoc hfrontNe hpred

omit [DecidableEq V] in
lemma trail_cons_parts {G : DirectedGraph V} {C : Set V} {a b c : V} {rest : List V}
    (hact : ActiveTrail G C (a :: b :: c :: rest)) :
    ∃ (hab : UndirectedEdge G a b) (hbc : UndirectedEdge G b c) (hac : a ≠ c),
      IsActive G C ⟨a, b, c, hab, hbc, hac⟩ ∧
      ActiveTrail G C (b :: c :: rest) := by
  rcases active_cons_of_long hact (by simp) with
    ⟨a0, b0, c0, rest0, hab, hbc, hac, hlist, hAct, hTail⟩
  injection hlist with ha hrest
  subst ha
  injection hrest with hb hr
  subst hb
  injection hr with hc hr
  subst hc
  subst hr
  exact ⟨hab, hbc, hac, hAct, hTail⟩

/-- Keep an active non-collider when passing to the outgoing-deleted graph.
The vertex after the middle may lie in `Z`; the entering hypothesis supplies
the direction of that final edge. -/
lemma finish_from_gx_noncollider
    (hAcyclic : graph.IsAcyclic) (X Z W : Finset V)
    {a b c : V} {rest : List V}
    (haZ : a ∉ Z) (hbZ : b ∉ Z)
    (hab : UndirectedEdge (gx graph X) a b)
    (hbc : UndirectedEdge (gx graph X) b c)
    (hac : a ≠ c)
    (hAct : IsActive (gx graph X) ((X ∪ Z ∪ W : Finset V) : Set V)
        ⟨a, b, c, hab, hbc, hac⟩)
    (hnon : IsNonCollider (gx graph X) ⟨a, b, c, hab, hbc, hac⟩)
    (hent : Enters (gx graph X) (a :: b :: c :: rest))
    (hout : exceptLastOutside ((Z : Finset V) : Set V) (a :: b :: c :: rest))
    (hitT : GoutHit (graph := graph) X Z W b c) :
    Nonempty (GoutHit (graph := graph) X Z W a b) := by
  have hbS : b ∉ ((X ∪ Z ∪ W : Finset V) : Set V) :=
    active_nonCollider_not_in_Z (gx graph X)
      ((X ∪ Z ∪ W : Finset V) : Set V)
      ⟨a, b, c, hab, hbc, hac⟩ hAct hnon
  have hbT : b ∉ ((X ∪ W : Finset V) : Set V) := by
    intro hbMem
    apply hbS
    rw [Finset.coe_union] at hbMem
    rw [Finset.coe_union, Finset.coe_union]
    rcases hbMem with hX | hW
    · exact Or.inl (Or.inl hX)
    · exact Or.inr hW
  have habG := gout_undirected_outside graph haZ hbZ hab
  have hbcG : UndirectedEdge (gout graph X Z) b c := by
    rcases hbc with hdir | hrev
    · exact Or.inl (gout_edge_outside graph hbZ hdir)
    · have hcZ : c ∉ Z := by
        intro hcMem
        cases rest with
        | nil =>
            have hin := hent b c [a] rfl
            exact (gx graph X).isAcyclic_no_two_cycle
              (gx_acyclic graph hAcyclic X) b c hin hrev
        | cons d rest' =>
            have hcFront : c ∈ (a :: b :: c :: d :: rest').dropLast := by
              simp [List.dropLast]
            exact exceptLast_dropLast hout c hcFront (Finset.mem_coe.mpr hcMem)
      exact Or.inr (gout_edge_outside graph hcZ hrev)
  have hnonG : IsNonCollider (gout graph X Z) ⟨a, b, c, habG, hbcG, hac⟩ := by
    intro hcol
    exact hnon ⟨hcol.1.1, hcol.2.1⟩
  have hActG := active_noncollider_outside hnonG hbT
  rcases extend_gout graph hitT habG hbcG hac hActG with ⟨hit', _⟩
  exact ⟨hit'⟩

/-- An active trail in `gx`, given `X ∪ Z ∪ W`, that starts outside `Z`, ends
inside `Z`, and enters its final vertex, yields an active trail in the graph
with the arrows out of `Z` deleted. A collider activated only by a descendant
in `Z` is replaced by the directed path to the first vertex of `Z`. -/
lemma prefix_hit (hAcyclic : graph.IsAcyclic) (X Z W : Finset V) {a : V} :
    ∀ (suf : List V),
      ActiveTrail (gx graph X) ((X ∪ Z ∪ W : Finset V) : Set V) (a :: suf) →
      exceptLastOutside ((Z : Finset V) : Set V) (a :: suf) →
      Enters (gx graph X) (a :: suf) →
      (a :: suf).getLast (List.cons_ne_nil a suf) ∈ Z →
      a ∉ Z →
      (hne : suf ≠ []) →
      Nonempty (GoutHit (graph := graph) X Z W a (suf.head hne)) := by
  intro suf
  induction suf generalizing a with
  | nil =>
      intro _ _ _ _ _ hne
      exact absurd rfl hne
  | cons b rest ih =>
      intro hact hout hent hlast haZ hne
      cases rest with
      | nil =>
          have hdir : (gx graph X).edges a b := hent a b [] rfl
          have hgo := gout_edge_outside graph haZ hdir
          have hbZ : b ∈ Z := by
            simpa [List.getLast_cons, List.getLast_singleton] using hlast
          exact ⟨{
            z := b
            tail := []
            hz := hbZ
            hpe := by simp [PathEndpoints]
            hact := ActiveTrail.two (Or.inl hgo)
          }⟩
      | cons c rest2 =>
          rcases trail_cons_parts hact with ⟨hab, hbc, hac, hAct, hTail⟩
          have hbZ : b ∉ Z := by
            simpa [Finset.mem_coe] using hout.2.1
          have houtT : exceptLastOutside ((Z : Finset V) : Set V) (b :: c :: rest2) :=
            hout.2
          have hentT : Enters (gx graph X) (b :: c :: rest2) := enters_tail hent
          have hlastT : (b :: c :: rest2).getLast (List.cons_ne_nil _ _) ∈ Z := by
            simpa [List.getLast_cons] using hlast
          rcases ih (a := b) hTail houtT hentT hlastT hbZ (by simp) with ⟨hitT⟩
          rcases hab with habAB | habBA
          · rcases hbc with hbcBC | hbcCB
            · have hnon := noncollider_of_out (gx_acyclic graph hAcyclic X)
                (hab := Or.inl habAB) (hbc := Or.inl hbcBC) (hac := hac)
                (Or.inr hbcBC)
              exact finish_from_gx_noncollider graph hAcyclic X Z W haZ hbZ
                (Or.inl habAB) (Or.inl hbcBC) hac hAct hnon hent hout hitT
            · have hcol : IsCollider (gx graph X)
                  ⟨a, b, c, Or.inl habAB, Or.inr hbcCB, hac⟩ := ⟨habAB, hbcCB⟩
              have hcZ : c ∉ Z := by
                intro hcMem
                cases rest2 with
                | nil =>
                    have hin := hent b c [a] rfl
                    exact (gx graph X).isAcyclic_no_two_cycle
                      (gx_acyclic graph hAcyclic X) b c hin hbcCB
                | cons d rest' =>
                    have hcFront : c ∈ (a :: b :: c :: d :: rest').dropLast := by
                      simp [List.dropLast]
                    exact exceptLast_dropLast hout c hcFront (Finset.mem_coe.mpr hcMem)
              have habG : UndirectedEdge (gout graph X Z) a b :=
                Or.inl (gout_edge_outside graph haZ habAB)
              have hbcG : UndirectedEdge (gout graph X Z) b c :=
                Or.inr (gout_edge_outside graph hcZ hbcCB)
              have hcolG : IsCollider (gout graph X Z)
                  ⟨a, b, c, habG, hbcG, hac⟩ :=
                ⟨gout_edge_outside graph haZ habAB, gout_edge_outside graph hcZ hbcCB⟩
              by_cases hbAvoid : b ∈ X ∪ W ∪ Z
              · have hbTW : b ∈ X ∪ W := by
                  rcases Finset.mem_union.mp hbAvoid with hmem | hmem
                  · exact hmem
                  · exact absurd hmem hbZ
                have hActG := active_collider_in_set hcolG (Finset.mem_coe.mpr hbTW)
                rcases extend_gout graph hitT habG hbcG hac hActG with ⟨hit', _⟩
                exact ⟨hit'⟩
              · rcases active_collider_desc_in_Z (gx graph X)
                    ((X ∪ Z ∪ W : Finset V) : Set V)
                    ⟨a, b, c, Or.inl habAB, Or.inr hbcCB, hac⟩ hAct hcol with
                  hbS | ⟨d, hdDesc, hdS⟩
                · exact absurd (mem_XWZ_of_XZW (Finset.mem_coe.mp hbS)) hbAvoid
                · rcases hdDesc with ⟨hreach, _hneD⟩
                  rcases chainOut_first hreach
                      (mem_XWZ_of_XZW (Finset.mem_coe.mp hdS)) hbAvoid with
                    ⟨w, hwAvoid, hchain⟩
                  by_cases hwTW : w ∈ X ∪ W
                  · have hreachG := chain_reachable_gout graph X Z
                        (fun v hv => Finset.mem_union_right (X ∪ W) hv) hchain
                    have hwNe : w ≠ b := by
                      intro heq
                      exact hbAvoid (heq.symm ▸ hwAvoid)
                    have hActG := active_collider_via_desc hcolG
                      ⟨w, ⟨hreachG, hwNe⟩, Finset.mem_coe.mpr hwTW⟩
                    rcases extend_gout graph hitT habG hbcG hac hActG with ⟨hit', _⟩
                    exact ⟨hit'⟩
                  · have hwZ : w ∈ Z := by
                      rcases Finset.mem_union.mp hwAvoid with hmem | hmem
                      · exact absurd hmem hwTW
                      · exact hmem
                    rcases goutHit_of_chain graph hAcyclic X Z W hwZ hchain with
                      ⟨nxt, hitB, _, hleave⟩
                    have hac2 : a ≠ nxt := by
                      intro heq
                      subst heq
                      exact (gout graph X Z).isAcyclic_no_two_cycle
                        (gout_acyclic graph hAcyclic X Z) a b
                        (gout_edge_outside graph haZ habAB) hleave
                    have hleaveU : UndirectedEdge (gout graph X Z) b nxt :=
                      Or.inl hleave
                    have habU : UndirectedEdge (gout graph X Z) a b :=
                      Or.inl (gout_edge_outside graph haZ habAB)
                    have hnonD : IsNonCollider (gout graph X Z)
                        ⟨a, b, nxt, habU, hleaveU, hac2⟩ :=
                      noncollider_of_out (gout_acyclic graph hAcyclic X Z)
                        (hab := habU) (hbc := hleaveU) (hac := hac2) (Or.inr hleave)
                    have hbT : b ∉ ((X ∪ W : Finset V) : Set V) := by
                      intro hbMem
                      exact hbAvoid (Finset.mem_union_left Z (Finset.mem_coe.mp hbMem))
                    have hActD := active_noncollider_outside hnonD hbT
                    rcases extend_gout graph hitB habU hleaveU hac2 hActD with ⟨hit', _⟩
                    exact ⟨hit'⟩
          · rcases hbc with hbcBC | hbcCB
            · have hnon := noncollider_of_out (gx_acyclic graph hAcyclic X)
                (hab := Or.inr habBA) (hbc := Or.inl hbcBC) (hac := hac)
                (Or.inl habBA)
              exact finish_from_gx_noncollider graph hAcyclic X Z W haZ hbZ
                (Or.inr habBA) (Or.inl hbcBC) hac hAct hnon hent hout hitT
            · have hnon := noncollider_of_out (gx_acyclic graph hAcyclic X)
                (hab := Or.inr habBA) (hbc := Or.inr hbcCB) (hac := hac)
                (Or.inl habBA)
              exact finish_from_gx_noncollider graph hAcyclic X Z W haZ hbZ
                (Or.inr habBA) (Or.inr hbcCB) hac hAct hnon hent hout hitT

/-- Rule 2, separation half. Separation of `Y` from `Z` given `X ∪ W` in the
graph with the arrows into `X` and out of `Z` deleted yields separation of the
observed copy of `Y` from the regime parents of `Z` given the observed copy of
`X ∪ Z ∪ W`. -/
theorem dsep_regime_rule2
    (hAcyclic : graph.IsAcyclic) {X Y Z W : Finset V}
    (hYZ : Disjoint Y Z)
    (hsep : DSeparatedFull (gout graph X Z) (Y : Set V) (Z : Set V)
        ((X ∪ W : Finset V) : Set V)) :
    DSeparatedFull (ga graph X Z)
      (AugV.obs '' (Y : Set V))
      (AugV.regime '' (Z : Set V))
      (AugV.obs '' ((X ∪ Z ∪ W : Finset V) : Set V)) := by
  intro yNode hyY fNode hfZ _hne htrail
  rcases hyY with ⟨y0, hy0, rfl⟩
  rcases hfZ with ⟨zv, hzv, rfl⟩
  rcases htrail with ⟨_p, _hp, hpe, hact⟩
  rcases augTrail_project graph X Z hact hpe with ⟨q, hqNe, hqEq, hpeq, hactQ⟩
  have hpre : obsPreimage (AugV.obs '' ((X ∪ Z ∪ W : Finset V) : Set V)) =
      ((X ∪ Z ∪ W : Finset V) : Set V) :=
    obsPreimage_image _
  rw [hpre] at hactQ
  have hzLast : q.getLast hqNe = zv := endpoint_last hqNe hpeq
  have hzMem : zv ∈ q := by
    rw [← hzLast]
    exact List.getLast_mem hqNe
  rcases firstHit_of_mem Z hzMem (Finset.mem_coe.mp hzv) with
    ⟨front, hit, back, hfh⟩
  have hspec := firstHit_spec Z q
  simp only [hfh] at hspec
  rcases hspec with ⟨hqSplit, hhitZ, hfrontOut⟩
  have hyNot : y0 ∉ Z :=
    (Finset.disjoint_left.mp hYZ) (Finset.mem_coe.mp hy0)
  have hheadEq : q.head hqNe = y0 := by
    have hends := pathEndpoints_head_last hqNe
    have hjoin : some (q.head hqNe, q.getLast hqNe) = some (y0, zv) := by
      rw [← hends, hpeq]
    injection hjoin with hp
    exact (Prod.ext_iff.mp hp).1
  have hfrontNe : front ≠ [] := by
    intro hnil
    rw [hnil] at hqSplit
    have hhd : q.head hqNe = hit := by
      simp [hqSplit, List.head_cons]
    exact hyNot (hheadEq.symm.trans hhd ▸ hhitZ)
  have htake := activeTrail_take hactQ (front.length + 1) (by omega) (by
    have hlen : q.length = front.length + back.length + 1 := by
      simp [hqSplit, List.length_append]
      omega
    omega)
  rw [take_firstHit hfh] at htake
  have hent : Enters (gx graph X) (front ++ [hit]) :=
    enters_of_first_hit graph hAcyclic X Z W hqNe hfrontNe hhitZ hqSplit
      hzLast hactQ (by
        rw [hqEq] at hact
        exact hact)
  have hout : exceptLastOutside ((Z : Finset V) : Set V) (front ++ [hit]) :=
    exceptLast_snoc (fun v hv hz => hfrontOut v hv (Finset.mem_coe.mp hz))
  cases front with
  | nil => exact absurd rfl hfrontNe
  | cons head suf =>
      have hqa : q.head hqNe = head := by
        simp [hqSplit, List.head_cons]
      have hheadY : y0 = head := (hqa.symm.trans hheadEq).symm
      subst hheadY
      have hsufNe : suf ++ [hit] ≠ [] := by simp
      have hlastP : (y0 :: (suf ++ [hit])).getLast (List.cons_ne_nil _ _) ∈ Z := by
        simp
        exact hhitZ
      rcases prefix_hit graph hAcyclic X Z W (suf ++ [hit]) htake hout hent
          hlastP hyNot hsufNe with ⟨hitG⟩
      have hyNe : y0 ≠ hitG.z := by
        intro heq
        exact hyNot (heq ▸ hitG.hz)
      exact hsep y0 hy0 hitG.z (Finset.mem_coe.mpr hitG.hz) hyNe
        ⟨y0 :: (suf ++ [hit]).head hsufNe :: hitG.tail, by simp, hitG.hpe, hitG.hact⟩

end Mettapedia.GSLT.Causality.DoCalculus
