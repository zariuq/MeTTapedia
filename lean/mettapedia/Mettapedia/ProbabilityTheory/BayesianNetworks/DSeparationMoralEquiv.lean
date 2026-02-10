/-
# D-Separation ↔ Moral-Ancestral Separation (Phase 2-3)

LLM primer:
- Edge-by-edge expansion of moral trails FAILS: spouse witnesses may be
  in Anc(X∪Y) \ Anc(Z), so colliders aren't activated.
- KEY LEMMA: if c ∉ Anc(Z), then ∀v reachable from c, v ∉ Z.
- Directed paths from c avoiding Anc(Z) to X∪Y yield active non-collider chains.
- The proof builds active trails by single-prepend (ActiveTrail.cons), using
  a "direction guarantee" on the first edge of the IH result.
- Non-activated spouse edges terminate immediately via directed detour.
-/

import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation

open DirectedGraph

variable {V : Type*}

/-! ## Anc(Z) closure lemmas -/

/-- If c ∉ Anc(Z), nothing reachable from c is in Z. -/
theorem not_in_Z_of_reachable_of_not_in_ancZ
    (G : DirectedGraph V) (Z : Set V) {c v : V}
    (hc : c ∉ ancestorClosure G Z) (hreach : G.Reachable c v) :
    v ∉ Z := by
  intro hv
  exact hc (Or.inr ⟨v, hv, hreach⟩)

/-- If c ∉ Anc(Z), nothing reachable from c is in Anc(Z). -/
theorem not_in_ancZ_of_reachable_of_not_in_ancZ
    (G : DirectedGraph V) (Z : Set V) {c v : V}
    (hc : c ∉ ancestorClosure G Z) (hreach : G.Reachable c v) :
    v ∉ ancestorClosure G Z := by
  intro hv
  rcases hv with hvZ | ⟨z, hzZ, hvz⟩
  · exact hc (Or.inr ⟨v, hvZ, hreach⟩)
  · exact hc (Or.inr ⟨z, hzZ, G.reachable_trans hreach hvz⟩)

/-- Z ⊆ Anc(Z). -/
theorem Z_subset_ancZ (G : DirectedGraph V) (Z : Set V) :
    Z ⊆ ancestorClosure G Z :=
  fun _ h => Or.inl h

/-! ## Directed chains -/

/-- Every consecutive pair has a directed edge. -/
def IsDirectedChain (G : DirectedGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => G.edges u v ∧ IsDirectedChain G (v :: rest)

/-- A directed chain in a DAG is an active trail when internal vertices avoid Z. -/
theorem directedChain_activeTrail
    (G : DirectedGraph V) (Z : Set V) (hacyclic : G.IsAcyclic) :
    ∀ {p : List V},
      IsDirectedChain G p →
      PathAvoidsInternals Z p →
      p ≠ [] →
      ActiveTrail G Z p := by
  intro p
  induction p with
  | nil => intro _ _ h; exact absurd rfl h
  | cons a rest ih =>
    match rest with
    | [] => intro _ _ _; exact ActiveTrail.single a
    | [b] => intro hC _ _; exact ActiveTrail.two (Or.inl hC.1)
    | b :: c :: rest' =>
      intro hC hA _
      have hab : G.edges a b := hC.1
      have hbc : G.edges b c := hC.2.1
      have hbNotZ : b ∉ Z := hA.1
      have hub : UndirectedEdge G a b := Or.inl hab
      have hbcU : UndirectedEdge G b c := Or.inl hbc
      have hac : a ≠ c := fun h => by
        subst h; exact G.isAcyclic_no_two_cycle hacyclic a b hab hbc
      have hNonCol : IsNonCollider G ⟨a, b, c, hub, hbcU, hac⟩ := by
        unfold IsNonCollider IsCollider; intro ⟨_, hcb⟩
        exact G.isAcyclic_no_two_cycle hacyclic b c hbc hcb
      have hAct : IsActive G Z ⟨a, b, c, hub, hbcU, hac⟩ := by
        unfold IsActive IsBlocked; push_neg
        exact ⟨fun _ => hbNotZ, fun h => absurd h hNonCol⟩
      exact ActiveTrail.cons hub hbcU hac hAct
        (ih hC.2 (pathAvoidsInternals_tail hA) (List.cons_ne_nil _ _))

/-! ## Reachability → directed chain -/

/-- From G.Reachable u v, extract a directed chain from u to v. -/
theorem reachable_to_directedChain (G : DirectedGraph V) {u w : V}
    (h : G.Reachable u w) :
    ∃ p : List V, p ≠ [] ∧
      p.head? = some u ∧ p.getLast? = some w ∧
      IsDirectedChain G p := by
  induction h with
  | @refl v =>
    exact ⟨[v], by simp, by simp, by simp [List.getLast?], trivial⟩
  | @step a b _ hab _ ih =>
    rcases ih with ⟨p, hpne, hHead, hLast, hChain⟩
    match p, hpne, hHead with
    | c :: rest, _, hHead =>
      have hcb : c = b := by simpa [List.head?] using hHead
      refine ⟨a :: c :: rest, by simp, by simp, ?_, ?_⟩
      · show (c :: rest).getLast? = some _; exact hLast
      · exact ⟨hcb ▸ hab, hChain⟩

/-- Every vertex on a directed chain is reachable from the first vertex. -/
theorem directedChain_reachable_from_head (G : DirectedGraph V) :
    ∀ {u : V} {p : List V},
      IsDirectedChain G (u :: p) →
      ∀ v ∈ u :: p, G.Reachable u v
  | u, [], _, v, hv => by simp at hv; exact hv ▸ G.reachable_refl u
  | u, w :: rest, hC, v, hv => by
    rcases List.mem_cons.mp hv with heq | hv
    · exact heq ▸ G.reachable_refl u
    · exact G.reachable_trans (G.edge_reachable hC.1)
        (directedChain_reachable_from_head G hC.2 v hv)

/-- PathAvoidsInternals holds when all vertices in the list avoid Z
    (stronger than needed, but convenient). -/
theorem pathAvoidsInternals_of_all_notInZ (Z : Set V) :
    ∀ {p : List V}, (∀ v ∈ p, v ∉ Z) → PathAvoidsInternals Z p := by
  intro p hAll
  induction p with
  | nil => trivial
  | cons a rest ih =>
    match rest with
    | [] => trivial
    | [_] => trivial
    | b :: _ :: _ =>
      exact ⟨hAll b (by simp), ih (fun v hv => hAll v (by simp [hv]))⟩

/-- Convenience wrapper for the common chain shape `x :: c :: rest`. -/
private theorem pathAvoidsInternals_cons_of_all_notInZ
    (Z : Set V) {x c : V} {rest : List V}
    (hAll : ∀ u ∈ c :: rest, u ∉ Z) :
    PathAvoidsInternals Z (x :: c :: rest) := by
  match rest with
  | [] =>
    exact trivial
  | d :: rest' =>
    constructor
    · exact hAll c (List.mem_cons.mpr (Or.inl rfl))
    · exact pathAvoidsInternals_of_all_notInZ Z
        (fun u hu => hAll u (by simp [List.mem_cons] at hu ⊢; tauto))

/-- Convenience wrapper: compute endpoints of `x :: tail` from `tail.getLast?`. -/
private theorem pathEndpoints_cons_eq_of_getLast
    {x w : V} {tail : List V}
    (hLast : tail.getLast? = some w) :
    PathEndpoints (x :: tail) = some (x, w) := by
  have hLast' : (x :: tail).getLast? = some w := by
    match tail with
    | [] =>
      simp [List.getLast?] at hLast
    | _ :: _ =>
      simpa [List.getLast?] using hLast
  exact pathEndpoints_of_head_last (p := x :: tail) (by simp) (by simp) hLast'

/-! ## Moral edge analysis -/

/-- Decompose a moral-ancestral edge into direct or spouse cases. -/
theorem moralAncestralEdge_decompose (G : DirectedGraph V) (X Y Z : Set V)
    {u v : V}
    (h : UndirectedEdge (moralAncestralGraph G X Y Z) u v) :
    (UndirectedEdge G u v ∧
      u ∈ relevantVertices G X Y Z ∧ v ∈ relevantVertices G X Y Z) ∨
    (∃ c, G.edges u c ∧ G.edges v c ∧
      c ∈ relevantVertices G X Y Z ∧
      u ∈ relevantVertices G X Y Z ∧ v ∈ relevantVertices G X Y Z) := by
  rcases h with huv | hvu
  · -- huv : moralUndirectedEdge (inducedSubgraph G W) u v
    rcases huv with ⟨_, hEdge | hSpouse⟩
    · left
      rcases hEdge with huv' | hvu'
      · exact ⟨Or.inl huv'.2.2, huv'.1, huv'.2.1⟩
      · exact ⟨Or.inr hvu'.2.2, hvu'.2.1, hvu'.1⟩
    · right
      rcases hSpouse with ⟨c, huc, hvc⟩
      exact ⟨c, huc.2.2, hvc.2.2, huc.2.1, huc.1, hvc.1⟩
  · -- hvu : moralUndirectedEdge (inducedSubgraph G W) v u
    rcases hvu with ⟨_, hEdge | hSpouse⟩
    · left
      rcases hEdge with hvu' | huv'
      · exact ⟨Or.inr hvu'.2.2, hvu'.2.1, hvu'.1⟩
      · exact ⟨Or.inl huv'.2.2, huv'.1, huv'.2.1⟩
    · right
      rcases hSpouse with ⟨c, hvc, huc⟩
      exact ⟨c, huc.2.2, hvc.2.2, huc.2.1, huc.1, hvc.1⟩

/-! ## relevantVertices membership from X∪Y∪Z -/

theorem relevant_of_X (G : DirectedGraph V) (X Y Z : Set V) {v : V}
    (h : v ∈ X) : v ∈ relevantVertices G X Y Z :=
  endpoint_in_relevant_X G X Y Z h

theorem relevant_of_Y (G : DirectedGraph V) (X Y Z : Set V) {v : V}
    (h : v ∈ Y) : v ∈ relevantVertices G X Y Z :=
  endpoint_in_relevant_Y G X Y Z h

/-- If v ∈ relevantVertices and v ∉ Anc(Z), then v reaches X∪Y. -/
theorem relevant_not_ancZ_reaches_XY
    (G : DirectedGraph V) (X Y Z : Set V) {v : V}
    (hv : v ∈ relevantVertices G X Y Z)
    (hvNotAncZ : v ∉ ancestorClosure G Z) :
    v ∈ X ∪ Y ∨ ∃ w ∈ X ∪ Y, G.Reachable v w ∧ v ≠ w := by
  unfold relevantVertices ancestorClosure at hv
  rcases hv with hvXYZ | ⟨s, hsXYZ, hreach⟩
  · rcases hvXYZ with (hvX | hvY) | hvZ
    · exact Or.inl (Or.inl hvX)
    · exact Or.inl (Or.inr hvY)
    · exact absurd (Z_subset_ancZ G Z hvZ) hvNotAncZ
  · rcases hsXYZ with (hsX | hsY) | hsZ
    · by_cases hvs : v = s
      · subst hvs; exact Or.inl (Or.inl hsX)
      · exact Or.inr ⟨s, Or.inl hsX, hreach, hvs⟩
    · by_cases hvs : v = s
      · subst hvs; exact Or.inl (Or.inr hsY)
      · exact Or.inr ⟨s, Or.inr hsY, hreach, hvs⟩
    · exact absurd (Or.inr ⟨s, hsZ, hreach⟩ : v ∈ ancestorClosure G Z) hvNotAncZ

/-! ## Directed detour through a child to X∪Y -/

/-- Given G.edges v c with c ∈ relevantVertices \ Anc(Z), produce an active
    directed chain from v through c to some w ∈ X∪Y.
    The chain is [v, c, ...] with all internals ∉ Z. -/
theorem directed_detour_through_child
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) {v c : V}
    (hvc : G.edges v c)
    (hcRel : c ∈ relevantVertices G X Y Z)
    (hcAncZ : c ∉ ancestorClosure G Z) :
    ∃ w ∈ X ∪ Y, v ≠ w ∧
      ∃ p : List V, p ≠ [] ∧
        p.head? = some v ∧ p.getLast? = some w ∧
        ActiveTrail G Z p := by
  rcases relevant_not_ancZ_reaches_XY G X Y Z hcRel hcAncZ with hcXY | ⟨w, hwXY, hreach, hcw⟩
  · -- c ∈ X∪Y directly. Active trail [v, c].
    have hvc_ne : v ≠ c := fun h => by subst h; exact G.isAcyclic_irrefl hacyclic v hvc
    exact ⟨c, hcXY, hvc_ne, [v, c], by simp, by simp, by simp [List.getLast?],
      ActiveTrail.two (Or.inl hvc)⟩
  · -- c reaches w ∈ X∪Y with c ≠ w
    rcases reachable_to_directedChain G hreach with ⟨q, hqne, hqHead, hqLast, hqChain⟩
    -- q is a directed chain from c to w. Prepend v.
    match q, hqne, hqHead with
    | c' :: qrest, _, hqHead =>
      have hcc' : c' = c := by simpa using hqHead
      -- Build chain [v, c', ...qrest]
      have hChain : IsDirectedChain G (v :: c' :: qrest) := ⟨hcc' ▸ hvc, hqChain⟩
      -- All vertices on chain from c onward are ∉ Z (since c ∉ Anc(Z))
      have hcNotZ : ∀ u ∈ c' :: qrest, u ∉ Z := by
        intro u hu
        have hcu : G.Reachable c u := by
          exact hcc' ▸ directedChain_reachable_from_head G hqChain u hu
        exact not_in_Z_of_reachable_of_not_in_ancZ G Z hcAncZ hcu
      -- PathAvoidsInternals: internal vertices of [v, c', ...qrest] are c' and qrest internals
      -- c' ∉ Z (from hcNotZ), and all qrest vertices ∉ Z
      have hAvoid : PathAvoidsInternals Z (v :: c' :: qrest) := by
        exact pathAvoidsInternals_cons_of_all_notInZ Z hcNotZ
      have hAT : ActiveTrail G Z (v :: c' :: qrest) :=
        directedChain_activeTrail G Z hacyclic hChain hAvoid (by simp)
      have hvw : v ≠ w := by
        intro hvw; subst hvw
        -- v→c and c reaches w = v, giving v→c→...→v, a cycle
        exact G.isAcyclic_iff_no_self_reach.mp hacyclic v c hvc
          (G.reachable_trans hreach (G.reachable_refl v))
      exact ⟨w, hwXY, hvw, v :: c' :: qrest, by simp, by simp,
        by show (c' :: qrest).getLast? = some w; exact hqLast,
        hAT⟩

/-- PathAvoidsInternals for q ++ [y]: only q's elements are internal,
    and y (the last vertex) is never checked. -/
theorem pathAvoidsInternals_append_endpoint (Z : Set V) :
    ∀ {q : List V} {y : V},
      (∀ v ∈ q, v ∉ Z) → q ≠ [] → PathAvoidsInternals Z (q ++ [y]) := by
  intro q y hNotZ hne
  induction q with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    match rest with
    | [] => exact trivial
    | [b] => exact ⟨hNotZ b (by simp), trivial⟩
    | b :: c :: rest' =>
      exact ⟨hNotZ b (by simp),
        ih (fun v hv => hNotZ v (by simp [List.mem_cons] at hv ⊢; tauto)) (by simp)⟩

/-! ## Backward chains (reversed directed chains) -/

/-- Every consecutive pair has a backward directed edge: G.edges v u. -/
def IsBackwardChain (G : DirectedGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => G.edges v u ∧ IsBackwardChain G (v :: rest)

/-- A backward chain in a DAG is an active trail when internal vertices avoid Z.
    At each triple (a,b,c): G.edges b a and G.edges c b.
    Collider would need G.edges a b ∧ G.edges c b, but DAG forbids G.edges a b
    when G.edges b a exists. So every internal node is a non-collider. -/
theorem backwardChain_activeTrail
    (G : DirectedGraph V) (Z : Set V) (hacyclic : G.IsAcyclic) :
    ∀ {p : List V},
      IsBackwardChain G p →
      PathAvoidsInternals Z p →
      p ≠ [] →
      ActiveTrail G Z p := by
  intro p
  induction p with
  | nil => intro _ _ h; exact absurd rfl h
  | cons a rest ih =>
    match rest with
    | [] => intro _ _ _; exact ActiveTrail.single a
    | [b] => intro hC _ _; exact ActiveTrail.two (Or.inr hC.1)
    | b :: c :: rest' =>
      intro hC hA _
      have hba : G.edges b a := hC.1
      have hcb : G.edges c b := hC.2.1
      have hbNotZ : b ∉ Z := hA.1
      have hub : UndirectedEdge G a b := Or.inr hba
      have hbcU : UndirectedEdge G b c := Or.inr hcb
      have hac : a ≠ c := fun h => by
        subst h; exact G.isAcyclic_no_two_cycle hacyclic b a hba hcb
      have hNonCol : IsNonCollider G ⟨a, b, c, hub, hbcU, hac⟩ := by
        unfold IsNonCollider IsCollider; intro ⟨hab, _⟩
        exact G.isAcyclic_no_two_cycle hacyclic b a hba hab
      have hAct : IsActive G Z ⟨a, b, c, hub, hbcU, hac⟩ := by
        unfold IsActive IsBlocked; push_neg
        exact ⟨fun _ => hbNotZ, fun h => absurd h hNonCol⟩
      exact ActiveTrail.cons hub hbcU hac hAct
        (ih hC.2 (pathAvoidsInternals_tail hA) (List.cons_ne_nil _ _))

/-- Extend a backward chain by appending one element. -/
theorem isBackwardChain_append_singleton
    (G : DirectedGraph V) :
    ∀ {p : List V} {b a : V},
      IsBackwardChain G p →
      p.getLast? = some b →
      G.edges a b →
      IsBackwardChain G (p ++ [a])
  | [_], _, _, _, hLast, hab => by
    simp [List.getLast?] at hLast; subst hLast
    exact ⟨hab, trivial⟩
  | c :: d :: rest, b, a, hChain, hLast, hab => by
    show G.edges d c ∧ IsBackwardChain G ((d :: rest) ++ [a])
    exact ⟨hChain.1, isBackwardChain_append_singleton G hChain.2
      (by simpa [List.getLast?] using hLast) hab⟩

/-- From G.Reachable u w with u ∉ Anc(Z), extract a backward chain from w to u
    with all vertices ∉ Z. -/
theorem reachable_to_backwardChain_avoidZ
    (G : DirectedGraph V) (Z : Set V) {u w : V}
    (h : G.Reachable u w) (huNotAncZ : u ∉ ancestorClosure G Z) :
    ∃ p : List V, p ≠ [] ∧
      p.head? = some w ∧ p.getLast? = some u ∧
      IsBackwardChain G p ∧
      (∀ v ∈ p, v ∉ Z) := by
  induction h with
  | refl =>
    rename_i v
    refine ⟨[v], by simp, rfl, by simp [List.getLast?], trivial, fun s hs => ?_⟩
    simp at hs
    exact hs ▸ not_in_Z_of_reachable_of_not_in_ancZ G Z huNotAncZ (G.reachable_refl _)
  | @step a b _ hab hbw ih =>
    have hbNotAncZ : b ∉ ancestorClosure G Z :=
      not_in_ancZ_of_reachable_of_not_in_ancZ G Z huNotAncZ (G.edge_reachable hab)
    rcases ih hbNotAncZ with ⟨q, hqne, hqHead, hqLast, hqBack, hqAvoid⟩
    refine ⟨q ++ [a], by simp, ?_, ?_, ?_, ?_⟩
    · match q, hqne, hqHead with
      | c :: _, _, hh => simpa using hh
    · -- getLast? of (q ++ [a]) = some a
      match q, hqne with
      | c :: rest, _ => simp [List.getLast?]
    · match q, hqne, hqLast with
      | [_], _, hLast => simp [List.getLast?] at hLast; subst hLast; exact ⟨hab, trivial⟩
      | c :: d :: rest, _, hLast =>
        exact ⟨(hqBack).1, isBackwardChain_append_singleton G hqBack.2
          (by simpa [List.getLast?] using hLast) hab⟩
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hqAvoid s hs
      · simp at hs; subst hs
        exact not_in_Z_of_reachable_of_not_in_ancZ G Z huNotAncZ (G.reachable_refl _)

/-! ## Main theorem: ¬SepMoral → ¬DSepFull -/

/-- Decompose endpoints for a trail with at least three vertices. -/
private theorem pathEndpoints_cons_cons_cons
    {a b c x y : V} {rest : List V}
    (hEnds : PathEndpoints (a :: b :: c :: rest) = some (x, y)) :
    a = x ∧ PathEndpoints (b :: c :: rest) = some (b, y) := by
  have hSome :
      some (a, (b :: c :: rest).getLast (by simp)) = some (x, y) := by
    simpa [PathEndpoints] using hEnds
  have hPair : (a, (b :: c :: rest).getLast (by simp)) = (x, y) :=
    Option.some.inj hSome
  have hPair' : a = x ∧ (b :: c :: rest).getLast (by simp) = y := by
    simpa using hPair
  have hLast : (c :: rest).getLast (by simp) = y := by
    simpa [List.getLast_cons] using hPair'.2
  constructor
  · exact hPair'.1
  · simpa [PathEndpoints, hLast]

/-- The right endpoint of a moral-ancestral edge lies in relevant vertices. -/
private theorem right_relevant_of_moral_edge
    (G : DirectedGraph V) (X Y Z : Set V) {x b : V}
    (hEdge : UndirectedEdge (moralAncestralGraph G X Y Z) x b) :
    b ∈ relevantVertices G X Y Z := by
  rcases moralAncestralEdge_decompose G X Y Z hEdge with
    ⟨_, _, hbR⟩ | ⟨_, _, _, _, _, hbR⟩
  · exact hbR
  · exact hbR

/-- Moral-ancestral undirected edges are irreflexive. -/
private theorem ne_of_moral_undirected_edge
    (G : DirectedGraph V) (X Y Z : Set V) {x b : V}
    (hEdge : UndirectedEdge (moralAncestralGraph G X Y Z) x b) :
    x ≠ b := by
  intro hxb
  rw [hxb] at hEdge
  rcases hEdge with hE | hE
  · exact hE.1 rfl
  · exact hE.1 rfl

/-- Base case helper: single moral edge from x∈X to y∈Y. -/
private theorem base_case_single_edge
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y) (hxy : x ≠ y)
    (hEdge : UndirectedEdge (moralAncestralGraph G X Y Z) x y) :
    ¬DSeparatedFull G X Y Z := by
  intro hDSep
  rcases moralAncestralEdge_decompose G X Y Z hEdge with
    ⟨hDirect, _, _⟩ | ⟨c, hxc, hyc, hcRel, _, _⟩
  · -- Direct edge: [x, y] is active trail
    exact hDSep x hx y hy hxy ⟨[x, y], by simp, by simp [PathEndpoints],
      ActiveTrail.two hDirect⟩
  · -- Spouse edge via c: G.edges x c ∧ G.edges y c
    by_cases hcAncZ : c ∈ ancestorClosure G Z
    · -- c ∈ Anc(Z): collider x→c←y is activated
      have hxc_ne : x ≠ c := fun h => by subst h; exact G.isAcyclic_irrefl hacyclic x hxc
      have hyc_ne : y ≠ c := fun h => by subst h; exact G.isAcyclic_irrefl hacyclic y hyc
      have hub : UndirectedEdge G x c := Or.inl hxc
      have hcv : UndirectedEdge G c y := Or.inr hyc
      have hCol : IsCollider G ⟨x, c, y, hub, hcv, hxy⟩ := ⟨hxc, hyc⟩
      have hAct : IsActive G Z ⟨x, c, y, hub, hcv, hxy⟩ :=
        isActive_of_collider_and_activated G Z ⟨x, c, y, hub, hcv, hxy⟩ hCol hcAncZ
      exact hDSep x hx y hy hxy ⟨[x, c, y], by simp, by simp [PathEndpoints],
        ActiveTrail.cons hub hcv hxy hAct (ActiveTrail.two hcv)⟩
    · -- c ∉ Anc(Z): detour to X∪Y
      rcases relevant_not_ancZ_reaches_XY G X Y Z hcRel hcAncZ with hcXY | ⟨w, hwXY, hreach, hcw⟩
      · -- c ∈ X∪Y directly
        rcases hcXY with hcX | hcY
        · -- c ∈ X: trail [c, y], c∈X, y∈Y
          have hcy_ne : c ≠ y := fun h => by subst h; exact G.isAcyclic_irrefl hacyclic c hyc
          exact hDSep c hcX y hy hcy_ne ⟨[c, y], by simp, by simp [PathEndpoints],
            ActiveTrail.two (Or.inr hyc)⟩
        · -- c ∈ Y: trail [x, c], x∈X, c∈Y
          have hxc_ne : x ≠ c := fun h => by subst h; exact G.isAcyclic_irrefl hacyclic x hxc
          exact hDSep x hx c hcY hxc_ne ⟨[x, c], by simp, by simp [PathEndpoints],
            ActiveTrail.two (Or.inl hxc)⟩
      · -- c reaches w ∈ X∪Y, c ≠ w
        rcases hwXY with hwX | hwY
        · -- w ∈ X: backward chain [w, ..., c] then append y → [w, ..., c, y]
          rcases reachable_to_backwardChain_avoidZ G Z hreach hcAncZ with
            ⟨q, hqne, hqHead, hqLast, hqBack, hqNotZ⟩
          -- Extend backward chain: append y with edge G.edges y c
          have hBack : IsBackwardChain G (q ++ [y]) := by
            match q, hqne, hqLast with
            | [_], _, hL =>
              simp [List.getLast?] at hL; subst hL; exact ⟨hyc, trivial⟩
            | _ :: _ :: _, _, hL =>
              exact ⟨hqBack.1, isBackwardChain_append_singleton G hqBack.2
                (by simpa [List.getLast?] using hL) hyc⟩
          have hwy_ne : w ≠ y := by
            intro heq; have hcy : G.Reachable c y := heq ▸ hreach
            exact G.isAcyclic_iff_no_self_reach.mp hacyclic y c hyc hcy
          -- PathAvoidsInternals: internals of [w, ..., c, y] are the q-tail
          -- elements (all ∉ Z by hqNotZ) and c (also ∉ Z).
          have hAvoidQy : PathAvoidsInternals Z (q ++ [y]) :=
            pathAvoidsInternals_append_endpoint Z hqNotZ hqne
          -- PathEndpoints
          have hPE : PathEndpoints (q ++ [y]) = some (w, y) := by
            match q, hqne, hqHead with
            | [a], _, hH =>
              simp at hH; simp [PathEndpoints, hH]
            | a :: b :: rest, _, hH =>
              have haw : a = w := by simpa using hH
              simp [PathEndpoints, haw]
          exact hDSep w hwX y hy hwy_ne
            ⟨q ++ [y], by simp, hPE,
             backwardChain_activeTrail G Z hacyclic hBack hAvoidQy (by simp)⟩
        · -- w ∈ Y: forward chain [x, c, ..., w]
          rcases reachable_to_directedChain G hreach with
            ⟨q, hqne, hqHead, hqLast, hqChain⟩
          match q, hqne, hqHead with
          | c' :: qrest, _, hqH =>
            have hcc' : c' = c := by simpa using hqH
            have hFwd : IsDirectedChain G (x :: c' :: qrest) := ⟨hcc' ▸ hxc, hqChain⟩
            have hxw_ne : x ≠ w := by
              intro heq; subst heq
              -- x→c and c reaches x, giving cycle
              exact G.isAcyclic_iff_no_self_reach.mp hacyclic x c hxc hreach
            -- All vertices from c onward ∉ Z
            have hcNotZ : ∀ u ∈ c' :: qrest, u ∉ Z := by
              intro u hu
              exact not_in_Z_of_reachable_of_not_in_ancZ G Z hcAncZ
                (hcc' ▸ directedChain_reachable_from_head G hqChain u hu)
            have hAvoidP : PathAvoidsInternals Z (x :: c' :: qrest) := by
              exact pathAvoidsInternals_cons_of_all_notInZ Z hcNotZ
            have hAT : ActiveTrail G Z (x :: c' :: qrest) :=
              directedChain_activeTrail G Z hacyclic hFwd hAvoidP (by simp)
            have hPE : PathEndpoints (x :: c' :: qrest) = some (x, w) := by
              exact pathEndpoints_cons_eq_of_getLast hqLast
            exact hDSep x hx w hwY hxw_ne
              ⟨x :: c' :: qrest, by simp, hPE, hAT⟩

/-- Helper: package contradiction from one explicit active-trail witness. -/
private theorem absurd_dsep_of_activeTrail
    (G : DirectedGraph V) (X Y Z : Set V)
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y) (hxy : x ≠ y)
    {p : List V} (hpne : p ≠ [])
    (hEnds : PathEndpoints p = some (x, y))
    (hAT : ActiveTrail G Z p)
    (hDSep : DSeparatedFull G X Y Z) :
    False := by
  exact hDSep x hx y hy hxy ⟨p, hpne, hEnds, hAT⟩

/-- Reusable contradiction helper:
if `x ∈ X`, `w ∈ Y`, and there is an edge `x → c` with `c ↠ w`,
then (provided `c ∉ Anc(Z)`) we can build an active trail from `x` to `w`. -/
private theorem absurd_dsep_of_forward_detour_to_Y
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {x c w : V}
    (hx : x ∈ X) (hwY : w ∈ Y)
    (hxc : G.edges x c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z) :
    ¬DSeparatedFull G X Y Z := by
  intro hDSep
  rcases reachable_to_directedChain G hreach with
    ⟨q, hqne, hqHead, hqLast, hqChain⟩
  match q, hqne, hqHead with
  | c' :: qrest, _, hqH =>
    have hcc' : c' = c := by simpa using hqH
    have hFwd : IsDirectedChain G (x :: c' :: qrest) :=
      ⟨hcc' ▸ hxc, hqChain⟩
    have hcNotZ : ∀ u ∈ c' :: qrest, u ∉ Z :=
      fun u hu => not_in_Z_of_reachable_of_not_in_ancZ G Z hcNotAncZ
        (hcc' ▸ directedChain_reachable_from_head G hqChain u hu)
    have hAvoidFwd : PathAvoidsInternals Z (x :: c' :: qrest) :=
      pathAvoidsInternals_cons_of_all_notInZ Z hcNotZ
    have hAT : ActiveTrail G Z (x :: c' :: qrest) :=
      directedChain_activeTrail G Z hacyclic hFwd hAvoidFwd (by simp)
    have hxw_ne : x ≠ w := by
      intro heq
      subst heq
      exact G.isAcyclic_iff_no_self_reach.mp hacyclic x c hxc hreach
    have hPE : PathEndpoints (x :: c' :: qrest) = some (x, w) :=
      pathEndpoints_cons_eq_of_getLast hqLast
    exact absurd_dsep_of_activeTrail G X Y Z hx hwY hxw_ne
      (by simp) hPE hAT hDSep

/-- Witness-form mirror of `absurd_dsep_of_forward_detour_to_Y`. -/
private theorem activeWitness_of_forward_detour_to_Y
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {x c w : V}
    (hx : x ∈ X) (hwY : w ∈ Y)
    (hxc : G.edges x c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z) :
    ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
  rcases reachable_to_directedChain G hreach with
    ⟨q, hqne, hqHead, hqLast, hqChain⟩
  match q, hqne, hqHead with
  | c' :: qrest, _, hqH =>
    have hcc' : c' = c := by simpa using hqH
    have hFwd : IsDirectedChain G (x :: c' :: qrest) :=
      ⟨hcc' ▸ hxc, hqChain⟩
    have hcNotZ : ∀ u ∈ c' :: qrest, u ∉ Z :=
      fun u hu => not_in_Z_of_reachable_of_not_in_ancZ G Z hcNotAncZ
        (hcc' ▸ directedChain_reachable_from_head G hqChain u hu)
    have hAvoidFwd : PathAvoidsInternals Z (x :: c' :: qrest) :=
      pathAvoidsInternals_cons_of_all_notInZ Z hcNotZ
    have hAT : ActiveTrail G Z (x :: c' :: qrest) :=
      directedChain_activeTrail G Z hacyclic hFwd hAvoidFwd (by simp)
    have hxw_ne : x ≠ w := by
      intro heq
      subst heq
      exact G.isAcyclic_iff_no_self_reach.mp hacyclic x c hxc hreach
    have hPE : PathEndpoints (x :: c' :: qrest) = some (x, w) :=
      pathEndpoints_cons_eq_of_getLast hqLast
    refine ⟨x, hx, w, hwY, hxw_ne, ?_⟩
    exact ⟨x :: c' :: qrest, by simp, hPE, hAT⟩

/-- X-side mirror: if `y ∈ Y`, `w ∈ X`, `y → c`, and `c ↠ w` with `c ∉ Anc(Z)`,
build an explicit active witness from `X` to `Y`. -/
private theorem activeWitness_of_backward_detour_to_X
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w c y : V}
    (hwX : w ∈ X) (hy : y ∈ Y)
    (hyc : G.edges y c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z) :
    ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
  rcases reachable_to_backwardChain_avoidZ G Z hreach hcNotAncZ with
    ⟨q, hqne, hqHead, hqLast, hqBack, hqNotZ⟩
  have hBack : IsBackwardChain G (q ++ [y]) := by
    match q, hqne, hqLast with
    | [_], _, hL =>
      simp [List.getLast?] at hL
      subst hL
      exact ⟨hyc, trivial⟩
    | _ :: _ :: _, _, hL =>
      exact ⟨hqBack.1, isBackwardChain_append_singleton G hqBack.2
        (by simpa [List.getLast?] using hL) hyc⟩
  have hwy_ne : w ≠ y := by
    intro heq
    have hcy : G.Reachable c y := heq ▸ hreach
    exact G.isAcyclic_iff_no_self_reach.mp hacyclic y c hyc hcy
  have hAvoidQy : PathAvoidsInternals Z (q ++ [y]) :=
    pathAvoidsInternals_append_endpoint Z hqNotZ hqne
  have hPE : PathEndpoints (q ++ [y]) = some (w, y) := by
    match q, hqne, hqHead with
    | [a], _, hH =>
      simp at hH
      simp [PathEndpoints, hH]
    | a :: b :: rest, _, hH =>
      have haw : a = w := by simpa using hH
      simp [PathEndpoints, haw]
  refine ⟨w, hwX, y, hy, hwy_ne, ?_⟩
  exact ⟨q ++ [y], by simp, hPE,
    backwardChain_activeTrail G Z hacyclic hBack hAvoidQy (by simp)⟩

/-- Package `reachable_to_directedChain` with the standard non-ancestor-to-avoid-Z
argument used repeatedly in the moral-to-active conversion proof. -/
private theorem reachable_chain_avoidZ_of_not_ancZ
    (G : DirectedGraph V) (Z : Set V)
    {b w : V}
    (hreach : G.Reachable b w)
    (hbNotAncZ : b ∉ ancestorClosure G Z) :
    ∃ q : List V,
      q ≠ [] ∧
      q.head? = some b ∧
      q.getLast? = some w ∧
      IsDirectedChain G q ∧
      (∀ u ∈ q, u ∉ Z) := by
  rcases reachable_to_directedChain G hreach with ⟨q, hqne, hqHead, hqLast, hqChain⟩
  match q, hqne, hqHead with
  | b' :: qrest, _, hqH =>
    have hbb' : b' = b := by simpa using hqH
    have hAvoid : ∀ u ∈ b' :: qrest, u ∉ Z := by
      intro u hu
      exact not_in_Z_of_reachable_of_not_in_ancZ G Z hbNotAncZ
        (hbb' ▸ directedChain_reachable_from_head G hqChain u hu)
    exact ⟨b' :: qrest, by simp, by simp [hqH], hqLast, hqChain, hAvoid⟩

/-- Extract the reusable tail context from a `x :: b :: c :: rest` moral trail. -/
private theorem tail_context_of_three_plus
    (G : DirectedGraph V) (X Y Z : Set V)
    {x y b c : V} {rest : List V}
    (hEnds : PathEndpoints (x :: b :: c :: rest) = some (x, y))
    (hTrail : IsTrail (moralAncestralGraph G X Y Z) (x :: b :: c :: rest))
    (hAvoid : PathAvoidsInternals Z (x :: b :: c :: rest)) :
    UndirectedEdge (moralAncestralGraph G X Y Z) x b ∧
    IsTrail (moralAncestralGraph G X Y Z) (b :: c :: rest) ∧
    PathAvoidsInternals Z (b :: c :: rest) ∧
    b ∉ Z ∧
    PathEndpoints (b :: c :: rest) = some (b, y) := by
  have hEP := pathEndpoints_cons_cons_cons (hEnds := hEnds)
  have hEdge_xb : UndirectedEdge (moralAncestralGraph G X Y Z) x b := by
    cases hTrail with
    | cons hE _ => exact hE
  have hTailTrail : IsTrail (moralAncestralGraph G X Y Z) (b :: c :: rest) := by
    cases hTrail with
    | cons _ hT' => exact hT'
  exact ⟨hEdge_xb, hTailTrail, hAvoid.2, hAvoid.1, hEP.2⟩

/-- Unpack `¬DSeparatedFull` into an explicit active-trail witness
between some pair in `X × Y`. -/
private theorem activeWitness_of_not_dsepFull
    (G : DirectedGraph V) (X Y Z : Set V)
    (hNot : ¬DSeparatedFull G X Y Z) :
    ∃ x ∈ X, ∃ y ∈ Y, x ≠ y ∧ HasActiveTrail G Z x y := by
  classical
  unfold DSeparatedFull at hNot
  push_neg at hNot
  rcases hNot with ⟨x, hx, y, hy, hxy, hAT⟩
  exact ⟨x, hx, y, hy, hxy, hAT⟩

/-- Route-A state: some `X` endpoint is already actively connected to the current
head vertex. This lets the moral-trail induction recurse even when the head itself
is not in `X`. -/
private def ActiveFromX (G : DirectedGraph V) (X Z : Set V) (a : V) : Prop :=
  ∃ x ∈ X, HasActiveTrail G Z x a

/-- Local passability mode at the current head vertex:
either we can justify non-collider activation via `a ∉ Z`,
or collider activation via `a ∈ Anc(Z)`. -/
private inductive HeadPassability (G : DirectedGraph V) (Z : Set V) (a : V) : Prop
  | noncollider (hNotZ : a ∉ Z)
  | collider (hAncZ : a ∈ ancestorClosure G Z)

/-- Orientation of an incident edge at a head vertex:
incoming means the edge points into the head, outgoing means it points out. -/
private inductive JoinEdgeDir
  | incoming
  | outgoing
deriving DecidableEq

/-- Edge-direction witness specialized at the head endpoint of an undirected edge. -/
private def edgeMatchesHeadDir
    (G : DirectedGraph V) {u a : V}
    (dir : JoinEdgeDir) : Prop :=
  match dir with
  | JoinEdgeDir.incoming => G.edges u a
  | JoinEdgeDir.outgoing => G.edges a u

/-- Required activation side-condition at the join vertex when composing an
existing active segment (with head-incidence `prev`) and one new step
(`next`).

Only the incoming/incoming pattern is a collider join and therefore needs
`a ∈ Anc(Z)`. Every other local orientation is a non-collider join and needs
`a ∉ Z`. -/
private def JoinConditionAtHead
    (G : DirectedGraph V) (Z : Set V) (a : V)
    (prev next : JoinEdgeDir) : Prop :=
  if prev = JoinEdgeDir.incoming ∧ next = JoinEdgeDir.incoming then
    a ∈ ancestorClosure G Z
  else
    a ∉ Z

/-- Collider join specialization: incoming/incoming needs `a ∈ Anc(Z)`. -/
private theorem joinConditionAtHead_in_in
    (G : DirectedGraph V) (Z : Set V) (a : V)
    (haAncZ : a ∈ ancestorClosure G Z) :
    JoinConditionAtHead G Z a JoinEdgeDir.incoming JoinEdgeDir.incoming := by
  simp [JoinConditionAtHead, haAncZ]

/-- Non-collider join specialization: all orientation patterns except incoming/incoming
need `a ∉ Z`. -/
private theorem joinConditionAtHead_noncollider
    (G : DirectedGraph V) (Z : Set V) (a : V)
    {prev next : JoinEdgeDir}
    (haNotZ : a ∉ Z)
    (hNotBothIn : ¬ (prev = JoinEdgeDir.incoming ∧ next = JoinEdgeDir.incoming)) :
    JoinConditionAtHead G Z a prev next := by
  simp [JoinConditionAtHead, hNotBothIn, haNotZ]

/-- Reusable local join rule: once the caller provides the exact obligation
for each collider/non-collider case of the join triple, activation follows. -/
private theorem isActive_of_join_obligations
    (G : DirectedGraph V) (Z : Set V)
    {u a b : V}
    (hua : UndirectedEdge G u a) (hab : UndirectedEdge G a b) (hub : u ≠ b)
    (hNonCol : IsNonCollider G ⟨u, a, b, hua, hab, hub⟩ → a ∉ Z)
    (hCol : IsCollider G ⟨u, a, b, hua, hab, hub⟩ → a ∈ ancestorClosure G Z) :
    IsActive G Z ⟨u, a, b, hua, hab, hub⟩ := by
  by_cases hcol : IsCollider G ⟨u, a, b, hua, hab, hub⟩
  · exact isActive_of_collider_and_activated G Z ⟨u, a, b, hua, hab, hub⟩ hcol (hCol hcol)
  · have hnoncol : IsNonCollider G ⟨u, a, b, hua, hab, hub⟩ := hcol
    have haNotZ : a ∉ Z := hNonCol hnoncol
    unfold IsActive IsBlocked
    intro hBlocked
    rcases hBlocked with ⟨hnc, haInZ⟩ | ⟨hcol', _, _⟩
    · exact haNotZ haInZ
    · exact hcol hcol'

/-- Strengthened recursion state for Route A:
an X-anchor active witness to the current head plus a passability certificate
used to avoid repetitive ad-hoc case splits in edge-extension branches. -/
private structure ActiveFromXState (G : DirectedGraph V) (X Z : Set V) (a : V) : Prop where
  active : ActiveFromX G X Z a
  passable : HeadPassability G Z a

/-- Build a head-passability certificate from `a ∉ Z`. -/
private theorem headPassability_of_notInZ
    (G : DirectedGraph V) (Z : Set V) {a : V}
    (haNotZ : a ∉ Z) :
    HeadPassability G Z a :=
  HeadPassability.noncollider haNotZ

/-- Build a head-passability certificate from `a ∈ Anc(Z)`. -/
private theorem headPassability_of_ancZ
    (G : DirectedGraph V) (Z : Set V) {a : V}
    (haAncZ : a ∈ ancestorClosure G Z) :
    HeadPassability G Z a :=
  HeadPassability.collider haAncZ

/-- Default head-passability (classical): either `a ∉ Z`, or `a ∈ Z ⊆ Anc(Z)`. -/
private theorem headPassability_default
    (G : DirectedGraph V) (Z : Set V) (a : V) :
    HeadPassability G Z a := by
  classical
  by_cases haZ : a ∈ Z
  · exact HeadPassability.collider (Or.inl haZ)
  · exact HeadPassability.noncollider haZ

/-- Lift an `ActiveFromX` witness into the strengthened state with a default
passability certificate at the same head. -/
private theorem activeFromXState_of_activeFromX
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (hAX : ActiveFromX G X Z a) :
    ActiveFromXState G X Z a := by
  exact ⟨hAX, headPassability_default G Z a⟩

/-- Lift an `ActiveFromX` witness with explicit `a ∉ Z` passability. -/
private theorem activeFromXState_of_activeFromX_notInZ
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (hAX : ActiveFromX G X Z a) (haNotZ : a ∉ Z) :
    ActiveFromXState G X Z a := by
  exact ⟨hAX, headPassability_of_notInZ G Z haNotZ⟩

/-- Lift an `ActiveFromX` witness with explicit `a ∈ Anc(Z)` passability. -/
private theorem activeFromXState_of_activeFromX_ancZ
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (hAX : ActiveFromX G X Z a) (haAncZ : a ∈ ancestorClosure G Z) :
    ActiveFromXState G X Z a := by
  exact ⟨hAX, headPassability_of_ancZ G Z haAncZ⟩

/-- Seed `ActiveFromX` from direct membership in `X`. -/
private theorem activeFromX_of_memX
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (haX : a ∈ X) :
    ActiveFromX G X Z a := by
  refine ⟨a, haX, ?_⟩
  exact ⟨[a], by simp, by simp [PathEndpoints], ActiveTrail.single a⟩

/-- Extend `ActiveFromX` by one directed edge from an `X` vertex. -/
private theorem activeFromX_of_edge_from_X
    (G : DirectedGraph V) (X Z : Set V) {x a : V}
    (hxX : x ∈ X) (hxa : G.edges x a) :
    ActiveFromX G X Z a := by
  refine ⟨x, hxX, ?_⟩
  exact ⟨[x, a], by simp, by simp [PathEndpoints], ActiveTrail.two (Or.inl hxa)⟩

/-- Extend `ActiveFromX` by one directed edge into an `X` vertex. -/
private theorem activeFromX_of_edge_to_X
    (G : DirectedGraph V) (X Z : Set V) {x a : V}
    (hxX : x ∈ X) (hax : G.edges a x) :
    ActiveFromX G X Z a := by
  refine ⟨x, hxX, ?_⟩
  exact ⟨[x, a], by simp, by simp [PathEndpoints], ActiveTrail.two (Or.inr hax)⟩

/-- Seed the strengthened state from direct membership in `X`. -/
private theorem activeFromXState_of_memX
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (haX : a ∈ X) :
    ActiveFromXState G X Z a := by
  exact activeFromXState_of_activeFromX G X Z (activeFromX_of_memX G X Z haX)

/-- Seed state from `a ∈ X` with explicit `a ∉ Z` passability. -/
private theorem activeFromXState_of_memX_notInZ
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (haX : a ∈ X) (haNotZ : a ∉ Z) :
    ActiveFromXState G X Z a := by
  exact activeFromXState_of_activeFromX_notInZ G X Z
    (activeFromX_of_memX G X Z haX) haNotZ

/-- Seed state from `a ∈ X` with explicit `a ∈ Anc(Z)` passability. -/
private theorem activeFromXState_of_memX_ancZ
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (haX : a ∈ X) (haAncZ : a ∈ ancestorClosure G Z) :
    ActiveFromXState G X Z a := by
  exact activeFromXState_of_activeFromX_ancZ G X Z
    (activeFromX_of_memX G X Z haX) haAncZ

/-- Direct-edge transition for the `ActiveFromX` state when the current head is in `X`. -/
private theorem activeFromX_direct_transition
    (G : DirectedGraph V) (X Z : Set V) {a b : V}
    (haX : a ∈ X) (hDirect : UndirectedEdge G a b) :
    ActiveFromX G X Z b := by
  rcases hDirect with hab | hba
  · exact activeFromX_of_edge_from_X G X Z haX hab
  · exact activeFromX_of_edge_to_X G X Z haX hba

/-- Activated-spouse transition for the `ActiveFromX` state when the current head is in `X`.
This realizes the standard active collider segment `a → c ← b` (read as
undirected trail `a ~ c ~ b`) under `c ∈ Anc(Z)`. -/
private theorem activeFromX_spouse_activated_transition
    (G : DirectedGraph V) (X Z : Set V)
    {a b c : V}
    (haX : a ∈ X) (hab : a ≠ b)
    (hac : G.edges a c) (hbc : G.edges b c)
    (hcAncZ : c ∈ ancestorClosure G Z) :
    ActiveFromX G X Z b := by
  let hub : UndirectedEdge G a c := Or.inl hac
  let hcv : UndirectedEdge G c b := Or.inr hbc
  have hCol : IsCollider G ⟨a, c, b, hub, hcv, hab⟩ := ⟨hac, hbc⟩
  have hAct : IsActive G Z ⟨a, c, b, hub, hcv, hab⟩ :=
    isActive_of_collider_and_activated G Z ⟨a, c, b, hub, hcv, hab⟩ hCol hcAncZ
  refine ⟨a, haX, ?_⟩
  refine ⟨[a, c, b], by simp, by simp [PathEndpoints], ?_⟩
  exact ActiveTrail.cons hub hcv hab hAct (ActiveTrail.two hcv)

/-- X-side detour update:
if `b → c`, `c ↠ w`, `w ∈ X`, and `c ∉ Anc(Z)`, then `b` gains an `ActiveFromX`
state via the backward chain `w ↝ c` followed by the edge `b → c`. -/
private theorem activeFromX_of_backward_detour_to_X_at_b
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w c b : V}
    (hwX : w ∈ X)
    (hbc : G.edges b c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z) :
    ActiveFromX G X Z b := by
  rcases reachable_to_backwardChain_avoidZ G Z hreach hcNotAncZ with
    ⟨q, hqne, hqHead, hqLast, hqBack, hqNotZ⟩
  have hBack : IsBackwardChain G (q ++ [b]) := by
    match q, hqne, hqLast with
    | [_], _, hL =>
      simp [List.getLast?] at hL
      subst hL
      exact ⟨hbc, trivial⟩
    | _ :: _ :: _, _, hL =>
      exact ⟨hqBack.1, isBackwardChain_append_singleton G hqBack.2
        (by simpa [List.getLast?] using hL) hbc⟩
  have hAvoidQb : PathAvoidsInternals Z (q ++ [b]) :=
    pathAvoidsInternals_append_endpoint Z hqNotZ hqne
  have hPE : PathEndpoints (q ++ [b]) = some (w, b) := by
    match q, hqne, hqHead with
    | [a], _, hH =>
      simp at hH
      simp [PathEndpoints, hH]
    | a :: d :: rest, _, hH =>
      have haw : a = w := by simpa using hH
      simp [PathEndpoints, haw]
  refine ⟨w, hwX, ?_⟩
  exact ⟨q ++ [b], by simp, hPE,
    backwardChain_activeTrail G Z hacyclic hBack hAvoidQb (by simp)⟩

/-- Direct backward-reach update at the current head:
if `b ↠ w`, `w ∈ X`, and `b ∉ Anc(Z)`, then `b` has an `ActiveFromX` witness
by reversing the directed chain from `b` to `w`. -/
private theorem activeFromX_of_backward_reach_to_X_at_head
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w b : V}
    (hwX : w ∈ X)
    (hreach : G.Reachable b w)
    (hbNotAncZ : b ∉ ancestorClosure G Z) :
    ActiveFromX G X Z b := by
  rcases reachable_to_backwardChain_avoidZ G Z hreach hbNotAncZ with
    ⟨q, hqne, hqHead, hqLast, hqBack, hqNotZ⟩
  have hAvoidQ : PathAvoidsInternals Z q :=
    pathAvoidsInternals_of_all_notInZ Z hqNotZ
  have hPE : PathEndpoints q = some (w, b) :=
    pathEndpoints_of_head_last (p := q) hqne hqHead hqLast
  refine ⟨w, hwX, ?_⟩
  exact ⟨q, hqne, hPE, backwardChain_activeTrail G Z hacyclic hqBack hAvoidQ hqne⟩

/-- State-form wrapper for X-side backward detour update at `b`. -/
private theorem activeFromXState_of_backward_detour_to_X_at_b
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w c b : V}
    (hwX : w ∈ X)
    (hbc : G.edges b c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX G X Z
    (activeFromX_of_backward_detour_to_X_at_b G X Z hacyclic hwX hbc hreach hcNotAncZ)

/-- State-form direct transition to `b` with explicit `b ∉ Z` passability. -/
private theorem activeFromXState_direct_transition_notInZ
    (G : DirectedGraph V) (X Z : Set V) {a b : V}
    (haX : a ∈ X) (hDirect : UndirectedEdge G a b) (hbNotZ : b ∉ Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX_notInZ G X Z
    (activeFromX_direct_transition G X Z haX hDirect) hbNotZ

/-- State-form direct transition to `b` with explicit `b ∈ Anc(Z)` passability. -/
private theorem activeFromXState_direct_transition_ancZ
    (G : DirectedGraph V) (X Z : Set V) {a b : V}
    (haX : a ∈ X) (hDirect : UndirectedEdge G a b) (hbAncZ : b ∈ ancestorClosure G Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX_ancZ G X Z
    (activeFromX_direct_transition G X Z haX hDirect) hbAncZ

/-- State-form activated-spouse transition to `b` with explicit `b ∉ Z` passability. -/
private theorem activeFromXState_spouse_activated_transition_notInZ
    (G : DirectedGraph V) (X Z : Set V)
    {a b c : V}
    (haX : a ∈ X) (hab : a ≠ b)
    (hac : G.edges a c) (hbc : G.edges b c)
    (hcAncZ : c ∈ ancestorClosure G Z)
    (hbNotZ : b ∉ Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX_notInZ G X Z
    (activeFromX_spouse_activated_transition G X Z haX hab hac hbc hcAncZ) hbNotZ

/-- State-form activated-spouse transition to `b` with explicit `b ∈ Anc(Z)` passability. -/
private theorem activeFromXState_spouse_activated_transition_ancZ
    (G : DirectedGraph V) (X Z : Set V)
    {a b c : V}
    (haX : a ∈ X) (hab : a ≠ b)
    (hac : G.edges a c) (hbc : G.edges b c)
    (hcAncZ : c ∈ ancestorClosure G Z)
    (hbAncZ : b ∈ ancestorClosure G Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX_ancZ G X Z
    (activeFromX_spouse_activated_transition G X Z haX hab hac hbc hcAncZ) hbAncZ

/-- State-form X-side backward detour update at `b` with explicit `b ∉ Z` passability. -/
private theorem activeFromXState_backward_detour_notInZ
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w c b : V}
    (hwX : w ∈ X)
    (hbc : G.edges b c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z)
    (hbNotZ : b ∉ Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX_notInZ G X Z
    (activeFromX_of_backward_detour_to_X_at_b G X Z hacyclic hwX hbc hreach hcNotAncZ) hbNotZ

/-- State-form X-side backward detour update at `b` with explicit `b ∈ Anc(Z)` passability. -/
private theorem activeFromXState_backward_detour_ancZ
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w c b : V}
    (hwX : w ∈ X)
    (hbc : G.edges b c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z)
    (hbAncZ : b ∈ ancestorClosure G Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX_ancZ G X Z
    (activeFromX_of_backward_detour_to_X_at_b G X Z hacyclic hwX hbc hreach hcNotAncZ) hbAncZ

/-- State-form direct backward-reach update at the current head with `b ∉ Z`. -/
private theorem activeFromXState_backward_reach_notInZ
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w b : V}
    (hwX : w ∈ X)
    (hreach : G.Reachable b w)
    (hbNotAncZ : b ∉ ancestorClosure G Z)
    (hbNotZ : b ∉ Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX_notInZ G X Z
    (activeFromX_of_backward_reach_to_X_at_head G X Z hacyclic hwX hreach hbNotAncZ) hbNotZ

/-- State-form direct backward-reach update at the current head with `b ∈ Anc(Z)`. -/
private theorem activeFromXState_backward_reach_ancZ
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w b : V}
    (hwX : w ∈ X)
    (hreach : G.Reachable b w)
    (hbNotAncZ : b ∉ ancestorClosure G Z)
    (hbAncZ : b ∈ ancestorClosure G Z) :
    ActiveFromXState G X Z b := by
  exact activeFromXState_of_activeFromX_ancZ G X Z
    (activeFromX_of_backward_reach_to_X_at_head G X Z hacyclic hwX hreach hbNotAncZ) hbAncZ

/-- Route-A core step (direct edge): advance state from head `a` to neighbor `b`
using local passability at `a` and a chosen passability certificate for `b`.

TODO: replace `sorry` with explicit endpoint-extension on `HasActiveTrail`:
append one edge and discharge the new middle-vertex activation from `hState.passable`. -/
private theorem activeFromXState_step_direct
    (G : DirectedGraph V) (X Z : Set V)
    {a b : V}
    (hState : ActiveFromXState G X Z a)
    (hDirect : UndirectedEdge G a b)
    (hPassB : HeadPassability G Z b) :
    ActiveFromXState G X Z b := by
  sorry

/-- Route-A core step (activated spouse): advance state from head `a` to `b`
through collider witness `c` when `c ∈ Anc(Z)`.

TODO: replace `sorry` by composing the existing state witness to `a` with the
active segment `a ~ c ~ b`, then package with `hPassB`. -/
private theorem activeFromXState_step_spouse_activated
    (G : DirectedGraph V) (X Z : Set V)
    {a b c : V}
    (hState : ActiveFromXState G X Z a)
    (hab : a ≠ b)
    (hac : G.edges a c) (hbc : G.edges b c)
    (hcAncZ : c ∈ ancestorClosure G Z)
    (hPassB : HeadPassability G Z b) :
    ActiveFromXState G X Z b := by
  sorry

/-- If there is a moral-ancestral trail from x∈X to y∈Y avoiding Z,
    then there is an active trail between some pair in X×Y.
    This is the key lemma for Phase 2 (hMoralToAT direction).

    **WARNING (for future LLMs):** This theorem is mid-refactor to Route A.
    The auxiliary recursion now threads `ActiveFromXState`, but the endpoint
    extension lemmas are still incomplete (`activeFromXState_step_direct`,
    `activeFromXState_step_spouse_activated`). Until those are proved, there
    remain both recursion-shape and branch-case `sorry` obligations. -/
theorem not_dsepFull_of_moralTrail
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) (hirr : ∀ v, ¬G.edges v v)
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y) (hxy : x ≠ y)
    {p : List V} (hpne : p ≠ [])
    (hEnds : PathEndpoints p = some (x, y))
    (hTrail : IsTrail (moralAncestralGraph G X Y Z) p)
    (hAvoid : PathAvoidsInternals Z p) :
    ¬DSeparatedFull G X Y Z := by
  -- Strong induction on trail length
  suffices aux : ∀ (n : ℕ) {x y : V} {p : List V},
      p.length ≤ n →
      y ∈ Y → x ≠ y →
      ActiveFromXState G X Z x →
      p ≠ [] →
      PathEndpoints p = some (x, y) →
      IsTrail (moralAncestralGraph G X Y Z) p →
      PathAvoidsInternals Z p →
      ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' from by
    rcases aux p.length (le_refl _) hy hxy
      (activeFromXState_of_memX G X Z hx) hpne hEnds hTrail hAvoid with
      ⟨x', hx', y', hy', hxy', hAT'⟩
    intro hDSep
    exact hDSep x' hx' y' hy' hxy' hAT'
  intro n
  induction n with
  | zero => intro hlen _ _ _ hpne; simp_all
  | succ n ih =>
    intro x y p hlen hy hxy hState hpne hEnds hTrail hAvoid
    -- Temporary bridge while migrating all branch closures to pure Route-A state.
    -- This will be removed once endpoint-extension lemmas eliminate all direct `x ∈ X` uses.
    have hx : x ∈ X := by
      sorry
    match p, hpne, hTrail with
    | [a], _, _ =>
      simp [PathEndpoints] at hEnds
      obtain ⟨rfl, rfl⟩ := hEnds
      exact absurd rfl hxy
    | [a, b], _, hT =>
      simp [PathEndpoints] at hEnds
      obtain ⟨rfl, rfl⟩ := hEnds
      have hEdge_ab : UndirectedEdge (moralAncestralGraph G X Y Z) a b := by
        cases hT with | cons hE _ => exact hE
      exact activeWitness_of_not_dsepFull G X Y Z
        (base_case_single_edge G X Y Z hacyclic hx hy hxy hEdge_ab)
    | a :: b :: c :: rest', _, hT =>
      -- Extract a = x from PathEndpoints
      have hEP := pathEndpoints_cons_cons_cons (hEnds := hEnds)
      have ha : a = x := hEP.1
      have hEnds' : PathEndpoints (x :: b :: c :: rest') = some (x, y) := by
        simpa [ha] using hEnds
      have hTrail' : IsTrail (moralAncestralGraph G X Y Z) (x :: b :: c :: rest') := by
        simpa [ha] using hT
      have hAvoid' : PathAvoidsInternals Z (x :: b :: c :: rest') := by
        simpa [ha] using hAvoid
      rcases tail_context_of_three_plus G X Y Z (hEnds := hEnds') (hTrail := hTrail')
          (hAvoid := hAvoid') with
        ⟨hEdge_xb, hTailTrail, hAvoidTail, hbNotZ, hEndsTail⟩
      -- Tail is shorter
      have hTailLen : (b :: c :: rest').length ≤ n := by
        simp [List.length] at hlen ⊢; omega
      -- Case split on b
      by_cases hbY : b ∈ Y
      · -- b ∈ Y: base case on first edge x—b
        have hxb_ne : x ≠ b := ne_of_moral_undirected_edge G X Y Z hEdge_xb
        exact activeWitness_of_not_dsepFull G X Y Z
          (base_case_single_edge G X Y Z hacyclic hx hbY hxb_ne hEdge_xb)
      · by_cases hbX : b ∈ X
        · -- b ∈ X: recurse on shorter tail trail
          have hby : b ≠ y := fun h => hbY (h ▸ hy)
          exact ih hTailLen hy hby
            (activeFromXState_of_memX G X Z hbX)
            (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
        · -- b ∉ X ∪ Y: use b's reachability
          -- Extract b ∈ relevantVertices from the moral edge
          have hbRel : b ∈ relevantVertices G X Y Z :=
            right_relevant_of_moral_edge G X Y Z hEdge_xb
          -- Main approach: check if b ∉ Anc(Z), then b reaches X∪Y
          by_cases hbAncZ : b ∈ ancestorClosure G Z
          · -- b ∈ Anc(Z) \ Z: complex case
              -- Decompose first edge to look for spouse reaching Y
              rcases moralAncestralEdge_decompose G X Y Z hEdge_xb with
                ⟨hDirect, _, _⟩ | ⟨c', hxc', hbc', hc'Rel, _, _⟩
              · have hStateB : ActiveFromXState G X Z b :=
                  activeFromXState_step_direct G X Z hState hDirect
                    (headPassability_of_ancZ G Z hbAncZ)
                -- Route-A target: recurse on tail from `b` using this state witness.
                -- This branch remains blocked only by the current IH shape (`b ∈ X` requirement).
                sorry -- Direct edge with b ∈ Anc(Z)
              · by_cases hc'AncZ : c' ∈ ancestorClosure G Z
                · have hxb_ne : x ≠ b :=
                    ne_of_moral_undirected_edge G X Y Z hEdge_xb
                  have hStateB : ActiveFromXState G X Z b :=
                    activeFromXState_step_spouse_activated
                      G X Z hState hxb_ne hxc' hbc' hc'AncZ
                      (headPassability_of_ancZ G Z hbAncZ)
                  -- Route-A target: recurse on tail from `b` with collider-activated spouse step.
                  sorry -- Both c' and b in Anc(Z)
                · -- c' ∉ Anc(Z): c' reaches X∪Y
                  rcases relevant_not_ancZ_reaches_XY G X Y Z hc'Rel hc'AncZ with
                    hc'XY | ⟨w, hwXY, hreach, _⟩
                  · rcases hc'XY with hc'X | hc'Y
                    · by_cases hc'Y' : c' ∈ Y
                      · -- Overlap case: c' ∈ X ∩ Y, use the direct edge [x, c'].
                        have hxc'_ne : x ≠ c' := fun h => by
                          subst h
                          exact G.isAcyclic_irrefl hacyclic x hxc'
                        exact ⟨x, hx, c', hc'Y', hxc'_ne,
                          ⟨[x, c'], by simp, by simp [PathEndpoints], ActiveTrail.two (Or.inl hxc')⟩⟩
                      · by_cases hxY' : x ∈ Y
                        · -- Use backward-detour witness with y = x and c = c'.
                          exact activeWitness_of_backward_detour_to_X
                              G X Y Z hacyclic hc'X hxY' hxc' (G.reachable_refl c') hc'AncZ
                        · have hStateB : ActiveFromXState G X Z b :=
                            activeFromXState_backward_detour_ancZ
                              G X Z hacyclic hc'X hbc' (G.reachable_refl c') hc'AncZ hbAncZ
                          -- Route-A target: continue on tail from `b`; this is now a pure IH-shape gap.
                          sorry -- c' ∈ X \ Y and x ∉ Y
                    · -- c' ∈ Y: trail [x, c']
                      have hxc'_ne : x ≠ c' := fun h => by
                        subst h
                        exact G.isAcyclic_irrefl hacyclic x hxc'
                      exact activeWitness_of_not_dsepFull G X Y Z (by
                        intro hDSep
                        exact absurd_dsep_of_activeTrail G X Y Z hx hc'Y hxc'_ne
                          (by simp) (by simp [PathEndpoints]) (ActiveTrail.two (Or.inl hxc'))
                          hDSep)
                  · rcases hwXY with hwX | hwY
                    · by_cases hwY' : w ∈ Y
                      · exact activeWitness_of_forward_detour_to_Y
                          G X Y Z hacyclic hx hwY' hxc' hreach hc'AncZ
                      · by_cases hxY' : x ∈ Y
                        · -- Use backward-detour witness with y = x.
                          exact activeWitness_of_backward_detour_to_X
                              G X Y Z hacyclic hwX hxY' hxc' hreach hc'AncZ
                        · have hStateB : ActiveFromXState G X Z b :=
                            activeFromXState_backward_detour_ancZ
                              G X Z hacyclic hwX hbc' hreach hc'AncZ hbAncZ
                          -- Route-A target: continue on tail from `b`; this is now a pure IH-shape gap.
                          sorry -- c' reaches w ∈ X \ Y and x ∉ Y
                    · exact activeWitness_of_forward_detour_to_Y
                        G X Y Z hacyclic hx hwY hxc' hreach hc'AncZ
          · -- b ∉ Anc(Z): b reaches w ∈ X∪Y
            rcases relevant_not_ancZ_reaches_XY G X Y Z hbRel hbAncZ with
              hbXY | ⟨w, hwXY, hreachBW, hbw⟩
            · -- b ∈ X∪Y: contradiction
              rcases hbXY with hbXX | hbYY
              · exact absurd hbXX hbX
              · exact absurd hbYY hbY
            · rcases hwXY with hwX | hwY
              · have hStateB : ActiveFromXState G X Z b :=
                  activeFromXState_backward_reach_notInZ
                    G X Z hacyclic hwX hreachBW hbAncZ hbNotZ
                -- Route-A target: recurse on tail from `b` with state produced from backward reachability.
                sorry -- b reaches w ∈ X only (hard case)
              · -- b reaches w ∈ Y
                -- Decompose first edge to prepend x.
                rcases moralAncestralEdge_decompose G X Y Z hEdge_xb with
                  ⟨hDirect, _, _⟩ | ⟨c', hxc', hbc', hc'Rel, _, _⟩
                · -- Direct edge x—b: build [x, b, ..., w∈Y]
                  rcases hDirect with hxb_edge | hbx_edge
                  · exact activeWitness_of_forward_detour_to_Y
                      G X Y Z hacyclic hx hwY hxb_edge hreachBW hbAncZ
                  ·
                    -- Remaining orientation: b → x. Use the directed chain from b to w.
                    rcases reachable_chain_avoidZ_of_not_ancZ G Z hreachBW hbAncZ with
                      ⟨q, hqne, hqHead, hqLast, hqChain, hbNotZ_chain⟩
                    match q, hqne, hqHead with
                    | b' :: qrest, _, hqH =>
                      have hbb' : b' = b := by simpa using hqH
                      have hFwd : IsDirectedChain G (b' :: qrest) := hqChain
                      -- x ≠ b from moral edge (moralUndirectedEdge has u ≠ v)
                      have hxb_ne : x ≠ b := by
                        exact ne_of_moral_undirected_edge G X Y Z hEdge_xb
                      have hxb'_ne : x ≠ b' := by rw [hbb']; exact hxb_ne
                      match qrest with
                      | [] =>
                        -- q = [b'], w = b'. Trail [x, b'] from x∈X to b'=w∈Y.
                        have hbw' : b' = w := by simp [List.getLast?] at hqLast; exact hqLast
                        rw [← hbw'] at hwY
                        exact activeWitness_of_not_dsepFull G X Y Z (by
                          intro hDSep
                          exact absurd_dsep_of_activeTrail G X Y Z hx hwY hxb'_ne
                            (by simp) (by simp [PathEndpoints])
                            (ActiveTrail.two (Or.inr (hbb' ▸ hbx_edge))) hDSep)
                      | d :: qrest' =>
                        -- Chain: b' → d → ... → w ∈ Y, with b' → x from hbx_edge.
                        have hbd : G.edges b' d := hFwd.1
                        have hAvoidQ : PathAvoidsInternals Z (b' :: d :: qrest') :=
                          pathAvoidsInternals_of_all_notInZ Z hbNotZ_chain
                        -- Case B: G.edges b x → b→x and b→d, both outgoing from b
                        by_cases hxd : x = d
                        · -- x = d: use sub-chain from x onwards (skip b)
                          subst hxd
                          -- Sub-chain: x :: qrest' (tail of b' :: x :: qrest')
                          have hSubChain : IsDirectedChain G (x :: qrest') := hFwd.2
                          have hSubNotZ : ∀ u ∈ x :: qrest', u ∉ Z := fun u hu =>
                            hbNotZ_chain u (List.mem_cons_of_mem b' hu)
                          match qrest' with
                          | [] =>
                            -- Chain [b', x], so w = x. Edge case: x = w ∈ Y, x ∈ X.
                            sorry -- x = d, qrest' = [], w = x edge case
                          | e :: rest =>
                            -- Sub-chain x → e → ... → w, build active trail
                            have hSC : IsDirectedChain G (x :: e :: rest) := hSubChain
                            have hSubAvoid : PathAvoidsInternals Z (x :: e :: rest) :=
                              pathAvoidsInternals_of_all_notInZ Z hSubNotZ
                            have hSubAT : ActiveTrail G Z (x :: e :: rest) :=
                              directedChain_activeTrail G Z hacyclic hSC hSubAvoid (by simp)
                            have hLast : (e :: rest).getLast? = some w := by
                              simp [List.getLast?] at hqLast ⊢; exact hqLast
                            have hw_mem : w ∈ e :: rest := by
                              have hmem : w ∈ (e :: rest).getLast? := hLast
                              rcases List.mem_getLast?_eq_getLast hmem with ⟨hne, heq⟩
                              exact heq ▸ List.getLast_mem _
                            have hxw_ne : x ≠ w := by
                              intro heq; subst heq
                              exact G.isAcyclic_iff_no_self_reach.mp hacyclic x e hSC.1
                                (directedChain_reachable_from_head G hSC.2 x hw_mem)
                            have hPE : PathEndpoints (x :: e :: rest) = some (x, w) := by
                              exact pathEndpoints_cons_eq_of_getLast hLast
                            exact activeWitness_of_not_dsepFull G X Y Z (by
                              intro hDSep
                              exact absurd_dsep_of_activeTrail G X Y Z hx hwY hxw_ne
                                (by simp) hPE hSubAT hDSep)
                        · -- x ≠ d: triple (x, b', d) with b→x, b→d (non-collider)
                          have hub : UndirectedEdge G x b' :=
                            Or.inr (by rw [hbb']; exact hbx_edge)
                          have hbcU : UndirectedEdge G b' d := Or.inl hbd
                          have hNonCol : IsNonCollider G ⟨x, b', d, hub, hbcU, hxd⟩ := by
                            unfold IsNonCollider IsCollider; intro ⟨_, hdb'⟩
                            exact G.isAcyclic_no_two_cycle hacyclic b' d hbd hdb'
                          have hAct : IsActive G Z ⟨x, b', d, hub, hbcU, hxd⟩ := by
                            unfold IsActive IsBlocked; push_neg
                            exact ⟨fun _ => hbb' ▸ hbNotZ, fun h => absurd h hNonCol⟩
                          have hTailAT : ActiveTrail G Z (b' :: d :: qrest') :=
                            directedChain_activeTrail G Z hacyclic hFwd hAvoidQ (by simp)
                          have hFullAT : ActiveTrail G Z (x :: b' :: d :: qrest') :=
                            ActiveTrail.cons hub hbcU hxd hAct hTailAT
                          by_cases hxw : x = w
                          · -- x = w ∈ Y: split on qrest' to normalize endpoint constraints.
                            cases qrest' with
                            | nil =>
                              have hwd : d = w := by
                                simp [List.getLast?] at hqLast
                                exact hqLast
                              exact False.elim (hxd (hxw.trans hwd.symm))
                            | cons e rest =>
                              sorry -- x = w with G.edges b x, x ≠ d, qrest' = e :: rest
                          · have hPE : PathEndpoints (x :: b' :: d :: qrest') = some (x, w) := by
                              exact pathEndpoints_cons_eq_of_getLast hqLast
                            exact activeWitness_of_not_dsepFull G X Y Z (by
                              intro hDSep
                              exact absurd_dsep_of_activeTrail G X Y Z hx hwY hxw
                                (by simp) hPE hFullAT hDSep)
                · -- Spouse edge: x→c' and b→c'. Try [x, c', b, ..., w∈Y]
                  sorry -- Spouse edge with b reaching Y (needs collider analysis at c')

/-- Route A interface: from one moral-ancestral trail witness, extract an explicit
active-trail witness in `X × Y`. This is the endpoint-flexible form used by the
refactor plan. -/
theorem activeWitness_of_moralTrail
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) (hirr : ∀ v, ¬G.edges v v)
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y) (hxy : x ≠ y)
    {p : List V} (hpne : p ≠ [])
    (hEnds : PathEndpoints p = some (x, y))
    (hTrail : IsTrail (moralAncestralGraph G X Y Z) p)
    (hAvoid : PathAvoidsInternals Z p) :
    ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
  exact activeWitness_of_not_dsepFull G X Y Z
    (not_dsepFull_of_moralTrail G X Y Z hacyclic hirr hx hy hxy hpne hEnds hTrail hAvoid)

/--
Phase 3: The main equivalence theorem.
D-separation in a DAG G is equivalent to separation in the moralized ancestral graph.
Proof via contrapositives of Phase 1 and Phase 2:
  (→) DSepFull → SepMoral: contrapositive of Phase 2 (moral trail → ¬DSepFull)
  (←) SepMoral → DSepFull: contrapositive of Phase 1 (active trail → moral trail)
-/
theorem dsepFull_iff_separatedInMoralAncestral
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) (hirr : ∀ v, ¬G.edges v v) :
    DSeparatedFull G X Y Z ↔ SeparatedInMoralAncestral G X Y Z := by
  constructor
  · -- (→) DSepFull → SepMoral
    -- Contrapositive: ¬SepMoral → ¬DSepFull
    intro hDSep x hx y hy hxy ⟨p, hpne, hEnds, hTrail, hAvoid⟩
    rcases activeWitness_of_moralTrail G X Y Z hacyclic hirr hx hy hxy hpne hEnds hTrail hAvoid with
      ⟨x', hx', y', hy', hxy', hAT'⟩
    exact hDSep x' hx' y' hy' hxy' hAT'
  · -- (←) SepMoral → DSepFull
    -- Contrapositive of Phase 1: active trail → moral trail → ¬SepMoral
    intro hSep x hx y hy hxy ⟨p, hpne, hEnds, hAT⟩
    rcases activeTrail_to_moralAncestralTrail G X Y Z hacyclic hirr hx hy hpne hEnds hAT with
      ⟨p', hp'ne, hEnds', hTrail', hAvoid'⟩
    exact hSep x hx y hy hxy ⟨p', hp'ne, hEnds', hTrail', hAvoid'⟩

end Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
