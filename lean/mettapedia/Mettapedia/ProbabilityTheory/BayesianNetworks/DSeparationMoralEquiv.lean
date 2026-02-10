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

/-- If there is a moral-ancestral trail from x∈X to y∈Y avoiding Z,
    then there is an active trail between some pair in X×Y.
    This is the key lemma for Phase 2 (hMoralToAT direction).

    **WARNING (for future LLMs):** The remaining sorry cases in this theorem are
    STRUCTURALLY WRONG — they are NOT simply "hard to prove." The induction
    hypothesis requires the trail's first element to be in X, but in the edge cases
    the internal vertex b ∉ X, so the IH cannot be applied. The correct fix requires
    EITHER restructuring the induction (e.g., proving endpoint-preserving
    moral→active conversion without X/Y requirements) OR implementing the
    activated-moral-graph approach from the plan (define `activatedMoralEdge` that
    only includes spouse edges where the witness c ∈ Anc(Z), prove separation
    equivalence, then expand activated edges to active trail segments). -/
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
      x ∈ X → y ∈ Y → x ≠ y →
      p ≠ [] →
      PathEndpoints p = some (x, y) →
      IsTrail (moralAncestralGraph G X Y Z) p →
      PathAvoidsInternals Z p →
      ¬DSeparatedFull G X Y Z from
    aux p.length (le_refl _) hx hy hxy hpne hEnds hTrail hAvoid
  intro n
  induction n with
  | zero => intro hlen _ _ _ hpne; simp_all
  | succ n ih =>
    intro x y p hlen hx hy hxy hpne hEnds hTrail hAvoid
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
      exact base_case_single_edge G X Y Z hacyclic hx hy hxy hEdge_ab
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
        exact base_case_single_edge G X Y Z hacyclic hx hbY hxb_ne hEdge_xb
      · by_cases hbX : b ∈ X
        · -- b ∈ X: recurse on shorter tail trail
          have hby : b ≠ y := fun h => hbY (h ▸ hy)
          exact ih hTailLen hbX hy hby
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
              ⟨_, _, _⟩ | ⟨c', hxc', hbc', hc'Rel, _, _⟩
            · sorry -- Direct edge with b ∈ Anc(Z)
            · by_cases hc'AncZ : c' ∈ ancestorClosure G Z
              · sorry -- Both c' and b in Anc(Z)
              · -- c' ∉ Anc(Z): c' reaches X∪Y
                rcases relevant_not_ancZ_reaches_XY G X Y Z hc'Rel hc'AncZ with
                  hc'XY | ⟨w, hwXY, hreach, _⟩
                · rcases hc'XY with hc'X | hc'Y
                  · sorry -- c' ∈ X
                  · -- c' ∈ Y: trail [x, c']
                    have hxc'_ne : x ≠ c' := fun h => by
                      subst h; exact G.isAcyclic_irrefl hacyclic x hxc'
                    intro hDSep
                    exact absurd_dsep_of_activeTrail G X Y Z hx hc'Y hxc'_ne
                      (by simp) (by simp [PathEndpoints]) (ActiveTrail.two (Or.inl hxc'))
                      hDSep
                · rcases hwXY with hwX | hwY
                  · sorry -- c' reaches w ∈ X
                  · exact absurd_dsep_of_forward_detour_to_Y
                      G X Y Z hacyclic hx hwY hxc' hreach hc'AncZ
          · -- b ∉ Anc(Z): b reaches w ∈ X∪Y
            rcases relevant_not_ancZ_reaches_XY G X Y Z hbRel hbAncZ with
              hbXY | ⟨w, hwXY, hreachBW, hbw⟩
            · -- b ∈ X∪Y: contradiction
              rcases hbXY with hbXX | hbYY
              · exact absurd hbXX hbX
              · exact absurd hbYY hbY
            · rcases hwXY with hwX | hwY
              · sorry -- b reaches w ∈ X only (hard case)
              · -- b reaches w ∈ Y
                -- Decompose first edge to prepend x.
                rcases moralAncestralEdge_decompose G X Y Z hEdge_xb with
                  ⟨hDirect, _, _⟩ | ⟨c', hxc', hbc', hc'Rel, _, _⟩
                · -- Direct edge x—b: build [x, b, ..., w∈Y]
                  rcases hDirect with hxb_edge | hbx_edge
                  · exact absurd_dsep_of_forward_detour_to_Y
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
                        intro hDSep
                        exact absurd_dsep_of_activeTrail G X Y Z hx hwY hxb'_ne
                          (by simp) (by simp [PathEndpoints])
                          (ActiveTrail.two (Or.inr (hbb' ▸ hbx_edge))) hDSep
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
                            intro hDSep
                            exact absurd_dsep_of_activeTrail G X Y Z hx hwY hxw_ne
                              (by simp) hPE hSubAT hDSep
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
                          · -- x = w ∈ Y: edge case
                            sorry -- x = w with G.edges b x, x ≠ d
                          · have hPE : PathEndpoints (x :: b' :: d :: qrest') = some (x, w) := by
                              exact pathEndpoints_cons_eq_of_getLast hqLast
                            intro hDSep
                            exact absurd_dsep_of_activeTrail G X Y Z hx hwY hxw
                              (by simp) hPE hFullAT hDSep
                · -- Spouse edge: x→c' and b→c'. Try [x, c', b, ..., w∈Y]
                  sorry -- Spouse edge with b reaching Y (needs collider analysis at c')

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
    exact not_dsepFull_of_moralTrail G X Y Z hacyclic hirr hx hy hxy hpne hEnds hTrail hAvoid hDSep
  · -- (←) SepMoral → DSepFull
    -- Contrapositive of Phase 1: active trail → moral trail → ¬SepMoral
    intro hSep x hx y hy hxy ⟨p, hpne, hEnds, hAT⟩
    rcases activeTrail_to_moralAncestralTrail G X Y Z hacyclic hirr hx hy hpne hEnds hAT with
      ⟨p', hp'ne, hEnds', hTrail', hAvoid'⟩
    exact hSep x hx y hy hxy ⟨p', hp'ne, hEnds', hTrail', hAvoid'⟩

end Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
