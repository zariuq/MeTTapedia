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
  · simp [PathEndpoints, hLast]

/-- The right endpoint of a moral-ancestral edge lies in relevant vertices. -/
private theorem right_relevant_of_moral_edge
    (G : DirectedGraph V) (X Y Z : Set V) {x b : V}
    (hEdge : UndirectedEdge (moralAncestralGraph G X Y Z) x b) :
    b ∈ relevantVertices G X Y Z := by
  rcases moralAncestralEdge_decompose G X Y Z hEdge with
    ⟨_, _, hbR⟩ | ⟨_, _, _, _, _, hbR⟩
  · exact hbR
  · exact hbR

/-- The left endpoint of a moral-ancestral edge lies in relevant vertices. -/
private theorem left_relevant_of_moral_edge
    (G : DirectedGraph V) (X Y Z : Set V) {x b : V}
    (hEdge : UndirectedEdge (moralAncestralGraph G X Y Z) x b) :
    x ∈ relevantVertices G X Y Z := by
  have hEdge' : UndirectedEdge (moralAncestralGraph G X Y Z) b x :=
    (undirectedEdge_symm (moralAncestralGraph G X Y Z) x b).1 hEdge
  exact right_relevant_of_moral_edge G X Y Z hEdge'

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

/-- In a nontrivial moral-ancestral trail starting at `x`, the head is relevant. -/
private theorem head_relevant_of_moral_trail_cons
    (G : DirectedGraph V) (X Y Z : Set V)
    {x b : V} {rest : List V}
    (hTrail : IsTrail (moralAncestralGraph G X Y Z) (x :: b :: rest)) :
    x ∈ relevantVertices G X Y Z := by
  have hEdge_xb : UndirectedEdge (moralAncestralGraph G X Y Z) x b := by
    cases hTrail with
    | cons hE _ => exact hE
  exact left_relevant_of_moral_edge G X Y Z hEdge_xb

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

private def ActiveFromXNeY (G : DirectedGraph V) (X Z : Set V) (y a : V) : Prop :=
  ∃ x ∈ X, x ≠ y ∧ HasActiveTrail G Z x a

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

/-- Extract concrete `(prev,next)` orientation data from the available local
head passability certificate. This is used to thread explicit join-shape data
through endpoint-extension lemmas. -/
private theorem joinDirs_of_headPassability
    (G : DirectedGraph V) (Z : Set V) (a : V)
    (hPass : HeadPassability G Z a) :
    ∃ prev next : JoinEdgeDir, JoinConditionAtHead G Z a prev next := by
  cases hPass with
  | noncollider hNotZ =>
    refine ⟨JoinEdgeDir.outgoing, JoinEdgeDir.outgoing, ?_⟩
    exact joinConditionAtHead_noncollider G Z a hNotZ (by simp)
  | collider hAncZ =>
    refine ⟨JoinEdgeDir.incoming, JoinEdgeDir.incoming, ?_⟩
    exact joinConditionAtHead_in_in G Z a hAncZ

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

/-- Extract the X-anchor witness carried by `ActiveFromXState`. -/
private theorem activeFromXState_anchor
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (hState : ActiveFromXState G X Z a) :
    ∃ x0 ∈ X, HasActiveTrail G Z x0 a :=
  hState.active

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

private theorem activeFromXNeY_of_memX
    (G : DirectedGraph V) (X Z : Set V) {y a : V}
    (haX : a ∈ X) (haNe : a ≠ y) :
    ActiveFromXNeY G X Z y a := by
  refine ⟨a, haX, haNe, ?_⟩
  exact ⟨[a], by simp, by simp [PathEndpoints], ActiveTrail.single a⟩

/-! ## Active trail tail extension (snoc) -/

private theorem hasActiveTrail_snoc_shape_of_ne
    (G : DirectedGraph V) (Z : Set V)
    {x0 a : V}
    (hAT : HasActiveTrail G Z x0 a)
    (hx0a : x0 ≠ a) :
    ∃ p u,
      PathEndpoints (p ++ [u, a]) = some (x0, a) ∧
      ActiveTrail G Z (p ++ [u, a]) := by
  rcases hAT with ⟨q, hqne, hqEnds, hqAct⟩
  have hqLast : q.getLast? = some a := getLast_of_pathEndpoints hqEnds
  let q1 := q.dropLast
  have hq1ne : q1 ≠ [] := by
    intro hnil
    cases q with
    | nil =>
        cases hqne rfl
    | cons v rest =>
        cases rest with
        | nil =>
            simp [PathEndpoints] at hqEnds
            obtain ⟨rfl, rfl⟩ := hqEnds
            exact (hx0a rfl).elim
        | cons w rest' =>
            simp [q1] at hnil
  let u := q1.getLast hq1ne
  let p := q1.dropLast
  have hq1eq : q1 = p ++ [u] := by
    simpa [q1, p, u] using (List.dropLast_append_getLast (l := q1) hq1ne).symm
  have hqeq' : q = q1 ++ [a] := by
    have hqLastEq : q.getLast hqne = a := by
      have : some (q.getLast hqne) = some a := by
        calc
          some (q.getLast hqne) = q.getLast? := by
            simpa using (List.getLast?_eq_getLast_of_ne_nil (l := q) hqne).symm
          _ = some a := hqLast
      exact Option.some.inj this
    calc
      q = q1 ++ [q.getLast hqne] := by
        simpa [q1] using (List.dropLast_append_getLast (l := q) hqne).symm
      _ = q1 ++ [a] := by simp [hqLastEq]
  have hqeq : q = p ++ [u, a] := by
    calc
      q = q1 ++ [a] := hqeq'
      _ = (p ++ [u]) ++ [a] := by simp [hq1eq]
      _ = p ++ [u, a] := by simp [List.append_assoc]
  refine ⟨p, u, ?_, ?_⟩
  · simpa [hqeq] using hqEnds
  · simpa [hqeq] using hqAct

private theorem activeTrail_last_edge
    (G : DirectedGraph V) (Z : Set V) :
    ∀ {p : List V} {b c : V},
      ActiveTrail G Z (p ++ [b, c]) →
      UndirectedEdge G b c := by
  intro p
  induction p with
  | nil =>
      intro b c hAT
      -- Only the `two` constructor fits `[b, c]`.
      cases hAT with
      | two hbc => exact hbc
  | cons a p ih =>
      intro b c hAT
      cases p with
      | nil =>
          -- p = [a], so list is [a, b, c]
          cases hAT with
          | cons _ hbc _ _ _ => exact hbc
      | cons a' rest =>
          -- p = a :: a' :: rest, tail list is a' :: rest ++ [b, c]
          cases rest with
          | nil =>
              -- list is [a, a', b, c]
              cases hAT with
              | cons _ _ _ _ hTail =>
                  -- Tail list is [a', b, c]
                  exact ih hTail

          | cons r rs =>
              -- list is a :: a' :: r :: rs ++ [b, c]
              cases hAT with
              | cons _ _ _ _ hTail =>
                  -- Recurse on the tail using the IH (where p = a' :: r :: rs).
                  exact ih hTail

/-- Extract either direct head membership in `X`, or an explicit snoc-form anchor
trail ending in a predecessor/head pair `u, a`. This is the concrete join-shape
needed to reason about extension at the head. -/
private theorem activeFromXState_anchor_or_snoc
    (G : DirectedGraph V) (X Z : Set V) {a : V}
    (hState : ActiveFromXState G X Z a) :
    (a ∈ X) ∨
    ∃ x0 ∈ X, x0 ≠ a ∧
      ∃ p u,
        PathEndpoints (p ++ [u, a]) = some (x0, a) ∧
        ActiveTrail G Z (p ++ [u, a]) := by
  rcases activeFromXState_anchor G X Z hState with ⟨x0, hx0, hAT0⟩
  by_cases hx0a : x0 = a
  · left
    simpa [hx0a] using hx0
  · right
    rcases hasActiveTrail_snoc_shape_of_ne G Z hAT0 hx0a with
      ⟨p, u, hEnds, hAT⟩
    exact ⟨x0, hx0, hx0a, p, u, hEnds, hAT⟩

private theorem activeTrail_snoc
    (G : DirectedGraph V) (Z : Set V) :
    ∀ {p : List V} {b c d : V},
      (hAT : ActiveTrail G Z (p ++ [b, c])) →
      (hcd : UndirectedEdge G c d) →
      (hbd : b ≠ d) →
      IsActive G Z
        ⟨b, c, d,
          (activeTrail_last_edge G Z (p := p) (b := b) (c := c) hAT),
          hcd, hbd⟩ →
      ActiveTrail G Z (p ++ [b, c, d]) := by
  intro p
  induction p with
  | nil =>
      intro b c d hAT hcd hbd hAct
      -- hAT : ActiveTrail G Z [b, c]
      have hbc : UndirectedEdge G b c := by
        cases hAT with
        | two hbc => exact hbc
      exact ActiveTrail.cons hbc hcd hbd hAct (ActiveTrail.two hcd)
  | cons a p ih =>
      intro b c d hAT hcd hbd hAct
      cases p with
      | nil =>
          -- p = [a], list is [a, b, c]
          cases hAT with
          | cons hab hbc hac hAct0 hTail =>
              -- hTail : ActiveTrail G Z [b, c]
              have hAct' :
                  IsActive G Z
                    ⟨b, c, d,
                      (activeTrail_last_edge G Z (p := []) (b := b) (c := c) hTail),
                      hcd, hbd⟩ := by
                simpa using hAct
              have hTail' : ActiveTrail G Z ([b, c] ++ [d]) :=
                ih hTail hcd hbd hAct'
              simpa [List.append_assoc] using
                (ActiveTrail.cons hab hbc hac hAct0 hTail')
      | cons a' rest =>
          -- p = a :: a' :: rest
          cases rest with
          | nil =>
              -- list is [a, a', b, c]
              cases hAT with
              | cons hab hbc hac hAct0 hTail =>
                  have hAct' :
                      IsActive G Z
                        ⟨b, c, d,
                          (activeTrail_last_edge G Z (p := [a']) (b := b) (c := c) hTail),
                          hcd, hbd⟩ := by
                    simpa using hAct
                  have hTail' : ActiveTrail G Z (([a'] ++ [b, c]) ++ [d]) :=
                    ih hTail hcd hbd hAct'
                  simpa [List.cons_append, List.append_assoc] using
                    (ActiveTrail.cons hab hbc hac hAct0 hTail')

          | cons r rs =>
              -- list is a :: a' :: r :: rs ++ [b, c]
              cases hAT with
              | cons hab hbc hac hAct0 hTail =>
                  have hAct' :
                      IsActive G Z
                        ⟨b, c, d,
                          (activeTrail_last_edge G Z (p := a' :: r :: rs) (b := b) (c := c) hTail),
                          hcd, hbd⟩ := by
                    simpa using hAct
                  have hTail' : ActiveTrail G Z ((a' :: r :: rs) ++ [b, c, d]) :=
                    ih hTail hcd hbd hAct'
                  simpa [List.cons_append, List.append_assoc] using
                    (ActiveTrail.cons hab hbc hac hAct0 hTail')

/-- Lift one explicit snoc extension into `HasActiveTrail` form. -/
private theorem hasActiveTrail_extend_from_snoc
    (G : DirectedGraph V) (Z : Set V)
    {xA u a : V} {pref : List V}
    (hEnds : PathEndpoints (pref ++ [u, a]) = some (xA, a))
    (hAT : ActiveTrail G Z (pref ++ [u, a]))
    {b : V}
    (hab : UndirectedEdge G a b)
    (hub : u ≠ b)
    (hAct : IsActive G Z
      ⟨u, a, b,
        (activeTrail_last_edge G Z (p := pref) (b := u) (c := a) hAT),
        hab, hub⟩) :
    HasActiveTrail G Z xA b := by
  refine ⟨pref ++ [u, a, b], by simp, ?_, ?_⟩
  · have hHead0 : (pref ++ [u, a]).head? = some xA :=
      head_of_pathEndpoints (p := pref ++ [u, a]) hEnds
    have hHead : (pref ++ [u, a, b]).head? = some xA := by
      simpa using hHead0
    have hLast : (pref ++ [u, a, b]).getLast? = some b := by
      simp
    exact pathEndpoints_of_head_last (by simp) hHead hLast
  · exact activeTrail_snoc G Z hAT hab hub hAct

/-- Dropping the final endpoint from `pref ++ [u, a]` preserves `ActiveTrail`. -/
private theorem activeTrail_dropLast_pair
    (G : DirectedGraph V) (Z : Set V) :
    ∀ (pref : List V) (u a : V),
      ActiveTrail G Z (pref ++ [u, a]) →
      ActiveTrail G Z (pref ++ [u]) := by
  intro pref
  induction pref with
  | nil =>
      intro u a hAT
      have hAT' : ActiveTrail G Z [u, a] := by simpa using hAT
      cases hAT' with
      | two _ =>
          simpa using (ActiveTrail.single (G := G) (Z := Z) u)
  | cons v pref ih =>
      intro u a hAT
      cases pref with
      | nil =>
          have hAT' : ActiveTrail G Z [v, u, a] := by simpa using hAT
          cases hAT' with
          | cons hvu _ _ _ _ =>
              exact ActiveTrail.two hvu
      | cons w rest =>
          cases rest with
          | nil =>
              have hAT' : ActiveTrail G Z [v, w, u, a] := by
                simpa [List.cons_append, List.append_assoc] using hAT
              cases hAT' with
              | cons hvw hwu hvu hAct hTail =>
                  have hTail' : ActiveTrail G Z ([w] ++ [u]) := by
                    exact ih u a (by simpa [List.cons_append, List.append_assoc] using hTail)
                  simpa [List.cons_append, List.append_assoc] using
                    (ActiveTrail.cons hvw hwu hvu hAct hTail')
          | cons r rs =>
              have hAT' : ActiveTrail G Z (v :: w :: r :: (rs ++ [u, a])) := by
                simpa [List.cons_append, List.append_assoc] using hAT
              cases hAT' with
              | cons hvw hwr hvr hAct hTail =>
                  have hTail' : ActiveTrail G Z ((w :: r :: rs) ++ [u]) := by
                    exact ih u a (by simpa [List.cons_append, List.append_assoc] using hTail)
                  simpa [List.cons_append, List.append_assoc] using
                    (ActiveTrail.cons hvw hwr hvr hAct hTail')

/-- Recover a predecessor-endpoint active witness from a snoc-form trail. -/
private theorem hasActiveTrail_prefix_from_snoc
    (G : DirectedGraph V) (Z : Set V)
    {xA u a : V} {pref : List V}
    (hEnds : PathEndpoints (pref ++ [u, a]) = some (xA, a))
    (hAT : ActiveTrail G Z (pref ++ [u, a])) :
    HasActiveTrail G Z xA u := by
  refine ⟨pref ++ [u], by simp, ?_, activeTrail_dropLast_pair G Z pref u a hAT⟩
  have hHead0 : (pref ++ [u, a]).head? = some xA :=
    head_of_pathEndpoints (p := pref ++ [u, a]) hEnds
  have hHead : (pref ++ [u]).head? = some xA := by
    simpa [List.append_assoc] using hHead0
  have hLast : (pref ++ [u]).getLast? = some u := by
    simp
  exact pathEndpoints_of_head_last (by simp) hHead hLast

private theorem isActive_of_nonCollider_notInZ
    (G : DirectedGraph V) (Z : Set V) (t : PathTriple G)
    (hNonCol : IsNonCollider G t) (hNotZ : t.b ∉ Z) :
    IsActive G Z t := by
  unfold IsActive IsBlocked
  intro hBlocked
  rcases hBlocked with ⟨hnc, hbZ⟩ | ⟨hcol, _, _⟩
  · exact hNotZ hbZ
  · exact hNonCol hcol

private theorem activeTrail_snoc_noncollider
    (G : DirectedGraph V) (Z : Set V) :
    ∀ {p : List V} {b c d : V},
      ActiveTrail G Z (p ++ [b, c]) →
      (hbc : UndirectedEdge G b c) →
      (hcd : UndirectedEdge G c d) →
      (hbd : b ≠ d) →
      (hNonCol : IsNonCollider G ⟨b, c, d, hbc, hcd, hbd⟩) →
      (hcNotZ : c ∉ Z) →
      ActiveTrail G Z (p ++ [b, c, d]) := by
  intro p b c d hAT hbc hcd hbd hNonCol hcNotZ
  have hAct : IsActive G Z ⟨b, c, d, hbc, hcd, hbd⟩ :=
    isActive_of_nonCollider_notInZ G Z _ hNonCol hcNotZ
  exact activeTrail_snoc G Z hAT hcd hbd hAct

private theorem activeTrail_snoc_collider
    (G : DirectedGraph V) (Z : Set V) :
    ∀ {p : List V} {b c d : V},
      ActiveTrail G Z (p ++ [b, c]) →
      (hbc : UndirectedEdge G b c) →
      (hcd : UndirectedEdge G c d) →
      (hbd : b ≠ d) →
      (hCol : IsCollider G ⟨b, c, d, hbc, hcd, hbd⟩) →
      (hcAncZ : c ∈ ancestorClosure G Z) →
      ActiveTrail G Z (p ++ [b, c, d]) := by
  intro p b c d hAT hbc hcd hbd hCol hcAncZ
  have hAct : IsActive G Z ⟨b, c, d, hbc, hcd, hbd⟩ :=
    isActive_of_collider_and_activated G Z _ hCol hcAncZ
  exact activeTrail_snoc G Z hAT hcd hbd hAct

/-- Extract the active proof at the final internal triple of a snoc-shaped trail. -/
private theorem activeTrail_last_triple_data
    (G : DirectedGraph V) (Z : Set V) :
    ∀ {p : List V} {b c d : V},
      ActiveTrail G Z (p ++ [b, c, d]) →
      ∃ hbc : UndirectedEdge G b c, ∃ hcd : UndirectedEdge G c d, ∃ hbd : b ≠ d,
        IsActive G Z ⟨b, c, d, hbc, hcd, hbd⟩ := by
  intro p
  induction p with
  | nil =>
      intro b c d hAT
      have hAT' : ActiveTrail G Z [b, c, d] := by simpa using hAT
      cases hAT' with
      | cons hbc hcd hbd hAct _ =>
          exact ⟨hbc, hcd, hbd, hAct⟩
  | cons a p ih =>
      intro b c d hAT
      cases p with
      | nil =>
          have hAT' : ActiveTrail G Z [a, b, c, d] := by
            simpa [List.append_assoc] using hAT
          cases hAT' with
          | cons _ _ _ _ hTail =>
              have hTail' : ActiveTrail G Z [b, c, d] := by simpa using hTail
              cases hTail' with
              | cons hbc hcd hbd hAct _ =>
                  exact ⟨hbc, hcd, hbd, hAct⟩
      | cons phead prest =>
          cases prest with
          | nil =>
              have hAT' : ActiveTrail G Z [a, phead, b, c, d] := by
                simpa [List.append_assoc] using hAT
              cases hAT' with
              | cons _ _ _ _ hTail =>
                  have hTail' : ActiveTrail G Z [phead, b, c, d] := by
                    simpa [List.append_assoc] using hTail
                  cases hTail' with
                  | cons _ _ _ _ hTail2 =>
                      have hTail3 : ActiveTrail G Z [b, c, d] := by
                        simpa [List.append_assoc] using hTail2
                      cases hTail3 with
                      | cons hbc hcd hbd hAct _ =>
                          exact ⟨hbc, hcd, hbd, hAct⟩
          | cons p2 prest2 =>
              have hAT' : ActiveTrail G Z (a :: phead :: p2 :: prest2 ++ [b, c, d]) := by
                simpa [List.cons_append, List.append_assoc] using hAT
              cases hAT' with
              | cons _ _ _ _ hTail =>
                  have hTail' : ActiveTrail G Z ((phead :: p2 :: prest2) ++ [b, c, d]) := by
                    simpa [List.cons_append, List.append_assoc] using hTail
                  exact ih hTail'

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

private theorem activeFromXNeY_direct_transition
    (G : DirectedGraph V) (X Z : Set V) {y a b : V}
    (haX : a ∈ X) (haNe : a ≠ y) (hDirect : UndirectedEdge G a b) :
    ActiveFromXNeY G X Z y b := by
  refine ⟨a, haX, haNe, ?_⟩
  exact ⟨[a, b], by simp, by simp [PathEndpoints], ActiveTrail.two hDirect⟩

/-- Extend an anchored `ActiveFromXNeY` witness across an outgoing edge `x → b`.
This is the join-safe composition case used by fallback routing: either the anchor
already reaches `b` at the predecessor boundary (`u = b`), or we append one step
at `x` with an explicitly non-collider join (forced by DAG acyclicity). -/
private theorem activeFromXNeY_of_anchor_step_outgoing
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {y x b : V}
    (hAX : ActiveFromXNeY G X Z y x)
    (hxb : G.edges x b)
    (hxNotZ : x ∉ Z) :
    ActiveFromXNeY G X Z y b := by
  rcases hAX with ⟨x0, hx0, hx0NeY, hAT0⟩
  by_cases hx0x : x0 = x
  · subst hx0x
    refine ⟨x0, hx0, hx0NeY, ?_⟩
    exact ⟨[x0, b], by simp, by simp [PathEndpoints], ActiveTrail.two (Or.inl hxb)⟩
  · rcases hasActiveTrail_snoc_shape_of_ne G Z hAT0 hx0x with
      ⟨pref, u, hEnds0, hTrail0⟩
    by_cases hub : u = b
    · subst hub
      refine ⟨x0, hx0, hx0NeY, ?_⟩
      simpa using hasActiveTrail_prefix_from_snoc
        (G := G) (Z := Z)
        (xA := x0) (u := u) (a := x) (pref := pref)
        hEnds0 hTrail0
    · have hux : UndirectedEdge G u x :=
        activeTrail_last_edge G Z (p := pref) (b := u) (c := x) hTrail0
      have huxb_ne : u ≠ b := hub
      let t : PathTriple G := ⟨u, x, b, hux, Or.inl hxb, huxb_ne⟩
      have hNonCol : IsNonCollider G t := by
        intro hCol
        have hbx : G.edges b x := hCol.2
        exact G.isAcyclic_iff_no_self_reach.mp hacyclic x b hxb (G.edge_reachable hbx)
      have hAct : IsActive G Z t :=
        isActive_of_nonCollider_notInZ G Z t hNonCol hxNotZ
      refine ⟨x0, hx0, hx0NeY, ?_⟩
      exact hasActiveTrail_extend_from_snoc G Z hEnds0 hTrail0 (Or.inl hxb) huxb_ne (by
        simpa [t] using hAct)

/-- Extend an anchored `ActiveFromXNeY` witness across an incoming edge `b → x`
when the join at `x` is collider-enabled (`x ∈ Anc(Z)`). -/
private theorem activeFromXNeY_of_anchor_step_incoming_ancZ
    (G : DirectedGraph V) (X Z : Set V)
    {y x b : V}
    (hAX : ActiveFromXNeY G X Z y x)
    (hbx : G.edges b x)
    (hxNotZ : x ∉ Z)
    (hxAncZ : x ∈ ancestorClosure G Z) :
    ActiveFromXNeY G X Z y b := by
  rcases hAX with ⟨x0, hx0, hx0NeY, hAT0⟩
  by_cases hx0x : x0 = x
  · subst hx0x
    refine ⟨x0, hx0, hx0NeY, ?_⟩
    exact ⟨[x0, b], by simp, by simp [PathEndpoints], ActiveTrail.two (Or.inr hbx)⟩
  · rcases hasActiveTrail_snoc_shape_of_ne G Z hAT0 hx0x with
      ⟨pref, u, hEnds0, hTrail0⟩
    by_cases hub : u = b
    · subst hub
      refine ⟨x0, hx0, hx0NeY, ?_⟩
      simpa using hasActiveTrail_prefix_from_snoc
        (G := G) (Z := Z)
        (xA := x0) (u := u) (a := x) (pref := pref)
        hEnds0 hTrail0
    · have hux : UndirectedEdge G u x :=
        activeTrail_last_edge G Z (p := pref) (b := u) (c := x) hTrail0
      have huxb_ne : u ≠ b := hub
      let t : PathTriple G := ⟨u, x, b, hux, Or.inr hbx, huxb_ne⟩
      have hAct : IsActive G Z t :=
        isActive_of_join_obligations G Z t.edge_ab t.edge_bc t.a_ne_c
          (fun _ => hxNotZ) (fun _ => hxAncZ)
      refine ⟨x0, hx0, hx0NeY, ?_⟩
      exact hasActiveTrail_extend_from_snoc G Z hEnds0 hTrail0 (Or.inr hbx) huxb_ne (by
        simpa [t] using hAct)

/-- Extend an anchored `ActiveFromXNeY` witness from head `x` to neighbor `b`
through an activated spouse witness `c` (`x → c ← b`). This handles both the
generic no-backtrack case and the crux `u = c` case by extracting the last
internal triple at `c` when needed. -/
private theorem activeFromXNeY_of_anchor_step_spouse_activated
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {y x b c : V}
    (hAX : ActiveFromXNeY G X Z y x)
    (hxc : G.edges x c) (hbc : G.edges b c)
    (hxb : x ≠ b)
    (hxNotZ : x ∉ Z)
    (hcAncZ : c ∈ ancestorClosure G Z) :
    ActiveFromXNeY G X Z y b := by
  rcases hAX with ⟨x0, hx0, hx0NeY, hAT0⟩
  by_cases hx0x : x0 = x
  · subst hx0x
    let hub : UndirectedEdge G x0 c := Or.inl hxc
    let hcv : UndirectedEdge G c b := Or.inr hbc
    have hCol : IsCollider G ⟨x0, c, b, hub, hcv, hxb⟩ := ⟨hxc, hbc⟩
    have hAct : IsActive G Z ⟨x0, c, b, hub, hcv, hxb⟩ :=
      isActive_of_collider_and_activated G Z ⟨x0, c, b, hub, hcv, hxb⟩ hCol hcAncZ
    refine ⟨x0, hx0, hx0NeY, ?_⟩
    refine ⟨[x0, c, b], by simp, by simp [PathEndpoints], ?_⟩
    exact ActiveTrail.cons hub hcv hxb hAct (ActiveTrail.two hcv)
  · rcases hasActiveTrail_snoc_shape_of_ne G Z hAT0 hx0x with
      ⟨pref, u, hEnds0, hTrail0⟩
    by_cases huc : u = c
    · by_cases hpref : pref = []
      · have hx0c : x0 = c := by
          have hSome : some (c, x) = some (x0, x) := by
            simpa [huc, hpref, PathEndpoints] using hEnds0
          have hPair : (c, x) = (x0, x) := Option.some.inj hSome
          exact (Prod.mk.inj hPair).1.symm
        refine ⟨x0, hx0, hx0NeY, ?_⟩
        refine ⟨[x0, b], by simp, by simp [PathEndpoints], ?_⟩
        exact ActiveTrail.two (by simpa [hx0c] using (Or.inr hbc : UndirectedEdge G c b))
      · let v : V := pref.getLast hpref
        let p2 : List V := pref.dropLast
        have hpref_eq : pref = p2 ++ [v] := by
          simpa [p2, v] using (List.dropLast_append_getLast (l := pref) hpref).symm
        have hTrailVcx0 : ActiveTrail G Z ((p2 ++ [v]) ++ [c, x]) := by
          rw [huc] at hTrail0
          rw [hpref_eq] at hTrail0
          simpa [List.append_assoc] using hTrail0
        have hTrailVcx : ActiveTrail G Z (p2 ++ [v, c, x]) := by
          simpa [List.append_assoc] using hTrailVcx0
        have hEndsVcx0 : PathEndpoints ((p2 ++ [v]) ++ [c, x]) = some (x0, x) := by
          rw [huc] at hEnds0
          rw [hpref_eq] at hEnds0
          simpa [List.append_assoc] using hEnds0
        have hEndsVcx : PathEndpoints (p2 ++ [v, c, x]) = some (x0, x) := by
          simpa [List.append_assoc] using hEndsVcx0
        have hTrailVc0 : ActiveTrail G Z ((p2 ++ [v]) ++ [c]) :=
          activeTrail_dropLast_pair G Z (p2 ++ [v]) c x hTrailVcx0
        have hTrailVc : ActiveTrail G Z (p2 ++ [v, c]) := by
          simpa [List.append_assoc] using hTrailVc0
        have hEndsVc : PathEndpoints (p2 ++ [v, c]) = some (x0, c) := by
          have hHeadVcx : (p2 ++ [v, c, x]).head? = some x0 :=
            head_of_pathEndpoints (p := p2 ++ [v, c, x]) hEndsVcx
          have hHeadVc : (p2 ++ [v, c]).head? = some x0 := by
            simpa [List.append_assoc] using hHeadVcx
          have hLastVc : (p2 ++ [v, c]).getLast? = some c := by
            simp
          exact pathEndpoints_of_head_last
            (by simp) hHeadVc hLastVc
        by_cases hvb : v = b
        · have hATv : HasActiveTrail G Z x0 v :=
            hasActiveTrail_prefix_from_snoc
                  (G := G) (Z := Z)
                  (xA := x0) (u := v) (a := c) (pref := p2)
                  hEndsVc hTrailVc
          refine ⟨x0, hx0, hx0NeY, ?_⟩
          simpa [hvb] using hATv
        · have hvc : UndirectedEdge G v c :=
            activeTrail_last_edge G Z (p := p2) (b := v) (c := c) hTrailVc
          rcases activeTrail_last_triple_data G Z (p := p2) (b := v) (c := c) (d := x) hTrailVcx with
            ⟨hvcOld, hcxOld, hvxOld, hActOld⟩
          let tNew : PathTriple G := ⟨v, c, b, hvc, (Or.inr hbc), hvb⟩
          have hActNew : IsActive G Z tNew := by
            refine isActive_of_join_obligations G Z tNew.edge_ab tNew.edge_bc tNew.a_ne_c ?_ ?_
            · intro hNonColNew
              have hcv : G.edges c v := by
                cases hvc with
                | inl hvc_in =>
                    exact (hNonColNew ⟨hvc_in, hbc⟩).elim
                | inr hcv_out => exact hcv_out
              have hNot_vc : ¬ G.edges v c := by
                intro hvc_in
                exact G.isAcyclic_no_two_cycle hacyclic c v hcv hvc_in
              have hNonColOld : IsNonCollider G ⟨v, c, x, hvcOld, hcxOld, hvxOld⟩ := by
                intro hColOld
                exact hNot_vc hColOld.1
              exact active_nonCollider_not_in_Z G Z ⟨v, c, x, hvcOld, hcxOld, hvxOld⟩ hActOld hNonColOld
            · intro _
              exact hcAncZ
          have hATb : HasActiveTrail G Z x0 b :=
            hasActiveTrail_extend_from_snoc
                  (G := G) (Z := Z)
                  (xA := x0) (u := v) (a := c) (pref := p2)
                  hEndsVc hTrailVc
                  (Or.inr hbc) hvb (by simpa [tNew] using hActNew)
          exact ⟨x0, hx0, hx0NeY, hATb⟩
    · have hux : UndirectedEdge G u x :=
        activeTrail_last_edge G Z (p := pref) (b := u) (c := x) hTrail0
      let tX : PathTriple G := ⟨u, x, c, hux, (Or.inl hxc), huc⟩
      have hNonColX : IsNonCollider G tX := by
        intro hCol
        have hcx : G.edges c x := hCol.2
        exact G.isAcyclic_no_two_cycle hacyclic x c hxc hcx
      have hActX : IsActive G Z tX :=
        isActive_of_nonCollider_notInZ G Z tX hNonColX hxNotZ
      have hTrailXc : ActiveTrail G Z (pref ++ [u, x, c]) :=
        activeTrail_snoc G Z hTrail0 (Or.inl hxc) huc (by simpa [tX] using hActX)
      have hEndsXc : PathEndpoints (pref ++ [u, x, c]) = some (x0, c) := by
        have hHead0 : (pref ++ [u, x]).head? = some x0 :=
          head_of_pathEndpoints (p := pref ++ [u, x]) hEnds0
        have hHead1 : (pref ++ [u, x, c]).head? = some x0 := by
          simpa using hHead0
        have hLast1 : (pref ++ [u, x, c]).getLast? = some c := by
          simp
        exact pathEndpoints_of_head_last (by simp) hHead1 hLast1
      let tC : PathTriple G := ⟨x, c, b, (Or.inl hxc), (Or.inr hbc), hxb⟩
      have hColC : IsCollider G tC := ⟨hxc, hbc⟩
      have hActC : IsActive G Z tC :=
        isActive_of_collider_and_activated G Z tC hColC hcAncZ
      have hEndsXc' : PathEndpoints ((pref ++ [u]) ++ [x, c]) = some (x0, c) := by
        simpa [List.append_assoc] using hEndsXc
      have hTrailXc' : ActiveTrail G Z ((pref ++ [u]) ++ [x, c]) := by
        simpa [List.append_assoc] using hTrailXc
      have hATb : HasActiveTrail G Z x0 b :=
        hasActiveTrail_extend_from_snoc
          (G := G) (Z := Z)
          (xA := x0) (u := x) (a := c) (pref := pref ++ [u])
          hEndsXc' hTrailXc'
          (Or.inr hbc) hxb (by simpa [tC] using hActC)
      exact ⟨x0, hx0, hx0NeY, hATb⟩

private theorem activeFromX_of_activeFromXNeY
    (G : DirectedGraph V) (X Z : Set V) {y a : V}
    (hAX : ActiveFromXNeY G X Z y a) :
    ActiveFromX G X Z a := by
  rcases hAX with ⟨x0, hx0, _, hAT0⟩
  exact ⟨x0, hx0, hAT0⟩

/-- Propagate an anchored `ActiveFromXNeY` witness along a directed chain whose
vertices are all outside `Z`. -/
private theorem activeFromXNeY_of_directedChain_head
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic) {y : V} :
    ∀ {a : V} {q : List V},
      (hqne : q ≠ []) →
      q.head? = some a →
      IsDirectedChain G q →
      (∀ u ∈ q, u ∉ Z) →
      ActiveFromXNeY G X Z y a →
      ActiveFromXNeY G X Z y (q.getLast hqne) := by
  intro a q hqne hHead hChain hNotZ hAXa
  induction q generalizing a with
  | nil =>
      exact (hqne rfl).elim
  | cons v qs ih =>
      cases qs with
      | nil =>
          have hva : v = a := by simpa using hHead
          subst hva
          simpa using hAXa
      | cons w rest =>
          have hva : v = a := by simpa using hHead
          subst hva
          have havw : G.edges v w := hChain.1
          have haNotZ : v ∉ Z := hNotZ v (by simp)
          have hAXw : ActiveFromXNeY G X Z y w :=
            activeFromXNeY_of_anchor_step_outgoing G X Z hacyclic hAXa havw haNotZ
          have hNotZtail : ∀ u ∈ (w :: rest), u ∉ Z := by
            intro u hu
            exact hNotZ u (by simp [hu])
          have hTail :
              ActiveFromXNeY G X Z y ((w :: rest).getLast (by simp : (w :: rest) ≠ [])) :=
            ih (a := w) (by simp) (by simp) hChain.2 hNotZtail hAXw
          simpa using hTail

/-- From an anchored `X`-to-head witness and a forward detour `x → c`, `c ↠ w ∈ Y`
with `c ∉ Anc(Z)`, produce an explicit `X × Y` active witness (assuming `w ∉ X`
to discharge endpoint distinctness at `w`). -/
private theorem activeWitness_of_anchor_forward_detour_to_Y
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {x y c w : V}
    (hAX : ActiveFromXNeY G X Z y x)
    (hxc : G.edges x c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z)
    (hxNotZ : x ∉ Z)
    (hwY : w ∈ Y)
    (hwNotX : w ∉ X) :
    ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
  rcases reachable_to_directedChain G hreach with
    ⟨q, hqne, hqHead, hqLast, hqChain⟩
  cases q with
  | nil =>
      exact (hqne rfl).elim
  | cons c' qrest =>
      have hqH : (c' :: qrest).head? = some c := hqHead
      have hcc' : c' = c := by simpa using hqH
      have hChainX : IsDirectedChain G (x :: c' :: qrest) := ⟨hcc' ▸ hxc, hqChain⟩
      have hNotZq : ∀ u ∈ (c' :: qrest), u ∉ Z := by
        intro u hu
        exact not_in_Z_of_reachable_of_not_in_ancZ G Z hcNotAncZ
          (hcc' ▸ directedChain_reachable_from_head G hqChain u hu)
      have hNotZxq : ∀ u ∈ (x :: c' :: qrest), u ∉ Z := by
        intro u hu
        rcases List.mem_cons.1 hu with rfl | hu'
        · exact hxNotZ
        · exact hNotZq u hu'
      have hAXw :
          ActiveFromXNeY G X Z y ((x :: c' :: qrest).getLast (by simp : (x :: c' :: qrest) ≠ [])) :=
        activeFromXNeY_of_directedChain_head
          G X Z hacyclic (a := x) (q := x :: c' :: qrest)
          (by simp) (by simp) hChainX hNotZxq hAX
      have hLastX : (x :: c' :: qrest).getLast? = some w := by
        simpa [List.getLast?] using hqLast
      have hLastXEq :
          (x :: c' :: qrest).getLast (by simp : (x :: c' :: qrest) ≠ []) = w := by
        exact Option.some.inj hLastX
      rcases hAXw with ⟨x0, hx0, _, hATw⟩
      have hx0w : x0 ≠ w := by
        intro hEq
        apply hwNotX
        simpa [hEq] using hx0
      exact ⟨x0, hx0, w, hwY, hx0w, by simpa [hLastXEq] using hATw⟩

/-- Forward-detour witness when the detour endpoint is exactly the tracked `y`.
Unlike the generic rank helper, this does not require `y ∉ X` because
`ActiveFromXNeY ... y ...` already carries endpoint distinctness. -/
private theorem activeWitness_of_anchor_forward_detour_to_exactY
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {x y c : V}
    (hAX : ActiveFromXNeY G X Z y x)
    (hxc : G.edges x c)
    (hreach : G.Reachable c y)
    (hcNotAncZ : c ∉ ancestorClosure G Z)
    (hxNotZ : x ∉ Z)
    (hy : y ∈ Y) :
    ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
  rcases reachable_to_directedChain G hreach with
    ⟨q, hqne, hqHead, hqLast, hqChain⟩
  cases q with
  | nil =>
      exact (hqne rfl).elim
  | cons c' qrest =>
      have hqH : (c' :: qrest).head? = some c := hqHead
      have hcc' : c' = c := by simpa using hqH
      have hChainX : IsDirectedChain G (x :: c' :: qrest) := ⟨hcc' ▸ hxc, hqChain⟩
      have hNotZq : ∀ u ∈ (c' :: qrest), u ∉ Z := by
        intro u hu
        exact not_in_Z_of_reachable_of_not_in_ancZ G Z hcNotAncZ
          (hcc' ▸ directedChain_reachable_from_head G hqChain u hu)
      have hNotZxq : ∀ u ∈ (x :: c' :: qrest), u ∉ Z := by
        intro u hu
        rcases List.mem_cons.1 hu with rfl | hu'
        · exact hxNotZ
        · exact hNotZq u hu'
      have hAXyTmp :
          ActiveFromXNeY G X Z y ((x :: c' :: qrest).getLast (by simp : (x :: c' :: qrest) ≠ [])) :=
        activeFromXNeY_of_directedChain_head
          G X Z hacyclic (a := x) (q := x :: c' :: qrest)
          (by simp) (by simp) hChainX hNotZxq hAX
      have hLastEq :
          (x :: c' :: qrest).getLast (by simp : (x :: c' :: qrest) ≠ []) = y := by
        have hLastSome : (x :: c' :: qrest).getLast? = some y := by
          simpa [List.getLast?] using hqLast
        exact Option.some.inj hLastSome
      have hAXy : ActiveFromXNeY G X Z y y := by
        simpa [hLastEq] using hAXyTmp
      rcases hAXy with ⟨x0, hx0, hx0NeY, hATy⟩
      exact ⟨x0, hx0, y, hy, hx0NeY, hATy⟩

/-- From an anchored `X`-to-head witness and a reachability chain from the head
`x ↠ w ∈ Y` with `x ∉ Anc(Z)`, produce an explicit `X × Y` active witness
(assuming `w ∉ X` for endpoint distinctness). -/
private theorem activeWitness_of_anchor_reach_to_Y_from_notAnc_head
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {x y w : V}
    (hAX : ActiveFromXNeY G X Z y x)
    (hreach : G.Reachable x w)
    (hxNotAncZ : x ∉ ancestorClosure G Z)
    (hwY : w ∈ Y)
    (hwNotX : w ∉ X) :
    ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
  rcases reachable_to_directedChain G hreach with
    ⟨q, hqne, hqHead, hqLast, hqChain⟩
  cases q with
  | nil =>
      exact (hqne rfl).elim
  | cons x' qrest =>
      have hxx' : x' = x := by simpa using hqHead
      have hNotZq : ∀ u ∈ (x' :: qrest), u ∉ Z := by
        intro u hu
        exact not_in_Z_of_reachable_of_not_in_ancZ G Z hxNotAncZ
          (hxx' ▸ directedChain_reachable_from_head G hqChain u hu)
      have hAXw :
          ActiveFromXNeY G X Z y ((x' :: qrest).getLast (by simp : (x' :: qrest) ≠ [])) :=
        activeFromXNeY_of_directedChain_head
          G X Z hacyclic (a := x) (q := x' :: qrest)
          (by simp) (by simp [hxx']) hqChain hNotZq hAX
      have hLastEq : (x' :: qrest).getLast (by simp : (x' :: qrest) ≠ []) = w := by
        have hLastSome : (x' :: qrest).getLast? = some w := by simpa using hqLast
        exact Option.some.inj hLastSome
      rcases hAXw with ⟨x0, hx0, _, hATw⟩
      have hx0w : x0 ≠ w := by
        intro hEq
        apply hwNotX
        simpa [hEq] using hx0
      exact ⟨x0, hx0, w, hwY, hx0w, by simpa [hLastEq] using hATw⟩

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

private theorem activeFromXNeY_spouse_activated_transition
    (G : DirectedGraph V) (X Z : Set V)
    {y a b c : V}
    (haX : a ∈ X) (haNe : a ≠ y) (hab : a ≠ b)
    (hac : G.edges a c) (hbc : G.edges b c)
    (hcAncZ : c ∈ ancestorClosure G Z) :
    ActiveFromXNeY G X Z y b := by
  let hub : UndirectedEdge G a c := Or.inl hac
  let hcv : UndirectedEdge G c b := Or.inr hbc
  have hCol : IsCollider G ⟨a, c, b, hub, hcv, hab⟩ := ⟨hac, hbc⟩
  have hAct : IsActive G Z ⟨a, c, b, hub, hcv, hab⟩ :=
    isActive_of_collider_and_activated G Z ⟨a, c, b, hub, hcv, hab⟩ hCol hcAncZ
  refine ⟨a, haX, haNe, ?_⟩
  refine ⟨[a, c, b], by simp, by simp [PathEndpoints], ?_⟩
  exact ActiveTrail.cons hub hcv hab hAct (ActiveTrail.two hcv)

/-- X-side detour update:
if `b → c`, `c ↠ w`, `w ∈ X`, and `c ∉ Anc(Z)`, then `b` gains an `ActiveFromX`
state via the backward chain `w ↝ c` followed by the edge `b → c`. -/
private theorem activeTrail_of_backward_detour_to_X_at_b
    (G : DirectedGraph V) (Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w c b : V}
    (hbc : G.edges b c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z) :
    HasActiveTrail G Z w b := by
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
  exact ⟨q ++ [b], by simp, hPE,
    backwardChain_activeTrail G Z hacyclic hBack hAvoidQb (by simp)⟩

private theorem activeFromX_of_backward_detour_to_X_at_b
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w c b : V}
    (hwX : w ∈ X)
    (hbc : G.edges b c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z) :
    ActiveFromX G X Z b := by
  refine ⟨w, hwX, ?_⟩
  exact activeTrail_of_backward_detour_to_X_at_b
    G Z hacyclic hbc hreach hcNotAncZ

private theorem activeFromXNeY_of_backward_detour_to_X_at_b
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {y w c b : V}
    (hwX : w ∈ X) (hwNe : w ≠ y)
    (hbc : G.edges b c)
    (hreach : G.Reachable c w)
    (hcNotAncZ : c ∉ ancestorClosure G Z) :
    ActiveFromXNeY G X Z y b := by
  refine ⟨w, hwX, hwNe, ?_⟩
  exact activeTrail_of_backward_detour_to_X_at_b
    G Z hacyclic hbc hreach hcNotAncZ

/-- Direct backward-reach update at the current head:
if `b ↠ w`, `w ∈ X`, and `b ∉ Anc(Z)`, then `b` has an `ActiveFromX` witness
by reversing the directed chain from `b` to `w`. -/
private theorem activeTrail_of_backward_reach_to_X_at_head
    (G : DirectedGraph V) (Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w b : V}
    (hreach : G.Reachable b w)
    (hbNotAncZ : b ∉ ancestorClosure G Z) :
    HasActiveTrail G Z w b := by
  rcases reachable_to_backwardChain_avoidZ G Z hreach hbNotAncZ with
    ⟨q, hqne, hqHead, hqLast, hqBack, hqNotZ⟩
  have hAvoidQ : PathAvoidsInternals Z q :=
    pathAvoidsInternals_of_all_notInZ Z hqNotZ
  have hPE : PathEndpoints q = some (w, b) :=
    pathEndpoints_of_head_last (p := q) hqne hqHead hqLast
  exact ⟨q, hqne, hPE, backwardChain_activeTrail G Z hacyclic hqBack hAvoidQ hqne⟩

private theorem activeFromX_of_backward_reach_to_X_at_head
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {w b : V}
    (hwX : w ∈ X)
    (hreach : G.Reachable b w)
    (hbNotAncZ : b ∉ ancestorClosure G Z) :
    ActiveFromX G X Z b := by
  refine ⟨w, hwX, ?_⟩
  exact activeTrail_of_backward_reach_to_X_at_head
    G Z hacyclic hreach hbNotAncZ

private theorem activeFromXNeY_of_backward_reach_to_X_at_head
    (G : DirectedGraph V) (X Z : Set V)
    (hacyclic : G.IsAcyclic)
    {y w b : V}
    (hwX : w ∈ X) (hwNe : w ≠ y)
    (hreach : G.Reachable b w)
    (hbNotAncZ : b ∉ ancestorClosure G Z) :
    ActiveFromXNeY G X Z y b := by
  refine ⟨w, hwX, hwNe, ?_⟩
  exact activeTrail_of_backward_reach_to_X_at_head
    G Z hacyclic hreach hbNotAncZ

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

/-- Route-A core step (direct edge) from an `a ∈ X` head to neighbor `b`,
carrying an explicit passability certificate for the new head `b`. -/
private theorem activeFromXState_step_direct
    (G : DirectedGraph V) (X Z : Set V)
    {a b : V}
    (hState : ActiveFromXState G X Z a)
    (haX : a ∈ X)
    (hDirect : UndirectedEdge G a b)
    (hPassB : HeadPassability G Z b) :
    ActiveFromXState G X Z b := by
  have _ := hState
  exact ⟨activeFromX_direct_transition G X Z haX hDirect, hPassB⟩

/-- Route-A core step (activated spouse) from an `a ∈ X` head to `b` through
collider witness `c` under `c ∈ Anc(Z)`, carrying passability for `b`. -/
private theorem activeFromXState_step_spouse_activated
    (G : DirectedGraph V) (X Z : Set V)
    {a b c : V}
    (hState : ActiveFromXState G X Z a)
    (haX : a ∈ X)
    (hab : a ≠ b)
    (hac : G.edges a c) (hbc : G.edges b c)
    (hcAncZ : c ∈ ancestorClosure G Z)
    (hPassB : HeadPassability G Z b) :
    ActiveFromXState G X Z b := by
  have _ := hState
  exact ⟨activeFromX_spouse_activated_transition G X Z haX hab hac hbc hcAncZ, hPassB⟩

/-- Final Route-A fallback target:
head is not in `X` or `Y`, but we carry an `ActiveFromXState` anchor and a
moral-ancestral tail to `y ∈ Y`. Prove an explicit `X × Y` active witness.

This isolates the last structural composition obligation from the main induction
statement so the remaining closure work can focus on one theorem boundary. -/
private theorem activeWitness_of_state_fallback
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic)
    {x y : V}
    (hy : y ∈ Y) (hxy : x ≠ y)
    (hState : ActiveFromXState G X Z x)
    (hAX : ActiveFromXNeY G X Z y x)
    (hxNotX : x ∉ X) (hxNotY : x ∉ Y) (hxNotZ : x ∉ Z)
    {p : List V} (hpne : p ≠ [])
    (hEnds : PathEndpoints p = some (x, y))
    (hTrail : IsTrail (moralAncestralGraph G X Y Z) p)
    (hAvoid : PathAvoidsInternals Z p)
    (hStep :
      ∀ {x' y' : V} {p' : List V},
        p'.length < p.length →
        y' ∈ Y → x' ≠ y' →
        ActiveFromXState G X Z x' →
        ActiveFromXNeY G X Z y' x' →
        (x' ∈ X ∨ x' ∉ Z) →
        p' ≠ [] →
        PathEndpoints p' = some (x', y') →
        IsTrail (moralAncestralGraph G X Y Z) p' →
        PathAvoidsInternals Z p' →
        ∃ x'' ∈ X, ∃ y'' ∈ Y, x'' ≠ y'' ∧ HasActiveTrail G Z x'' y'') :
    ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
  have _ := hacyclic
  have _ := hState
  have _ := hxNotX
  have _ := hxNotY
  have _ := hxNotZ
  have _ := hAvoid
  match p, hpne, hTrail with
  | [a], _, _ =>
    simp [PathEndpoints] at hEnds
    obtain ⟨rfl, rfl⟩ := hEnds
    exact (hxy rfl).elim
  | [a, b], _, hT =>
    have hPair :
        (a, b) = (x, y) := Option.some.inj (by simpa [PathEndpoints] using hEnds)
    have habxy : a = x ∧ b = y := by
      exact Prod.mk.inj hPair
    have ha : a = x := habxy.1
    have hb : b = y := habxy.2
    have hEdge_ab : UndirectedEdge (moralAncestralGraph G X Y Z) a b := by
      cases hT with
      | cons hE _ => exact hE
    have hEdge_xy : UndirectedEdge (moralAncestralGraph G X Y Z) x y := by
      simpa [ha, hb] using hEdge_ab
    rcases moralAncestralEdge_decompose G X Y Z hEdge_xy with
      ⟨hDirect, _, _⟩ | ⟨c', hxc', hyc', hc'Rel, _, _⟩
    · rcases hDirect with hxyD | hyxD
      · rcases activeFromXNeY_of_anchor_step_outgoing G X Z hacyclic hAX hxyD hxNotZ with
          ⟨x0, hx0, hx0NeY, hAT0⟩
        exact ⟨x0, hx0, y, hy, hx0NeY, hAT0⟩
      · by_cases hxAncZ : x ∈ ancestorClosure G Z
        · rcases activeFromXNeY_of_anchor_step_incoming_ancZ G X Z hAX hyxD hxNotZ hxAncZ with
            ⟨x0, hx0, hx0NeY, hAT0⟩
          exact ⟨x0, hx0, y, hy, hx0NeY, hAT0⟩
        · rcases hAX with ⟨x0, hx0, hx0NeY, hAT0⟩
          have hx0x_ne : x0 ≠ x := by
            intro hEq
            apply hxNotX
            simpa [hEq] using hx0
          rcases hasActiveTrail_snoc_shape_of_ne G Z hAT0 hx0x_ne with
            ⟨pref, u, hEnds0, hTrail0⟩
          by_cases huy : u = y
          · have hATu : HasActiveTrail G Z x0 u :=
              hasActiveTrail_prefix_from_snoc
                (G := G) (Z := Z)
                (xA := x0) (u := u) (a := x) (pref := pref)
                hEnds0 hTrail0
            have hATy : HasActiveTrail G Z x0 y := by
              simpa [huy] using hATu
            exact ⟨x0, hx0, y, hy, hx0NeY, hATy⟩
          · have hux : UndirectedEdge G u x :=
              activeTrail_last_edge G Z (p := pref) (b := u) (c := x) hTrail0
            cases hux with
            | inl hux_in =>
                have _ := hux_in
                have hxRel : x ∈ relevantVertices G X Y Z :=
                  left_relevant_of_moral_edge G X Y Z hEdge_xy
                rcases relevant_not_ancZ_reaches_XY G X Y Z hxRel hxAncZ with
                  hxXY | ⟨w, hwXY, hreachXW, _⟩
                · rcases hxXY with hxX | hxY
                  · exact (hxNotX hxX).elim
                  · exact (hxNotY hxY).elim
                · rcases hwXY with hwX | hwY
                  · exact activeWitness_of_backward_detour_to_X
                      G X Y Z hacyclic hwX hy hyxD hreachXW hxAncZ
                  · by_cases hwX' : w ∈ X
                    · exact activeWitness_of_backward_detour_to_X
                        G X Y Z hacyclic hwX' hy hyxD hreachXW hxAncZ
                    · have hAX0 : ActiveFromXNeY G X Z y x := ⟨x0, hx0, hx0NeY, hAT0⟩
                      exact activeWitness_of_anchor_reach_to_Y_from_notAnc_head
                        G X Y Z hacyclic hAX0 hreachXW hxAncZ hwY hwX'
            | inr hxu =>
                let t : PathTriple G := ⟨u, x, y, (Or.inr hxu), (Or.inr hyxD), huy⟩
                have hNonCol : IsNonCollider G t := by
                  intro hCol
                  have hux' : G.edges u x := hCol.1
                  exact G.isAcyclic_iff_no_self_reach.mp hacyclic x u hxu (G.edge_reachable hux')
                have hAct : IsActive G Z t :=
                  isActive_of_nonCollider_notInZ G Z t hNonCol hxNotZ
                have hATy : HasActiveTrail G Z x0 y :=
                  hasActiveTrail_extend_from_snoc
                    (G := G) (Z := Z)
                    (xA := x0) (u := u) (a := x) (pref := pref)
                    hEnds0 hTrail0 (Or.inr hyxD) huy (by simpa [t] using hAct)
                exact ⟨x0, hx0, y, hy, hx0NeY, hATy⟩
    · by_cases hc'Y : c' ∈ Y
      · have hAXc' : ActiveFromXNeY G X Z y c' :=
          activeFromXNeY_of_anchor_step_outgoing G X Z hacyclic hAX hxc' hxNotZ
        rcases hAXc' with ⟨x1, hx1, hx1NeY, hAT1⟩
        by_cases hx1c' : x1 = c'
        · have hc'neY : c' ≠ y := by
            intro hEq
            have hyy : G.edges y y := by
              simpa [hEq] using hyc'
            exact G.isAcyclic_irrefl hacyclic y hyy
          have hATcy : HasActiveTrail G Z c' y := by
            refine ⟨[c', y], by simp, by simp [PathEndpoints], ?_⟩
            exact ActiveTrail.two (Or.inr hyc')
          exact ⟨c', by simpa [hx1c'] using hx1, y, hy, hc'neY, hATcy⟩
        · exact ⟨x1, hx1, c', hc'Y, hx1c', hAT1⟩
      · by_cases hc'X : c' ∈ X
        · have hc'neY : c' ≠ y := by
            intro hEq
            apply hc'Y
            simpa [hEq] using hy
          have hATcy : HasActiveTrail G Z c' y := by
            refine ⟨[c', y], by simp, by simp [PathEndpoints], ?_⟩
            exact ActiveTrail.two (Or.inr hyc')
          exact ⟨c', hc'X, y, hy, hc'neY, hATcy⟩
        · by_cases hc'AncZ : c' ∈ ancestorClosure G Z
          · have hAXy : ActiveFromXNeY G X Z y y :=
              activeFromXNeY_of_anchor_step_spouse_activated
                G X Z hacyclic hAX hxc' hyc' hxy hxNotZ hc'AncZ
            rcases hAXy with ⟨x1, hx1, hx1NeY, hAT1⟩
            exact ⟨x1, hx1, y, hy, hx1NeY, hAT1⟩
          · rcases relevant_not_ancZ_reaches_XY G X Y Z hc'Rel hc'AncZ with
              hc'XY | ⟨w, hwXY, hreach, _⟩
            · rcases hc'XY with hc''X | hc''Y
              · exact (hc'X hc''X).elim
              · exact (hc'Y hc''Y).elim
            · rcases hwXY with hwX | hwY
              · exact activeWitness_of_backward_detour_to_X
                  G X Y Z hacyclic hwX hy hyc' hreach hc'AncZ
              · by_cases hwX' : w ∈ X
                · exact activeWitness_of_backward_detour_to_X
                    G X Y Z hacyclic hwX' hy hyc' hreach hc'AncZ
                · exact activeWitness_of_anchor_forward_detour_to_Y
                    G X Y Z hacyclic hAX hxc' hreach hc'AncZ hxNotZ hwY hwX'
  | a :: b :: c :: rest', _, hT =>
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
    by_cases hbyEq : b = y
    · have hlen2 : ([x, b] : List V).length < (a :: b :: c :: rest').length := by simp
      have hbY : b ∈ Y := by simpa [hbyEq] using hy
      have hxyb : x ≠ b := by simpa [hbyEq] using hxy
      have hAXb : ActiveFromXNeY G X Z b x := by simpa [hbyEq] using hAX
      have hTrail2 : IsTrail (moralAncestralGraph G X Y Z) [x, b] :=
        IsTrail.cons hEdge_xb (IsTrail.single (G := moralAncestralGraph G X Y Z) _)
      exact hStep (p' := [x, b])
        hlen2
        hbY hxyb hState hAXb (Or.inr hxNotZ)
        (by simp) (by simp [PathEndpoints]) hTrail2 (by simp [PathAvoidsInternals])
    · have hby : b ≠ y := hbyEq
      have hTailLen : (b :: c :: rest').length < (a :: b :: c :: rest').length := by simp
      rcases moralAncestralEdge_decompose G X Y Z hEdge_xb with
        ⟨hDirect, _, _⟩ | ⟨c', hxc', hbc', hc'Rel, _, _⟩
      · rcases hDirect with hxb | hbx
        · have hAXb : ActiveFromXNeY G X Z y b :=
            activeFromXNeY_of_anchor_step_outgoing G X Z hacyclic hAX hxb hxNotZ
          have hStateB : ActiveFromXState G X Z b :=
            activeFromXState_of_activeFromX_notInZ G X Z
              (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
          exact hStep (p' := b :: c :: rest')
            hTailLen
            hy hby hStateB hAXb
            (Or.inr hbNotZ)
            (List.cons_ne_nil _ _)
            hEndsTail hTailTrail hAvoidTail
        · by_cases hxAncZ : x ∈ ancestorClosure G Z
          · have hAXb : ActiveFromXNeY G X Z y b :=
              activeFromXNeY_of_anchor_step_incoming_ancZ G X Z hAX hbx hxNotZ hxAncZ
            have hStateB : ActiveFromXState G X Z b :=
              activeFromXState_of_activeFromX_notInZ G X Z
                (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
            exact hStep (p' := b :: c :: rest')
              hTailLen
              hy hby hStateB hAXb
              (Or.inr hbNotZ)
              (List.cons_ne_nil _ _)
              hEndsTail hTailTrail hAvoidTail
          · rcases hAX with ⟨x0, hx0, hx0NeY, hAT0⟩
            have hx0x_ne : x0 ≠ x := by
              intro hEq
              apply hxNotX
              simpa [hEq] using hx0
            rcases hasActiveTrail_snoc_shape_of_ne G Z hAT0 hx0x_ne with
              ⟨pref, u, hEnds0, hTrail0⟩
            by_cases hub : u = b
            · have hATu : HasActiveTrail G Z x0 u :=
                hasActiveTrail_prefix_from_snoc
                  (G := G) (Z := Z)
                  (xA := x0) (u := u) (a := x) (pref := pref)
                  hEnds0 hTrail0
              have hATb : HasActiveTrail G Z x0 b := by
                simpa [hub] using hATu
              have hAXb : ActiveFromXNeY G X Z y b := ⟨x0, hx0, hx0NeY, hATb⟩
              have hStateB : ActiveFromXState G X Z b :=
                activeFromXState_of_activeFromX_notInZ G X Z
                  (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
              exact hStep (p' := b :: c :: rest')
                hTailLen
                hy hby hStateB hAXb
                (Or.inr hbNotZ)
                (List.cons_ne_nil _ _)
                hEndsTail hTailTrail hAvoidTail
            · have hux : UndirectedEdge G u x :=
                activeTrail_last_edge G Z (p := pref) (b := u) (c := x) hTrail0
              cases hux with
              | inl hux_in =>
                  have _ := hux_in
                  have hAX0 : ActiveFromXNeY G X Z y x := ⟨x0, hx0, hx0NeY, hAT0⟩
                  have hxRel : x ∈ relevantVertices G X Y Z :=
                    left_relevant_of_moral_edge G X Y Z hEdge_xb
                  rcases relevant_not_ancZ_reaches_XY G X Y Z hxRel hxAncZ with
                    hxXY | ⟨w, hwXY, hreachXW, _⟩
                  · rcases hxXY with hxX | hxY
                    · exact (hxNotX hxX).elim
                    · exact (hxNotY hxY).elim
                  · by_cases hwNe : w ≠ y
                    · rcases hwXY with hwX | hwY
                      · have hAXb : ActiveFromXNeY G X Z y b :=
                          activeFromXNeY_of_backward_detour_to_X_at_b
                            G X Z hacyclic hwX hwNe hbx hreachXW hxAncZ
                        have hStateB : ActiveFromXState G X Z b :=
                          activeFromXState_of_activeFromX_notInZ G X Z
                            (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
                        exact hStep (p' := b :: c :: rest')
                          hTailLen
                          hy hby hStateB hAXb
                          (Or.inr hbNotZ)
                          (List.cons_ne_nil _ _)
                          hEndsTail hTailTrail hAvoidTail
                      · by_cases hwX' : w ∈ X
                        · have hAXb : ActiveFromXNeY G X Z y b :=
                            activeFromXNeY_of_backward_detour_to_X_at_b
                              G X Z hacyclic hwX' hwNe hbx hreachXW hxAncZ
                          have hStateB : ActiveFromXState G X Z b :=
                            activeFromXState_of_activeFromX_notInZ G X Z
                              (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
                          exact hStep (p' := b :: c :: rest')
                            hTailLen
                            hy hby hStateB hAXb
                            (Or.inr hbNotZ)
                            (List.cons_ne_nil _ _)
                            hEndsTail hTailTrail hAvoidTail
                        · exact activeWitness_of_anchor_reach_to_Y_from_notAnc_head
                            G X Y Z hacyclic hAX0 hreachXW hxAncZ hwY hwX'
                    · have hwEq : w = y := by
                        by_contra hneq
                        exact hwNe hneq
                      rcases reachable_to_directedChain G hreachXW with
                        ⟨q, hqne, hqHead, hqLast, hqChain⟩
                      cases q with
                      | nil =>
                          exact (hqne rfl).elim
                      | cons x' qrest =>
                          have hxx' : x' = x := by simpa using hqHead
                          have hNotZq : ∀ u ∈ (x' :: qrest), u ∉ Z := by
                            intro u hu
                            exact not_in_Z_of_reachable_of_not_in_ancZ G Z hxAncZ
                              (hxx' ▸ directedChain_reachable_from_head G hqChain u hu)
                          have hAXyTmp :
                              ActiveFromXNeY G X Z y
                                ((x' :: qrest).getLast (by simp : (x' :: qrest) ≠ [])) :=
                            activeFromXNeY_of_directedChain_head
                              G X Z hacyclic (a := x) (q := x' :: qrest)
                              (by simp) (by simp [hxx']) hqChain hNotZq hAX0
                          have hLastEq : (x' :: qrest).getLast (by simp : (x' :: qrest) ≠ []) = w := by
                            have hLastSome : (x' :: qrest).getLast? = some w := by simpa using hqLast
                            exact Option.some.inj hLastSome
                          have hAXy : ActiveFromXNeY G X Z y y := by
                            simpa [hLastEq, hwEq] using hAXyTmp
                          rcases hAXy with ⟨x1, hx1, hx1NeY, hATy⟩
                          exact ⟨x1, hx1, y, hy, hx1NeY, hATy⟩
              | inr hxu =>
                  let t : PathTriple G := ⟨u, x, b, (Or.inr hxu), (Or.inr hbx), hub⟩
                  have hNonCol : IsNonCollider G t := by
                    intro hCol
                    have hux' : G.edges u x := hCol.1
                    exact G.isAcyclic_iff_no_self_reach.mp hacyclic x u hxu (G.edge_reachable hux')
                  have hAct : IsActive G Z t :=
                    isActive_of_nonCollider_notInZ G Z t hNonCol hxNotZ
                  have hATb : HasActiveTrail G Z x0 b :=
                    hasActiveTrail_extend_from_snoc
                      (G := G) (Z := Z)
                      (xA := x0) (u := u) (a := x) (pref := pref)
                      hEnds0 hTrail0 (Or.inr hbx) hub (by simpa [t] using hAct)
                  have hAXb : ActiveFromXNeY G X Z y b := ⟨x0, hx0, hx0NeY, hATb⟩
                  have hStateB : ActiveFromXState G X Z b :=
                    activeFromXState_of_activeFromX_notInZ G X Z
                      (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
                  exact hStep (p' := b :: c :: rest')
                    hTailLen
                    hy hby hStateB hAXb
                    (Or.inr hbNotZ)
                    (List.cons_ne_nil _ _)
                    hEndsTail hTailTrail hAvoidTail
      · have hxb_ne : x ≠ b := ne_of_moral_undirected_edge G X Y Z hEdge_xb
        by_cases hc'AncZ : c' ∈ ancestorClosure G Z
        · have hAXb : ActiveFromXNeY G X Z y b :=
            activeFromXNeY_of_anchor_step_spouse_activated
              G X Z hacyclic hAX hxc' hbc' hxb_ne hxNotZ hc'AncZ
          have hStateB : ActiveFromXState G X Z b :=
            activeFromXState_of_activeFromX_notInZ G X Z
              (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
          exact hStep (p' := b :: c :: rest')
            hTailLen
            hy hby hStateB hAXb
            (Or.inr hbNotZ)
            (List.cons_ne_nil _ _)
            hEndsTail hTailTrail hAvoidTail
        · rcases relevant_not_ancZ_reaches_XY G X Y Z hc'Rel hc'AncZ with
            hc'XY | ⟨w, hwXY, hreach, _⟩
          ·
            have hProcess :
                ∀ {w : V}, (w ∈ X ∨ w ∈ Y) → G.Reachable c' w →
                  ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
              intro w hwXY hreachW
              by_cases hwY : w ∈ Y
              · by_cases hwEqY : w = y
                · have hreachXY : G.Reachable x y := by
                    exact G.reachable_trans (G.edge_reachable hxc') (hwEqY ▸ hreachW)
                  exact activeWitness_of_anchor_forward_detour_to_exactY
                    G X Y Z hacyclic hAX hxc' (hwEqY ▸ hreachW) hc'AncZ hxNotZ hy
                · by_cases hwX : w ∈ X
                  · have hAXb : ActiveFromXNeY G X Z y b :=
                      activeFromXNeY_of_backward_detour_to_X_at_b
                        G X Z hacyclic hwX hwEqY hbc' hreachW hc'AncZ
                    have hStateB : ActiveFromXState G X Z b :=
                      activeFromXState_of_activeFromX_notInZ G X Z
                        (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
                    exact hStep (p' := b :: c :: rest')
                      hTailLen
                      hy hby hStateB hAXb
                      (Or.inr hbNotZ)
                      (List.cons_ne_nil _ _)
                      hEndsTail hTailTrail hAvoidTail
                  · exact activeWitness_of_anchor_forward_detour_to_Y
                      G X Y Z hacyclic hAX hxc' hreachW hc'AncZ hxNotZ hwY hwX
              · have hwX : w ∈ X := by
                  rcases hwXY with hwX | hwY'
                  · exact hwX
                  · exact (hwY hwY').elim
                have hwNeY : w ≠ y := by
                  intro hEq
                  apply hwY
                  simpa [hEq] using hy
                have hAXb : ActiveFromXNeY G X Z y b :=
                  activeFromXNeY_of_backward_detour_to_X_at_b
                    G X Z hacyclic hwX hwNeY hbc' hreachW hc'AncZ
                have hStateB : ActiveFromXState G X Z b :=
                  activeFromXState_of_activeFromX_notInZ G X Z
                    (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
                exact hStep (p' := b :: c :: rest')
                  hTailLen
                  hy hby hStateB hAXb
                  (Or.inr hbNotZ)
                  (List.cons_ne_nil _ _)
                  hEndsTail hTailTrail hAvoidTail
            exact hProcess hc'XY (G.reachable_refl c')
          ·
            have hProcess :
                ∀ {w : V}, (w ∈ X ∨ w ∈ Y) → G.Reachable c' w →
                  ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
              intro w hwXY hreachW
              by_cases hwY : w ∈ Y
              · by_cases hwEqY : w = y
                · have hreachXY : G.Reachable x y := by
                    exact G.reachable_trans (G.edge_reachable hxc') (hwEqY ▸ hreachW)
                  exact activeWitness_of_anchor_forward_detour_to_exactY
                    G X Y Z hacyclic hAX hxc' (hwEqY ▸ hreachW) hc'AncZ hxNotZ hy
                · by_cases hwX : w ∈ X
                  · have hAXb : ActiveFromXNeY G X Z y b :=
                      activeFromXNeY_of_backward_detour_to_X_at_b
                        G X Z hacyclic hwX hwEqY hbc' hreachW hc'AncZ
                    have hStateB : ActiveFromXState G X Z b :=
                      activeFromXState_of_activeFromX_notInZ G X Z
                        (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
                    exact hStep (p' := b :: c :: rest')
                      hTailLen
                      hy hby hStateB hAXb
                      (Or.inr hbNotZ)
                      (List.cons_ne_nil _ _)
                      hEndsTail hTailTrail hAvoidTail
                  · exact activeWitness_of_anchor_forward_detour_to_Y
                      G X Y Z hacyclic hAX hxc' hreachW hc'AncZ hxNotZ hwY hwX
              · have hwX : w ∈ X := by
                  rcases hwXY with hwX | hwY'
                  · exact hwX
                  · exact (hwY hwY').elim
                have hwNeY : w ≠ y := by
                  intro hEq
                  apply hwY
                  simpa [hEq] using hy
                have hAXb : ActiveFromXNeY G X Z y b :=
                  activeFromXNeY_of_backward_detour_to_X_at_b
                    G X Z hacyclic hwX hwNeY hbc' hreachW hc'AncZ
                have hStateB : ActiveFromXState G X Z b :=
                  activeFromXState_of_activeFromX_notInZ G X Z
                    (activeFromX_of_activeFromXNeY G X Z hAXb) hbNotZ
                exact hStep (p' := b :: c :: rest')
                  hTailLen
                  hy hby hStateB hAXb
                  (Or.inr hbNotZ)
                  (List.cons_ne_nil _ _)
                  hEndsTail hTailTrail hAvoidTail
            exact hProcess hwXY hreach
  | [], hpne', _ =>
    exact (hpne' rfl).elim

/-- If there is a moral-ancestral trail from x∈X to y∈Y avoiding Z,
    then there is an active trail between some pair in X×Y.
    This is the key lemma for Phase 2 (hMoralToAT direction).

    Route A status: completed with state-first recursion on `ActiveFromXState`
    and anchored witness threading via `ActiveFromXNeY`. -/
theorem not_dsepFull_of_moralTrail
    (G : DirectedGraph V) (X Y Z : Set V)
    (hacyclic : G.IsAcyclic) (_hirr : ∀ v, ¬G.edges v v)
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y) (hxy : x ≠ y)
    {p : List V} (hpne : p ≠ [])
    (hEnds : PathEndpoints p = some (x, y))
    (hTrail : IsTrail (moralAncestralGraph G X Y Z) p)
    (hAvoid : PathAvoidsInternals Z p) :
    ¬DSeparatedFull G X Y Z := by
  -- Strong induction on trail length
  suffices auxState : ∀ (n : ℕ) {x y : V} {p : List V},
      p.length ≤ n →
      y ∈ Y → x ≠ y →
      ActiveFromXState G X Z x →
      ActiveFromXNeY G X Z y x →
      (x ∈ X ∨ x ∉ Z) →
      p ≠ [] →
      PathEndpoints p = some (x, y) →
      IsTrail (moralAncestralGraph G X Y Z) p →
      PathAvoidsInternals Z p →
      ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' from by
    rcases auxState p.length (le_refl _) hy hxy
      (activeFromXState_of_memX G X Z hx)
      (activeFromXNeY_of_memX G X Z hx hxy)
      (Or.inl hx) hpne hEnds hTrail hAvoid with
      ⟨x', hx', y', hy', hxy', hAT'⟩
    intro hDSep
    exact hDSep x' hx' y' hy' hxy' hAT'
  intro n
  induction n with
  | zero => intro hlen _ _ _ _ hpne; simp_all
  | succ n ih =>
    intro x y p hlen hy hxy hState hAX hHeadSafe hpne hEnds hTrail hAvoid
    by_cases hx : x ∈ X
    · match p, hpne, hTrail with
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
            have hAXb : ActiveFromXNeY G X Z y b :=
              activeFromXNeY_of_memX G X Z hbX hby
            exact ih hTailLen hy hby
              (activeFromXState_of_memX G X Z hbX) hAXb
              (Or.inl hbX)
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
                    activeFromXState_step_direct G X Z hState hx hDirect
                      (headPassability_of_ancZ G Z hbAncZ)
                  have hby : b ≠ y := fun h => hbY (h ▸ hy)
                  have hAXb : ActiveFromXNeY G X Z y b :=
                    activeFromXNeY_direct_transition G X Z (y := y) hx hxy hDirect
                  exact ih hTailLen hy hby hStateB hAXb
                    (Or.inr hbNotZ)
                    (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
                · by_cases hc'AncZ : c' ∈ ancestorClosure G Z
                  · have hxb_ne : x ≠ b :=
                      ne_of_moral_undirected_edge G X Y Z hEdge_xb
                    have hStateB : ActiveFromXState G X Z b :=
                      activeFromXState_step_spouse_activated
                        G X Z hState hx hxb_ne hxc' hbc' hc'AncZ
                        (headPassability_of_ancZ G Z hbAncZ)
                    have hby : b ≠ y := fun h => hbY (h ▸ hy)
                    have hAXb : ActiveFromXNeY G X Z y b :=
                      activeFromXNeY_spouse_activated_transition
                        G X Z (y := y) hx hxy hxb_ne hxc' hbc' hc'AncZ
                    exact ih hTailLen hy hby hStateB hAXb
                      (Or.inr hbNotZ)
                      (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
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
                            have hby : b ≠ y := fun h => hbY (h ▸ hy)
                            have hc'ne : c' ≠ y := by
                              intro h
                              apply hc'Y'
                              simpa [h] using hy
                            have hAXb : ActiveFromXNeY G X Z y b :=
                              activeFromXNeY_of_backward_detour_to_X_at_b
                                G X Z hacyclic hc'X hc'ne hbc' (G.reachable_refl c') hc'AncZ
                            exact ih hTailLen hy hby hStateB hAXb
                              (Or.inr hbNotZ)
                              (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
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
                            have hby : b ≠ y := fun h => hbY (h ▸ hy)
                            have hwNe : w ≠ y := by
                              intro h
                              apply hwY'
                              simpa [h] using hy
                            have hAXb : ActiveFromXNeY G X Z y b :=
                              activeFromXNeY_of_backward_detour_to_X_at_b
                                G X Z hacyclic hwX hwNe hbc' hreach hc'AncZ
                            exact ih hTailLen hy hby hStateB hAXb
                              (Or.inr hbNotZ)
                              (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
                      · exact activeWitness_of_forward_detour_to_Y
                          G X Y Z hacyclic hx hwY hxc' hreach hc'AncZ
            · -- b ∉ Anc(Z): b reaches w ∈ X∪Y
              rcases relevant_not_ancZ_reaches_XY G X Y Z hbRel hbAncZ with
                hbXY | ⟨w, hwXY, hreachBW, hbw⟩
              · -- b ∈ X∪Y: contradiction
                rcases hbXY with hbXX | hbYY
                · exact absurd hbXX hbX
                · exact absurd hbYY hbY
              ·
                have hReachY : w ∈ Y → ∃ x' ∈ X, ∃ y' ∈ Y, x' ≠ y' ∧ HasActiveTrail G Z x' y' := by
                  intro hwY
                  -- b reaches w ∈ Y
                  -- Decompose first edge to prepend x.
                  rcases moralAncestralEdge_decompose G X Y Z hEdge_xb with
                    ⟨hDirect, _, _⟩ | ⟨c', hxc', hbc', hc'Rel, _, _⟩
                  · -- Direct edge x—b: build [x, b, ..., w∈Y]
                    rcases hDirect with hxb_edge | hbx_edge
                    · exact activeWitness_of_forward_detour_to_Y
                        G X Y Z hacyclic hx hwY hxb_edge hreachBW hbAncZ
                    ·
                      -- Recurse from `b` directly; this avoids orientation-specific subcases.
                      have hStateB : ActiveFromXState G X Z b :=
                        activeFromXState_step_direct
                          G X Z hState hx (Or.inr hbx_edge)
                          (headPassability_of_notInZ G Z hbNotZ)
                      have hby : b ≠ y := fun h => hbY (h ▸ hy)
                      have hAXb : ActiveFromXNeY G X Z y b :=
                        activeFromXNeY_direct_transition G X Z (y := y) hx hxy (Or.inr hbx_edge)
                      exact ih hTailLen hy hby hStateB hAXb
                        (Or.inr hbNotZ)
                        (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
                  · -- Spouse edge: x→c' and b→c'. Try [x, c', b, ..., w∈Y]
                    by_cases hc'AncZ : c' ∈ ancestorClosure G Z
                    · have hxb_ne : x ≠ b :=
                        ne_of_moral_undirected_edge G X Y Z hEdge_xb
                      have hStateB : ActiveFromXState G X Z b :=
                        activeFromXState_step_spouse_activated
                          G X Z hState hx hxb_ne hxc' hbc' hc'AncZ
                          (headPassability_of_notInZ G Z hbNotZ)
                      have hby : b ≠ y := fun h => hbY (h ▸ hy)
                      have hAXb : ActiveFromXNeY G X Z y b :=
                        activeFromXNeY_spouse_activated_transition
                          G X Z (y := y) hx hxy hxb_ne hxc' hbc' hc'AncZ
                      exact ih hTailLen hy hby hStateB hAXb
                        (Or.inr hbNotZ)
                        (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
                    · rcases relevant_not_ancZ_reaches_XY G X Y Z hc'Rel hc'AncZ with
                        hc'XY | ⟨u, huXY, hreachCU, _⟩
                      · rcases hc'XY with hc'X | hc'Y
                        · by_cases hc'Y' : c' ∈ Y
                          · have hxc'_ne : x ≠ c' := fun h => by
                              subst h
                              exact G.isAcyclic_irrefl hacyclic x hxc'
                            exact ⟨x, hx, c', hc'Y', hxc'_ne,
                              ⟨[x, c'], by simp, by simp [PathEndpoints], ActiveTrail.two (Or.inl hxc')⟩⟩
                          · by_cases hxY' : x ∈ Y
                            · exact activeWitness_of_backward_detour_to_X
                                G X Y Z hacyclic hc'X hxY' hxc' (G.reachable_refl c') hc'AncZ
                            · have hStateB : ActiveFromXState G X Z b :=
                                activeFromXState_backward_detour_notInZ
                                  G X Z hacyclic hc'X hbc' (G.reachable_refl c') hc'AncZ hbNotZ
                              have hby : b ≠ y := fun h => hbY (h ▸ hy)
                              have hc'ne : c' ≠ y := by
                                intro h
                                apply hc'Y'
                                simpa [h] using hy
                              have hAXb : ActiveFromXNeY G X Z y b :=
                                activeFromXNeY_of_backward_detour_to_X_at_b
                                  G X Z hacyclic hc'X hc'ne hbc' (G.reachable_refl c') hc'AncZ
                              exact ih hTailLen hy hby hStateB hAXb
                                (Or.inr hbNotZ)
                                (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
                        · have hxc'_ne : x ≠ c' := fun h => by
                            subst h
                            exact G.isAcyclic_irrefl hacyclic x hxc'
                          exact activeWitness_of_not_dsepFull G X Y Z (by
                            intro hDSep
                            exact absurd_dsep_of_activeTrail G X Y Z hx hc'Y hxc'_ne
                              (by simp) (by simp [PathEndpoints]) (ActiveTrail.two (Or.inl hxc'))
                              hDSep)
                      · rcases huXY with huX | huY
                        · by_cases huY' : u ∈ Y
                          · exact activeWitness_of_forward_detour_to_Y
                              G X Y Z hacyclic hx huY' hxc' hreachCU hc'AncZ
                          · by_cases hxY' : x ∈ Y
                            · exact activeWitness_of_backward_detour_to_X
                                G X Y Z hacyclic huX hxY' hxc' hreachCU hc'AncZ
                            · have hStateB : ActiveFromXState G X Z b :=
                                activeFromXState_backward_detour_notInZ
                                  G X Z hacyclic huX hbc' hreachCU hc'AncZ hbNotZ
                              have hby : b ≠ y := fun h => hbY (h ▸ hy)
                              have huNe : u ≠ y := by
                                intro h
                                apply huY'
                                simpa [h] using hy
                              have hAXb : ActiveFromXNeY G X Z y b :=
                                activeFromXNeY_of_backward_detour_to_X_at_b
                                  G X Z hacyclic huX huNe hbc' hreachCU hc'AncZ
                              exact ih hTailLen hy hby hStateB hAXb
                                (Or.inr hbNotZ)
                                (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
                        · exact activeWitness_of_forward_detour_to_Y
                            G X Y Z hacyclic hx huY hxc' hreachCU hc'AncZ
                rcases hwXY with hwX | hwY
                · by_cases hwY' : w ∈ Y
                  · exact hReachY hwY'
                  · have hStateB : ActiveFromXState G X Z b :=
                      activeFromXState_backward_reach_notInZ
                        G X Z hacyclic hwX hreachBW hbAncZ hbNotZ
                    have hby : b ≠ y := fun h => hbY (h ▸ hy)
                    have hwNe : w ≠ y := by
                      intro h
                      apply hwY'
                      simpa [h] using hy
                    have hAXb : ActiveFromXNeY G X Z y b :=
                      activeFromXNeY_of_backward_reach_to_X_at_head
                        G X Z hacyclic hwX hwNe hreachBW hbAncZ
                    exact ih hTailLen hy hby hStateB hAXb
                      (Or.inr hbNotZ)
                      (List.cons_ne_nil _ _) hEndsTail hTailTrail hAvoidTail
                · exact hReachY hwY
    · -- Route-A fallback: if current head already lies in Y, the stored
      -- anchor witness immediately yields an X×Y active-trail witness.
      by_cases hxY : x ∈ Y
      · rcases activeFromXState_anchor G X Z hState with ⟨x0, hx0, hAT0⟩
        have hx0x_ne : x0 ≠ x := by
          intro hEq
          apply hx
          simpa [hEq] using hx0
        exact ⟨x0, hx0, x, hxY, hx0x_ne, hAT0⟩
      · -- Remaining hard state-only branch: x ∉ X ∪ Y.
        have hxNotZ : x ∉ Z := by
          rcases hHeadSafe with hxX | hxNZ
          · exact (hx hxX).elim
          · exact hxNZ
        have hStep :
            ∀ {x' y' : V} {p' : List V},
              p'.length < p.length →
              y' ∈ Y → x' ≠ y' →
              ActiveFromXState G X Z x' →
              ActiveFromXNeY G X Z y' x' →
              (x' ∈ X ∨ x' ∉ Z) →
              p' ≠ [] →
              PathEndpoints p' = some (x', y') →
              IsTrail (moralAncestralGraph G X Y Z) p' →
              PathAvoidsInternals Z p' →
              ∃ x'' ∈ X, ∃ y'' ∈ Y, x'' ≠ y'' ∧ HasActiveTrail G Z x'' y'' := by
          intro x' y' p' hp'lt hy' hxy' hState' hAX' hHeadSafe' hp'ne hEnds' hTrail' hAvoid'
          have hlen' : p'.length ≤ n := by
            omega
          exact ih hlen' hy' hxy' hState' hAX' hHeadSafe' hp'ne hEnds' hTrail' hAvoid'
        exact activeWitness_of_state_fallback
          G X Y Z hacyclic hy hxy hState hAX hx hxY hxNotZ hpne hEnds hTrail hAvoid hStep

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
