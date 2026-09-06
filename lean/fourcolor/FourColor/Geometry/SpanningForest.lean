import FourColor.Geometry.DiskTypes
import FourColor.Geometry.NoDigons
import FourColor.Geometry.PlanarityHelpers
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Spanning Forest for Planar Dual Graphs

**MINIMAL REWRITE** of DualForest.lean using only functions that actually exist.

## Strategy

Instead of the complex 3978-line approach, we prove `exists_spanning_forest` using a simple
greedy construction:

1. Define the dual graph using our existing `dualAdjacent`
2. Build spanning forest by taking a maximal acyclic subset of edges
3. Prove the dichotomy property using `NoDigons`

This removes all mathlib API mismatches and provides a clean ~100-line proof.

## Main Result

- `exists_spanning_forest`: Every DiskGeometry has a spanning forest on its dual graph

-/

namespace FourColor.Geometry

open Finset Relation
open FourColor
open FourColor.Geometry.RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Face Subtype and Acyclicity -/

/-- **Internal Face** - A face that is not the boundary.

    The dual graph lives over internal faces, not arbitrary Finset E.
    Using this subtype eliminates "proof that f is a face" obligations. -/
abbrev Face (G : DiskGeometry V E) :=
  {f : Finset E // f ∈ G.toRotationSystem.internalFaces}

/-- An acyclic set of tree edges: no edge creates a cycle in the dual graph.

    REFACTORED: Now uses Face G subtype - vertices of dual graph ARE faces.
    This eliminates infrastructure sorries about "f is actually a face". -/
def isAcyclic (G : DiskGeometry V E) (tree_edges : Finset E) : Prop :=
  ∀ e ∈ tree_edges, ∀ (f g : Face G),
    f ≠ g →
    e ∈ f.1 → e ∈ g.1 →
    ¬ Relation.ReflTransGen (fun f' g' => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f'.1 ∧ e' ∈ g'.1) f g

/-! ## Helper Lemmas -/


/-- Reverse a `ReflTransGen` path when the relation is symmetric. -/
lemma rflTransGen_reverse_of_symmetric {α : Type*} {R : α → α → Prop}
    (hSym : Symmetric R) {a b : α} (h : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
      exact .head (hSym hab) ih

/-- Lift a path from one domain to another given a mapping function. -/
lemma lift_path {α β : Type*} {R : α → α → Prop} {Q : β → β → Prop} (f : α → β)
    (h : ∀ a b, R a b → Q (f a) (f b)) (a b : α) (p : ReflTransGen R a b) :
    ReflTransGen Q (f a) (f b) := by
  induction p with
  | refl => exact ReflTransGen.refl
  | tail _ hab ih => exact ReflTransGen.tail ih (h _ _ hab)

/-- If a path exists in `R ∪ S` but not in `R`, it must use a step from `S`. -/
lemma path_must_use_new_edge {α : Type*} {R S : α → α → Prop} {a b : α}
    (h_path : ReflTransGen (fun x y => R x y ∨ S x y) a b)
    (h_not_R : ¬ ReflTransGen R a b) :
    ∃ x y, ReflTransGen R a x ∧ S x y ∧ x ≠ y ∧ ReflTransGen (fun x y => R x y ∨ S x y) y b := by
  induction h_path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exfalso
    exact h_not_R .refl
  | head h_step h_rest IH =>
    rename_i a' c
    cases h_step with
    | inl h_R =>
      by_cases h_R_rest : ReflTransGen R c b
      · exfalso; exact h_not_R (.head h_R h_R_rest)
      · obtain ⟨x, y, h_cx, h_Sxy, h_ne, h_yb⟩ := IH h_R_rest
        exact ⟨x, y, .head h_R h_cx, h_Sxy, h_ne, h_yb⟩
    | inr h_S =>
      if h_eq : a' = c then
        subst h_eq
        apply IH
        exact h_not_R
      else
        exact ⟨a', c, .refl, h_S, h_eq, h_rest⟩

/-- **Lifted version**: Path must use new edge, specialized to Face G.

    This version works over the Face G subtype, so the endpoints are
    automatically internal faces - no infrastructure sorries needed! -/
lemma path_must_use_new_edge_face (G : DiskGeometry V E)
    {R S : Face G → Face G → Prop}
    {a b : Face G}
    (h_path : ReflTransGen (fun x y => R x y ∨ S x y) a b)
    (h_not_R : ¬ ReflTransGen R a b) :
    ∃ x y, ReflTransGen R a x ∧ S x y ∧ x ≠ y ∧ ReflTransGen (fun x y => R x y ∨ S x y) y b := by
  -- Same proof as path_must_use_new_edge, just with Face G as α
  induction h_path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exfalso
    exact h_not_R .refl
  | head h_step h_rest IH =>
    rename_i a' c
    cases h_step with
    | inl h_R =>
      by_cases h_R_rest : ReflTransGen R c b
      · exfalso; exact h_not_R (.head h_R h_R_rest)
      · obtain ⟨x, y, h_cx, h_Sxy, h_ne, h_yb⟩ := IH h_R_rest
        exact ⟨x, y, .head h_R h_cx, h_Sxy, h_ne, h_yb⟩
    | inr h_S =>
      if h_eq : a' = c then
        subst h_eq
        apply IH
        exact h_not_R
      else
        exact ⟨a', c, .refl, h_S, h_eq, h_rest⟩


/-! ## Dual Graph Construction

We don't need SimpleGraph - we can work directly with our `dualAdjacent` relation
and `ReflTransGen` for connectivity.
-/

/-- A maximal acyclic set: adding any interior edge creates a cycle -/
def isMaximalAcyclic (G : DiskGeometry V E) (tree_edges : Finset E) : Prop :=
  isAcyclic G tree_edges ∧
  ∀ e, e ∉ G.toRotationSystem.boundaryEdges →
    e ∉ tree_edges →
    ¬isAcyclic G (insert e tree_edges)

/-! ## Path Transport Lemmas

Helpers for transporting ReflTransGen paths between Face G and Finset E. -/

/-- Transport a path from Face G to the underlying Finset E,
    filtering relation to only use edges in a given set. -/
lemma transport_face_path_to_finset {G : DiskGeometry V E} {tree_edges : Finset E}
    {f' g' : Face G} {extra : E}
    (h_path : ReflTransGen (fun (x y : Face G) =>
      ∃ e' ∈ insert extra tree_edges, e' ≠ extra ∧ e' ∈ x.1 ∧ e' ∈ y.1) f' g') :
    ReflTransGen (fun (x y : Finset E) =>
      ∃ e' ∈ tree_edges, e' ≠ extra ∧ e' ∈ x ∧ e' ∈ y) f'.1 g'.1 := by
  induction h_path using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head h_step h_rest IH =>
    obtain ⟨e', he'_ins, hne, hx, hy⟩ := h_step
    have he'_tree : e' ∈ tree_edges := by
      simp only [Finset.mem_insert] at he'_ins
      cases he'_ins with
      | inl heq => rw [heq] at hne; contradiction
      | inr hmem => exact hmem
    exact .head ⟨e', he'_tree, hne, hx, hy⟩ IH

/-! ## Fundamental Cycle Property

The fundamental cycle property is a cornerstone theorem in graph theory:
When adding an edge to an acyclic graph creates a cycle, the endpoints of
that edge must already be connected in the original graph. -/

lemma fundamental_cycle_property
    (G : DiskGeometry V E)
    (tree_edges : Finset E)
    (h_tree_acyclic : isAcyclic G tree_edges)
    {e : E} (he_int : e ∉ G.toRotationSystem.boundaryEdges)
    (he_notin : e ∉ tree_edges)
    (h_not_acyclic : ¬ isAcyclic G (insert e tree_edges)) :
  ∃ f g,
    f ∈ G.toRotationSystem.internalFaces ∧
    g ∈ G.toRotationSystem.internalFaces ∧
    f ≠ g ∧
    e ∈ f ∧ e ∈ g ∧
    ReflTransGen
      (fun f' g' => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f' ∧ e' ∈ g')
      f g := by
  -- Step 1: Extract the two faces incident to e using E2
  obtain ⟨fg, ⟨hcard2, hfaces⟩, hunique⟩ :=
    two_internal_faces_of_interior_edge G.toPlanarGeometry he_int
  rcases Finset.card_eq_two.mp hcard2 with ⟨f, g, hfg_ne, hfg_pair⟩
  have hf : f ∈ G.toRotationSystem.internalFaces := (hfaces f (by simp [hfg_pair])).1
  have hg : g ∈ G.toRotationSystem.internalFaces := (hfaces g (by simp [hfg_pair])).1
  have he_f : e ∈ f := (hfaces f (by simp [hfg_pair])).2
  have he_g : e ∈ g := (hfaces g (by simp [hfg_pair])).2

  -- Step 2: Unfold ¬isAcyclic to get witness
  unfold isAcyclic at h_not_acyclic
  push_neg at h_not_acyclic

  -- Extract witness: some edge e' witnesses non-acyclicity
  -- NOTE: f' and g' are now Face G types, so f'.property gives us membership automatically!
  obtain ⟨e_witness, he'_in, f', g', hf'_ne_g', he'_f', he'_g', h_path⟩ := h_not_acyclic

  -- Step 3: Case split - is the witness edge e itself, or something in tree_edges?
  have he'_cases : e_witness = e ∨ e_witness ∈ tree_edges := by
    simp only [Finset.mem_insert] at he'_in
    exact he'_in

  cases he'_cases with
  | inl he'_eq =>
    -- Case e' = e: The witness edge is e itself!
    -- This means e's two faces f' and g' are connected via (insert e tree_edges) \ {e}
    -- which is just tree_edges
    rw [he'_eq] at he'_f' he'_g' h_path

    -- Use E2 uniqueness: {f'.1, g'.1} must equal {f, g}
    have hcard_f'g' : ({f'.1, g'.1} : Finset (Finset E)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      intro h_eq
      exact hf'_ne_g' (Subtype.eq h_eq)

    have hfaces_f'g' : ∀ face ∈ ({f'.1, g'.1} : Finset (Finset E)),
        face ∈ G.toRotationSystem.internalFaces ∧ e ∈ face := by
      intro face hface
      simp only [Finset.mem_insert, Finset.mem_singleton] at hface
      cases hface with
      | inl heq => subst heq; exact ⟨f'.property, he'_f'⟩
      | inr heq => subst heq; exact ⟨g'.property, he'_g'⟩

    have hf'g'_eq_fg : {f'.1, g'.1} = fg := hunique _ ⟨hcard_f'g', hfaces_f'g'⟩

    -- Extract membership
    have hf'_mem : f'.1 ∈ ({f, g} : Finset (Finset E)) := by
      rw [← hfg_pair, ← hf'g'_eq_fg]; simp
    have hg'_mem : g'.1 ∈ ({f, g} : Finset (Finset E)) := by
      rw [← hfg_pair, ← hf'g'_eq_fg]; simp

    simp only [Finset.mem_insert, Finset.mem_singleton] at hf'_mem hg'_mem

    -- Transform path to use only tree_edges
    have h_path_tree : ReflTransGen (fun f'' g'' : Finset E =>
        ∃ (e'' : E), e'' ∈ tree_edges ∧ e'' ≠ e ∧ e'' ∈ f'' ∧ e'' ∈ g'') f'.1 g'.1 :=
      transport_face_path_to_finset h_path

    -- Handle symmetric cases: (f'.1, g'.1) could be (f, g) or (g, f)
    cases hf'_mem with
    | inl hf'_eq_f =>
      cases hg'_mem with
      | inl hg'_eq_f =>
        -- f'.1 = f and g'.1 = f, so f' = g' by Subtype.eq, contradicting hf'_ne_g'
        have : f' = g' := Subtype.eq (hf'_eq_f.trans hg'_eq_f.symm)
        exact absurd this hf'_ne_g'
      | inr hg'_eq_g =>
        rw [hf'_eq_f, hg'_eq_g] at h_path_tree
        exact ⟨f, g, hf, hg, hfg_ne, he_f, he_g, h_path_tree⟩
    | inr hf'_eq_g =>
      cases hg'_mem with
      | inl hg'_eq_f =>
        rw [hf'_eq_g, hg'_eq_f] at h_path_tree
        -- Need to reverse the path since we have g ~* f but need f ~* g
        have h_sym : Symmetric (fun f'' g'' : Finset E =>
            ∃ (e'' : E), e'' ∈ tree_edges ∧ e'' ≠ e ∧ e'' ∈ f'' ∧ e'' ∈ g'') := by
          intro x y ⟨e'', hmem, hne, hx, hy⟩
          exact ⟨e'', hmem, hne, hy, hx⟩
        have h_path_rev := rflTransGen_reverse_of_symmetric h_sym h_path_tree
        exact ⟨f, g, hf, hg, hfg_ne, he_f, he_g, h_path_rev⟩
      | inr hg'_eq_g =>
        -- f'.1 = g and g'.1 = g, so f' = g' by Subtype.eq, contradicting hf'_ne_g'
        have : f' = g' := Subtype.eq (hf'_eq_g.trans hg'_eq_g.symm)
        exact absurd this hf'_ne_g'

  | inr he'_in_tree =>
    -- Case e' ∈ tree_edges: The witness is an old edge (e' ≠ e)
    -- Since tree_edges is acyclic, e' is a bridge in tree_edges.
    -- Removing e' disconnects its endpoints f' and g' in tree_edges.
    -- But h_path connects them in (insert e tree_edges) \ {e'}
    -- which is (tree_edges \ {e'}) ∪ {e}.
    -- Therefore, the path MUST use e.
    -- This implies endpoints of e (f, g) are connected to endpoints of e' (f', g').
    -- Since f' connected to g' via e', we get connectivity f ~ g in tree_edges.

    -- 1. Get E2 property for edge e (not e')
    obtain ⟨fg_e, ⟨hcard2_e, hfaces_e⟩, hunique_e⟩ :=
      two_internal_faces_of_interior_edge G.toPlanarGeometry he_int
    rcases Finset.card_eq_two.mp hcard2_e with ⟨f, g, hfg_ne, hfg_pair⟩
    have hf : f ∈ G.toRotationSystem.internalFaces := (hfaces_e f (by simp [hfg_pair])).1
    have hg : g ∈ G.toRotationSystem.internalFaces := (hfaces_e g (by simp [hfg_pair])).1
    have he_f : e ∈ f := (hfaces_e f (by simp [hfg_pair])).2
    have he_g : e ∈ g := (hfaces_e g (by simp [hfg_pair])).2

    -- 2. Define relations for path splitting
    let R := fun (x y : Face G) => ∃ e' ∈ tree_edges, e' ≠ e_witness ∧ e' ∈ x.1 ∧ e' ∈ y.1
    let S := fun (x y : Face G) => e ∈ x.1 ∧ e ∈ y.1

    -- h_path connects f' and g' using (insert e tree_edges) \ {e_witness}
    -- This is exactly R ∪ S because e ≠ e_witness
    have h_path_RS : ReflTransGen (fun x y => R x y ∨ S x y) f' g' := by
      refine ReflTransGen.mono ?_ _ _ h_path
      intro x y h
      obtain ⟨e', he', hne, hx, hy⟩ := h
      simp only [Finset.mem_insert] at he'
      cases he' with
      | inl heq =>
        subst heq
        right
        exact ⟨hx, hy⟩
      | inr htree =>
        left
        exact ⟨e', htree, hne, hx, hy⟩

    -- 3. Show f' and g' are NOT connected by R (Bridge Property)
    -- If they were, then f' ~ g' in tree_edges \ {e_witness}.
    -- But f' and g' are endpoints of e_witness.
    -- So adding e_witness would create a cycle in tree_edges.
    -- But tree_edges is acyclic!
    have h_not_R : ¬ ReflTransGen R f' g' := by
      intro h_conn
      apply h_tree_acyclic e_witness he'_in_tree f' g' hf'_ne_g' he'_f' he'_g'
      convert h_conn

    -- 4. Use path splitting to find where e is used
    obtain ⟨x, y, h_f'x, h_xy, h_xy_ne, h_yg'⟩ := path_must_use_new_edge_face G h_path_RS h_not_R

    -- e connects x and y, so {x, y} = {f, g}
    have h_xy_eq : insert x.1 (singleton y.1) = ({f, g} : Finset (Finset E)) := by
      -- Use E2 uniqueness on e
      have hcard : (insert x.1 (singleton y.1) : Finset (Finset E)).card = 2 := by
        rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_singleton]
        · simp only [Finset.mem_singleton]
          intro h_eq
          apply h_xy_ne
          apply Subtype.eq
          exact h_eq
      have hfaces_xy : ∀ face ∈ (insert x.1 (singleton y.1) : Finset (Finset E)),
          face ∈ G.toRotationSystem.internalFaces ∧ e ∈ face := by
        intro face hface
        simp only [Finset.mem_insert, Finset.mem_singleton] at hface
        cases hface with
        | inl heq => subst heq; exact ⟨x.property, h_xy.1⟩
        | inr heq => subst heq; exact ⟨y.property, h_xy.2⟩
      have : insert x.1 (singleton y.1) = fg_e := hunique_e _ ⟨hcard, hfaces_xy⟩
      rw [this, ← hfg_pair]

    -- 5. f' ~> x in R
    have h_f'x_tree : ReflTransGen (fun x y => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ x.1 ∧ e' ∈ y.1) f' x := by
      refine ReflTransGen.mono ?_ _ _ h_f'x
      rintro a b ⟨e', htree, hne, ha, hb⟩
      exact ⟨e', htree, by rintro rfl; exact he_notin htree, ha, hb⟩

    -- 6. y ~> g' in R
    have h_path_rev : ReflTransGen (fun x y => R x y ∨ S x y) g' f' := by
      apply rflTransGen_reverse_of_symmetric
      · intro a b h; cases h <;> [left; right]
        · rcases ‹R a b› with ⟨e', h1, h2, h3, h4⟩; exact ⟨e', h1, h2, h4, h3⟩
        · rcases ‹S a b› with ⟨h1, h2⟩; exact ⟨h2, h1⟩
      exact h_path_RS

    have h_not_R_rev : ¬ ReflTransGen R g' f' := by
      intro h; apply h_not_R
      apply rflTransGen_reverse_of_symmetric
      · intro a b ⟨e', h1, h2, h3, h4⟩; exact ⟨e', h1, h2, h4, h3⟩
      exact h

    obtain ⟨u, v, h_g'u, h_uv, h_uv_ne, _⟩ := path_must_use_new_edge_face G h_path_rev h_not_R_rev

    have h_uv_eq : insert u.1 (singleton v.1) = ({f, g} : Finset (Finset E)) := by
      have hcard : (insert u.1 (singleton v.1) : Finset (Finset E)).card = 2 := by
        rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_singleton]
        · simp only [Finset.mem_singleton]
          intro h_eq
          apply h_uv_ne
          apply Subtype.eq
          exact h_eq
      have hfaces_uv : ∀ face ∈ (insert u.1 (singleton v.1) : Finset (Finset E)),
          face ∈ G.toRotationSystem.internalFaces ∧ e ∈ face := by
        intro face hface
        simp only [Finset.mem_insert, Finset.mem_singleton] at hface
        cases hface with
        | inl heq => subst heq; exact ⟨u.property, h_uv.1⟩
        | inr heq => subst heq; exact ⟨v.property, h_uv.2⟩
      have : insert u.1 (singleton v.1) = fg_e := hunique_e _ ⟨hcard, hfaces_uv⟩
      rw [this, ← hfg_pair]

    have h_x_ne_u : x ≠ u := by
      intro h_eq
      rw [← h_eq] at h_g'u
      have h_x_g' : ReflTransGen R x g' := by
        apply rflTransGen_reverse_of_symmetric
        · intro a b ⟨e', h1, h2, h3, h4⟩; exact ⟨e', h1, h2, h4, h3⟩
        exact h_g'u
      exact h_not_R (Relation.ReflTransGen.trans h_f'x h_x_g')

    have h_y_eq_u : y = u := by
      have h_xy_uv : insert x.1 (singleton y.1) = (insert u.1 (singleton v.1) : Finset (Finset E)) := by rw [h_xy_eq, h_uv_eq]
      have h_x_in_uv : x.1 ∈ (insert u.1 (singleton v.1) : Finset (Finset E)) := by rw [← h_xy_uv]; apply Finset.mem_insert_self
      have h_x_eq_v : x = v := by
        rw [Finset.mem_insert, Finset.mem_singleton] at h_x_in_uv
        cases h_x_in_uv with
        | inl h => exfalso; apply h_x_ne_u; apply Subtype.eq h
        | inr h => apply Subtype.eq h
      have h_y_in_uv : y.1 ∈ (insert u.1 (singleton v.1) : Finset (Finset E)) := by
        rw [← h_xy_uv]
        apply Finset.mem_insert_of_mem
        apply Finset.mem_singleton_self
      rw [Finset.mem_insert, Finset.mem_singleton] at h_y_in_uv
      cases h_y_in_uv with
      | inl h => apply Subtype.eq h
      | inr h =>
        have h_x_ne_y : x ≠ y := by
          intro h; rw [h] at h_xy_eq
          have h1 : (insert y.1 (singleton y.1) : Finset (Finset E)).card = 1 := by
            rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
            exact Finset.card_singleton _
          rw [h_xy_eq] at h1
          have h2 : ({f, g} : Finset (Finset E)).card = 2 := by
            rw [Finset.card_insert_of_notMem, Finset.card_singleton]
            simp; exact hfg_ne
          rw [h1] at h2
          contradiction
        exfalso; apply h_x_ne_y; rw [h_x_eq_v]; apply Subtype.eq h.symm

    rw [← h_y_eq_u] at h_g'u
    have h_yg'_tree : ReflTransGen (fun x y => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ x.1 ∧ e' ∈ y.1) g' y := by
      refine ReflTransGen.mono ?_ _ _ h_g'u
      rintro a b ⟨e', htree, hne, ha, hb⟩
      exact ⟨e', htree, by rintro rfl; exact he_notin htree, ha, hb⟩

    -- 7. Construct full path in tree
    -- f' ~ g' in tree via e' (e_witness)
    -- Path: x ~ f' - g' ~ y
    -- f' ~ x implies x ~ f'
    have h_xf' : ReflTransGen (fun x y => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ x.1 ∧ e' ∈ y.1) x f' := by
      apply rflTransGen_reverse_of_symmetric
      · intro a b ⟨e', h1, h2, h3, h4⟩; exact ⟨e', h1, h2, h4, h3⟩
      exact h_f'x_tree

    have h_f'g' : ReflTransGen (fun x y => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ x.1 ∧ e' ∈ y.1) f' g' := by
      apply Relation.ReflTransGen.single
      exists e_witness
      exact ⟨he'_in_tree, by rintro rfl; exact he_notin he'_in_tree, he'_f', he'_g'⟩

    have h_xy_conn : ReflTransGen (fun x y => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ x.1 ∧ e' ∈ y.1) x y := by
      trans f'
      exact h_xf'
      trans g'
      exact h_f'g'
      exact h_yg'_tree

    -- Project to Finset E
    let R_fin := fun (x y : Finset E) => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ x ∧ e' ∈ y
    have h_xy_fin : ReflTransGen R_fin x.1 y.1 := by
      apply lift_path Subtype.val _ _ _ h_xy_conn
      rintro a b ⟨e', h1, h2, h3, h4⟩
      exact ⟨e', h1, h2, h3, h4⟩

    -- Return result
    have h_x_mem : x.1 ∈ ({f, g} : Finset (Finset E)) := by rw [← h_xy_eq]; apply Finset.mem_insert_self
    have h_y_mem : y.1 ∈ ({f, g} : Finset (Finset E)) := by
      rw [← h_xy_eq]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_singleton_self
    simp only [Finset.mem_insert, Finset.mem_singleton] at h_x_mem h_y_mem

    cases h_x_mem with
    | inl hxf =>
      cases h_y_mem with
      | inl hyf =>
        have : x = y := Subtype.eq (hxf.trans hyf.symm)
        exfalso; exact h_xy_ne this
      | inr hyg =>
        rw [hxf, hyg] at h_xy_fin
        exact ⟨f, g, hf, hg, hfg_ne, he_f, he_g, h_xy_fin⟩
    | inr hxg =>
      cases h_y_mem with
      | inl hyf =>
        rw [hxg, hyf] at h_xy_fin
        have h_rev := rflTransGen_reverse_of_symmetric
          (fun a b ⟨e', h1, h2, h3, h4⟩ => ⟨e', h1, h2, h4, h3⟩)
          h_xy_fin
        exact ⟨f, g, hf, hg, hfg_ne, he_f, he_g, h_rev⟩
      | inr hyg =>
        have : x = y := Subtype.eq (hxg.trans hyg.symm)
        exfalso; exact h_xy_ne this

/-! ## Main Existence Theorem -/

/-- Every finite set of interior edges contains a maximal acyclic subset.

This is a simple finiteness argument: keep adding edges greedily until we can't anymore. -/
lemma exists_maximal_acyclic (G : DiskGeometry V E) :
    ∃ tree_edges : Finset E,
      (∀ e ∈ tree_edges, e ∉ G.toRotationSystem.boundaryEdges) ∧
      isMaximalAcyclic G tree_edges := by
  classical
  -- interior edges as a finset
  let interior_edges : Finset E :=
    Finset.univ.filter (fun e => e ∉ G.toRotationSystem.boundaryEdges)

  -- candidates = all acyclic subsets of the interior edges
  let candidates : Finset (Finset E) :=
    (interior_edges.powerset).filter (fun T => isAcyclic G T)

  have hCand_nonempty : candidates.Nonempty := by
    -- ∅ is acyclic by definition; it is also a subset of interior_edges
    have hEmptyAcyclic : isAcyclic G (∅ : Finset E) := by
      intro e he; simp at he
    have hEmptyIn : (∅ : Finset E) ⊆ interior_edges := by
      intro e he; simp at he
    refine ⟨∅, ?_⟩
    simp [candidates, hEmptyAcyclic, hEmptyIn]

  -- Get a candidate with maximum cardinality using max' on the image
  have hcard_nonempty : (candidates.image Finset.card).Nonempty := by
    exact Finset.Nonempty.image hCand_nonempty _

  let max_card := (candidates.image Finset.card).max' hcard_nonempty

  -- There exists a candidate with this maximum cardinality
  have : ∃ T ∈ candidates, T.card = max_card := by
    have : max_card ∈ candidates.image Finset.card := Finset.max'_mem _ hcard_nonempty
    simp [Finset.mem_image] at this
    exact this

  obtain ⟨T, hT_mem, hT_card⟩ := this

  -- Extract properties from membership in candidates
  have hT_sub : T ⊆ interior_edges := by
    have := (Finset.mem_filter.mp hT_mem).1
    exact (Finset.mem_powerset.mp this)
  have hT_acyclic : isAcyclic G T := (Finset.mem_filter.mp hT_mem).2

  -- Show T only has interior edges
  have hT_interior : ∀ e ∈ T, e ∉ G.toRotationSystem.boundaryEdges := by
    intro e heT
    have : e ∈ interior_edges := hT_sub heT
    simpa [interior_edges] using this

  -- Maximality: inserting any interior edge must break acyclicity
  have hT_max : ∀ e, e ∉ G.toRotationSystem.boundaryEdges →
      e ∉ T → ¬ isAcyclic G (insert e T) := by
    intro e he_int he_notinT hInsAcyclic
    -- First, (insert e T) is still a subset of interior edges
    have hIns_sub : insert e T ⊆ interior_edges := by
      apply Finset.insert_subset
      · simpa [interior_edges] using he_int
      · exact hT_sub
    -- hence it is a candidate with strictly larger cardinality
    have hIns_mem : insert e T ∈ candidates := by
      simp [candidates, hIns_sub, hInsAcyclic]
    -- The cardinality of (insert e T) is in the image
    have hIns_card_mem : (insert e T).card ∈ candidates.image Finset.card := by
      exact Finset.mem_image_of_mem _ hIns_mem
    -- But (insert e T).card > T.card
    have h_gt : (insert e T).card = T.card + 1 := by
      exact Finset.card_insert_of_notMem he_notinT
    -- And T.card = max_card, so (insert e T).card > max_card
    rw [hT_card] at h_gt
    have h_gt' : (insert e T).card > max_card := by omega
    -- This contradicts max' being the maximum
    have h_le : (insert e T).card ≤ max_card := by
      exact Finset.le_max' _ _ hIns_card_mem
    omega

  -- Done
  refine ⟨T, hT_interior, ⟨hT_acyclic, hT_max⟩⟩

/-- The dichotomy property holds for maximal acyclic sets.

For any interior edge e:
- Either e is in tree_edges (was added during greedy construction)
- Or adding e creates a cycle (blocked during construction)
  which means its endpoints are already connected via tree_edges
-/


lemma maximal_acyclic_dichotomy (G : DiskGeometry V E)
    (tree_edges : Finset E)
    (_ : ∀ e ∈ tree_edges, e ∉ G.toRotationSystem.boundaryEdges)
    (h_maximal : isMaximalAcyclic G tree_edges) :
    ∀ e, e ∉ G.toRotationSystem.boundaryEdges →
      e ∈ tree_edges ∨
      (∃ f g, dualAdjacent G f g ∧ e ∈ f ∧ e ∈ g ∧
        ReflTransGen (fun f' g' => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f' ∧ e' ∈ g') f g) := by
  classical
  intro e he_int
  by_cases h_in : e ∈ tree_edges
  · -- Case 1: e is already in the tree
    exact Or.inl h_in
  · -- Case 2: e is not in the tree
    -- By maximality, inserting e breaks acyclicity
    have h_notA : ¬ isAcyclic G (insert e tree_edges) := h_maximal.2 e he_int h_in

    -- Apply fundamental cycle lemma to extract the path
    obtain ⟨f, g, hf, hg, hfg_ne, he_f, he_g, h_path⟩ :=
      fundamental_cycle_property G tree_edges h_maximal.1 he_int h_in h_notA

    -- Build dualAdjacent witness and return Or.inr
    have h_dual : dualAdjacent G f g := ⟨hf, hg, hfg_ne, ⟨e, he_int, he_f, he_g⟩⟩
    exact Or.inr ⟨f, g, h_dual, he_f, he_g, h_path⟩

theorem exists_spanning_forest (G : DiskGeometry V E) :
    ∃ _ : SpanningForest G, True := by
  -- Get maximal acyclic set from finiteness
  obtain ⟨tree_edges, h_interior, h_maximal⟩ := exists_maximal_acyclic G

  -- Construct SpanningForest structure
  exact ⟨{
    tree_edges := tree_edges
    tree_edges_interior := h_interior
    dichotomy := maximal_acyclic_dichotomy G tree_edges h_interior h_maximal
  }, trivial⟩

/-! ## Cleanup: Archive Old DualForest.lean

The old 3978-line DualForest.lean should be moved to archive/:
```bash
mkdir -p archive
git mv FourColor/Geometry/DualForest.lean archive/DualForest_old.lean
```

This minimal 100-line proof is:
- ✅ Uses only existing API (dualAdjacent, NoDigons, ReflTransGen)
- ✅ No mathlib version mismatches
- ✅ Clear proof strategy (greedy maximal acyclic)
- ✅ Only 2 sorries (both with detailed proof sketches)

The 2 sorries are straightforward finiteness arguments that can be filled later.
-/

end FourColor.Geometry