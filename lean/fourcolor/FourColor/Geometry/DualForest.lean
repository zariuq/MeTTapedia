-- FourColor/Geometry/DualForest.lean
-- Proof of spanning forest existence for planar dual graphs
--
-- This proves Lemma 4.7 from Goertzel's roadmap:
-- "Connected planar dual of annulus A has spanning forest F"
--
-- Strategy:
-- 1. Define dualGraph as a SimpleGraph over internal faces
-- 2. Use Mathlib's Connected.exists_isTree_le for connected case
-- 3. Map the tree structure to SpanningForest
-- 4. This removes the sorry from Disk.lean:782

import FourColor.Geometry.Disk
import FourColor.Geometry.PlanarityHelpers
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

namespace FourColor.Geometry.DualForest

open Mathlib.SimpleGraph FourColor.Geometry

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Step 1: Define the Dual Graph as a SimpleGraph

The dual graph has internal faces as vertices, and edges connect
adjacent faces (those sharing an interior edge).
-/

/-- The dual graph of a disk geometry.

    **Vertices**: Internal faces (as subtype `{f // f ∈ internalFaces}`)
    **Edges**: Pairs of faces sharing an interior edge

    Using subtype ensures all vertices are actual rotation system faces,
    eliminating circularity in proofs. -/
def dualGraph (G : DiskGeometry V E) : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces} where
  Adj f g := DiskGeometry.adj G f.val g.val
  symm := by
    intro f g ⟨e, he_not_bdry, he_f, he_g, hunique⟩
    exact ⟨e, he_not_bdry, he_g, he_f, fun e' ⟨he'_not_bdry, he'_g, he'_f⟩ =>
      hunique e' ⟨he'_not_bdry, he'_f, he'_g⟩⟩
  loopless := by
    intro f ⟨e, he_int, he_f, he_f', hunique⟩
    -- Contradiction: hunique says e is the ONLY interior edge shared by f and f
    -- But also, any other interior edge e' in f is "shared" with f (since f = f)
    -- So if f has 2+ interior edges, we contradict uniqueness
    -- This is a bit subtle - let me use E2 directly:

    -- By E2, e belongs to exactly 2 DISTINCT faces
    obtain ⟨f1, f2, _, _, hf1_f2_ne, he_f1, he_f2, h_unique⟩ :=
      PlanarityHelpers.interior_edge_two_internal_faces G.toRotationSystem e he_int

    -- f.val contains e, so f.val = f1 or f.val = f2
    have : f.val = f1 ∨ f.val = f2 := h_unique f.val f.property he_f

    -- The two "endpoints" of adj f f are both f.val
    -- But E2 says there must be TWO distinct faces
    -- Since f.val = f.val, we violate distinctness
    cases this with
    | inl h => exact hf1_f2_ne (h.symm ▸ h.symm)  -- f1 = f.val = f.val = f2
    | inr h => exact hf1_f2_ne (h.symm ▸ h.symm)

/-! ## Step 2: Connected Dual Has Spanning Tree

Use Mathlib's theorem: every connected finite graph has a spanning tree.
-/

/-- If the dual graph is connected, it has a spanning tree. -/
lemma connected_dual_has_spanning_tree (G : DiskGeometry V E)
    (h_conn : (dualGraph G).Connected) :
    ∃ (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces}),
      T ≤ dualGraph G ∧ T.IsTree := by
  -- Use Mathlib's Connected.exists_isTree_le
  haveI : Finite {f // f ∈ G.toRotationSystem.internalFaces} := inferInstance
  exact h_conn.exists_isTree_le

/-! ## Step 3: Extract Tree Edges from Spanning Tree

A tree edge in the dual corresponds to a primal edge shared by two faces.
We extract these to build the SpanningForest structure.
-/

/-- Extract the set of primal edges corresponding to a dual tree.

    For each tree edge (f,g) in the dual, there's a unique interior edge e
    shared by faces f and g. These are our tree edges. -/
def treeEdgesOfDualTree (G : DiskGeometry V E)
    (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces})
    (hT_sub : T ≤ dualGraph G) :
    Finset E := by
  classical
  exact Finset.univ.filter (fun e =>
    ∃ (f g : {f // f ∈ G.toRotationSystem.internalFaces}),
      T.Adj f g ∧
      e ∈ f.val ∧ e ∈ g.val ∧
      e ∉ G.toRotationSystem.boundaryEdges)

/-- Tree edges are interior (not on boundary). -/
lemma treeEdges_interior (G : DiskGeometry V E)
    (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces})
    (hT_sub : T ≤ dualGraph G) :
    ∀ e ∈ treeEdgesOfDualTree G T hT_sub,
      e ∉ G.toRotationSystem.boundaryEdges := by
  intro e he
  -- Extract from definition of treeEdgesOfDualTree
  unfold treeEdgesOfDualTree at he
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨_, _, _, _, _, he_not_bdry⟩ := he
  exact he_not_bdry

/-! ## Step 4: Spanning Tree ↦ Spanning Forest

Map the SimpleGraph tree structure to our SpanningForest record.
-/

/-- Convert a dual spanning tree to a SpanningForest structure.

    The key insight: A spanning tree T in the dual graph induces a forest structure
    on primal edges where:
    - tree_edges = edges corresponding to dual tree edges
    - dichotomy: any non-tree edge e connects faces already connected via tree edges
      (this is the "creates a cycle" property) -/
def spanningTreeToForest (G : DiskGeometry V E)
    (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces})
    (hT_sub : T ≤ dualGraph G)
    (hT_tree : T.IsTree) :
    SpanningForest G where
  tree_edges := treeEdgesOfDualTree G T hT_sub
  tree_edges_interior := treeEdges_interior G T hT_sub
  dichotomy := by
    intro e he_int
    classical
    -- Case split: is e in tree_edges?
    by_cases he_tree : e ∈ treeEdgesOfDualTree G T hT_sub
    · -- e is a tree edge
      left
      exact he_tree
    · -- e is not a tree edge
      right
      -- Since e is interior, it connects two faces f and g
      obtain ⟨f, g, hf_int, hg_int, hfg_ne, he_f, he_g⟩ :=
        interior_edge_has_two_faces G e he_int

      use f, g
      constructor
      · -- Show dualAdjacent G f g
        unfold dualAdjacent
        exact ⟨hf_int, hg_int, hfg_ne, e, he_int, he_f, he_g⟩
      constructor
      · exact he_f
      constructor
      · exact he_g

      -- Key: f and g are connected in T (spanning tree property)
      -- Wrap f and g as subtype vertices
      let f_sub : {x // x ∈ G.toRotationSystem.internalFaces} := ⟨f, hf_int⟩
      let g_sub : {x // x ∈ G.toRotationSystem.internalFaces} := ⟨g, hg_int⟩

      -- Since T is spanning, f and g are reachable
      have hT_conn : T.Connected := hT_tree.connected
      have h_reach : T.Reachable f_sub g_sub := hT_conn f_sub.property g_sub.property

      -- Extract Walk from Reachable
      obtain ⟨walk⟩ := h_reach

      -- Map Walk to ReflTransGen
      -- The key insight: e ∉ tree_edges, so the walk never uses e
      exact walk_to_reflTransGen G T hT_sub walk e he_tree

/-! ## Step 4.5: Bite-Sized Lemmas for Disconnected Case

These lemmas build up the spanning forest construction incrementally:
1. Components are nonempty internal faces
2. Each component has a spanning tree
3. Tree edges are interior
4. Union satisfies dichotomy
5. Forest is acyclic

Following Grok's guide for manageable, provable steps.
-/

/-- **L4.7.1**: Connected components are nonempty subsets of internal faces.

    This is the foundation: each component gives us a set of faces to build a tree on. -/
lemma components_nonempty_internal (G : DiskGeometry V E)
    (comp : (dualGraph G).ConnectedComponent) :
    ∃ (f : {x // x ∈ G.toRotationSystem.internalFaces}),
      (dualGraph G).connectedComponentMk f = comp := by
  -- Every component is nonempty (has at least one vertex)
  -- Since our vertex type is {f // f ∈ internalFaces}, every vertex is internal
  classical
  -- Get any vertex in the component using Quotient.exists_rep
  obtain ⟨f⟩ := comp.exists_rep
  exact ⟨f, rfl⟩

/-- **L4.7.2**: Each component admits a spanning tree.

    Uses Mathlib's spanning tree existence for connected induced subgraphs. -/
lemma spanning_tree_per_component (G : DiskGeometry V E)
    (comp : (dualGraph G).ConnectedComponent) :
    ∃ (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces}),
      T ≤ dualGraph G ∧
      (∀ v w : {f // f ∈ G.toRotationSystem.internalFaces},
        (dualGraph G).connectedComponentMk v = comp →
        (dualGraph G).connectedComponentMk w = comp →
        T.Reachable v w) ∧
      T.IsAcyclic := by
  classical

  sorry  -- TODO[40-60 lines]: Construct spanning tree for this component
  --
  -- Implementation strategy:
  --
  -- 1. Define induced subgraph on component vertices:
  --    let comp_verts := {v | connectedComponentMk v = comp}
  --    let induced := (dualGraph G).induce comp_verts
  --
  -- 2. Prove induced is preconnected:
  --    - For v, w in comp_verts: connectedComponentMk v = comp = connectedComponentMk w
  --    - So v and w are reachable in dualGraph (by ConnectedComponent.exact)
  --    - Lift to induced using Walk.transfer or induce_mono
  --    - Key lemma: SimpleGraph.Reachable.map or Walk.ofList preservation
  --
  -- 3. Apply Mathlib's spanning tree theorem:
  --    have h_preconn : induced.Preconnected := ...  (from step 2)
  --    haveI : Finite induced.VertexSet := inferInstance
  --    obtain ⟨T_induced, hT_sub, hT_tree⟩ := h_preconn.exists_isTree_le
  --
  -- 4. Lift tree back to full graph:
  --    Define T : SimpleGraph {...} where
  --      Adj v w := v ∈ comp_verts ∧ w ∈ comp_verts ∧ T_induced.Adj ⟨v, ...⟩ ⟨w, ...⟩
  --
  -- 5. Prove T ≤ dualGraph G:
  --    From T_induced ≤ induced and induced ≤ dualGraph by induce definition
  --
  -- 6. Prove reachability property:
  --    If connectedComponentMk v = comp and connectedComponentMk w = comp, then
  --    T_induced.Reachable ⟨v, ...⟩ ⟨w, ...⟩ (from spanning property)
  --    Lift to T.Reachable v w
  --
  -- 7. Prove acyclicity:
  --    From T_induced.IsAcyclic (part of IsTree)
  --    Cycles in T would induce cycles in T_induced (lift Walk)
  --
  -- Mathlib deps:
  -- - SimpleGraph.induce, SimpleGraph.Preconnected.exists_isTree_le
  -- - Walk.transfer, ConnectedComponent.exact
  -- - SimpleGraph.IsTree (combines acyclic + connected)

/-- **L4.7.3**: Extract primal edge from dual adjacency.

    By definition of dualGraph, adjacent faces share exactly one interior edge.
    This function extracts that unique edge. -/
def thePrimalEdge (G : DiskGeometry V E)
    (f g : {x // x ∈ G.toRotationSystem.internalFaces})
    (h_adj : (dualGraph G).Adj f g) : E :=
  -- By definition of dualGraph.Adj, there exists a unique interior edge
  Classical.choose h_adj

lemma thePrimalEdge_spec (G : DiskGeometry V E)
    (f g : {x // x ∈ G.toRotationSystem.internalFaces})
    (h_adj : (dualGraph G).Adj f g) :
    let e := thePrimalEdge G f g h_adj
    e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f.val ∧ e ∈ g.val := by
  unfold thePrimalEdge
  obtain ⟨he_int, he_f, he_g, _⟩ := Classical.choose_spec h_adj
  exact ⟨he_int, he_f, he_g⟩

/-- **L4.7.4**: This is just treeEdgesOfDualTree with a different name.

    We reuse the existing definition for consistency. -/
abbrev treeEdgesOfComponent := @treeEdgesOfDualTree

/-- **L4.7.5**: Tree edges from components are interior (not boundary edges).

    This is just treeEdges_interior under the alias. -/
abbrev treeEdgesOfComponent_interior := @treeEdges_interior

/-! ## Step 4.6: Convert Acyclic Spanning Graph to SpanningForest

Helper for disconnected case: build SpanningForest from an acyclic spanning subgraph.
-/

/-- Build a SpanningForest from an acyclic spanning subgraph.

    This is used for the disconnected case, where we have a forest (union of trees)
    rather than a single connected tree. -/
def spanningForestFromAcyclicSpanning (G : DiskGeometry V E)
    (F : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces})
    (hF_sub : F ≤ dualGraph G)
    (hF_acyclic : F.IsAcyclic)
    (hF_spanning : ∀ v w : {f // f ∈ G.toRotationSystem.internalFaces},
      (dualGraph G).Reachable v w → F.Reachable v w) :
    SpanningForest G where
  tree_edges := treeEdgesOfDualTree G F hF_sub
  tree_edges_interior := treeEdges_interior G F hF_sub
  dichotomy := by
    intro e he_int
    classical
    by_cases he_tree : e ∈ treeEdgesOfDualTree G F hF_sub
    · left; exact he_tree
    · right
      obtain ⟨f, g, hf_int, hg_int, hfg_ne, he_f, he_g⟩ :=
        interior_edge_has_two_faces G e he_int
      use f, g
      constructor
      · unfold dualAdjacent
        exact ⟨hf_int, hg_int, hfg_ne, e, he_int, he_f, he_g⟩
      constructor
      · exact he_f
      constructor
      · exact he_g

      -- Key: f and g are adjacent in dualGraph (share edge e)
      -- So they're reachable in dualGraph
      let f_sub : {x // x ∈ G.toRotationSystem.internalFaces} := ⟨f, hf_int⟩
      let g_sub : {x // x ∈ G.toRotationSystem.internalFaces} := ⟨g, hg_int⟩

      have h_dual_adj : (dualGraph G).Adj f_sub g_sub := by
        unfold dualGraph
        simp only
        use e, he_int, he_f, he_g
        intro e' ⟨he'_int, he'_f, he'_g⟩
        -- Uniqueness from E2 property
        sorry  -- Prove e is unique interior edge shared by f and g

      have h_reach : (dualGraph G).Reachable f_sub g_sub :=
        SimpleGraph.Adj.reachable h_dual_adj

      -- By spanning property, f and g are connected in F
      have h_F_reach : F.Reachable f_sub g_sub := hF_spanning f_sub g_sub h_reach
      obtain ⟨walk⟩ := h_F_reach

      -- Map walk to ReflTransGen
      exact walk_to_reflTransGen G F hF_sub walk e he_tree

/-! ## Step 5: Main Theorem - Spanning Forest Exists

This is Lemma 4.7, and it removes the sorry from Disk.lean:782.
-/

/-- **Lemma 4.7**: Every disk geometry has a spanning forest.

    **Proof Strategy**:
    - If dual is connected: Use Mathlib's spanning tree theorem
    - If disconnected: Build forest as union of trees per component
    - Map tree structure to SpanningForest record -/
theorem exists_spanning_forest (G : DiskGeometry V E)
    (hNoDigons : NoDigons G) :
    Nonempty (SpanningForest G) := by
  classical
  -- For now, we can use the fact that if the dual is disconnected,
  -- we can still build a forest by taking a maximal acyclic subgraph.
  -- This is simpler than enumerating components.

  -- Alternative approach: Use the connected case with a trivial tree for empty graph
  -- Or: Prove that any finite graph has a spanning forest (disjoint union of spanning trees)

  -- Simplified construction: Take any maximal tree-like subgraph
  -- For the Four Color Theorem, we typically work with connected planar graphs,
  -- so this case is often vacuous.

  -- Temporary: Use connected case as primary, handle disconnected via component union
  by_cases h_conn : (dualGraph G).Connected
  · -- Case 1: Connected dual (main case for 4CT)
    obtain ⟨T, hT_sub, hT_tree⟩ := connected_dual_has_spanning_tree G h_conn
    exact ⟨spanningTreeToForest G T hT_sub hT_tree⟩
  · -- Case 2: Disconnected dual
    -- Build spanning forest as union of per-component spanning trees
    -- Following Grok's direct union approach

    haveI : Fintype {f // f ∈ G.toRotationSystem.internalFaces} := inferInstance
    haveI : DecidableEq {f // f ∈ G.toRotationSystem.internalFaces} := inferInstance
    classical

    -- Direct construction: Define tree_edges as union over all components
    let unionTreeEdges : Finset E := by
      classical
      -- For each connected component, get its spanning tree edges
      -- Union all these edge sets
      exact Finset.univ.biUnion fun (v : {f // f ∈ G.toRotationSystem.internalFaces}) =>
        -- Get spanning tree for v's component
        let comp := (dualGraph G).connectedComponentMk v
        -- Use spanning_tree_per_component to get tree for this component
        let tree_spec := spanning_tree_per_component G comp
        treeEdgesOfComponent G tree_spec.choose tree_spec.choose_spec.1

    -- Build SpanningForest directly from the union
    exact ⟨{
      tree_edges := unionTreeEdges
      tree_edges_interior := by
        intro e he
        -- e is in some component's tree edges
        unfold_let unionTreeEdges at he
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
        obtain ⟨v, he_comp⟩ := he
        -- Component tree edges are interior
        let comp := (dualGraph G).connectedComponentMk v
        exact treeEdgesOfComponent_interior G _ _ e he_comp
      dichotomy := by
        intro e he_int
        classical
        by_cases he_tree : e ∈ unionTreeEdges
        · left; exact he_tree
        · right
          -- e connects two faces f, g in same component
          obtain ⟨f, g, hf_int, hg_int, hfg_ne, he_f, he_g⟩ :=
            interior_edge_has_two_faces G e he_int
          use f, g
          constructor
          · unfold dualAdjacent
            exact ⟨hf_int, hg_int, hfg_ne, e, he_int, he_f, he_g⟩
          constructor
          · exact he_f
          constructor
          · exact he_g
          -- f and g are in same component, so connected via that component's tree
          let f_sub : {x // x ∈ G.toRotationSystem.internalFaces} := ⟨f, hf_int⟩
          let g_sub : {x // x ∈ G.toRotationSystem.internalFaces} := ⟨g, hg_int⟩

          -- Show f,g are in the same component (they're adjacent in dualGraph)
          have h_dual_adj : (dualGraph G).Adj f_sub g_sub := by
            unfold dualGraph
            simp only
            use e, he_int, he_f, he_g
            intro e' ⟨he'_int, he'_f, he'_g⟩
            -- Uniqueness: e is the only interior edge shared by f and g
            -- This follows from E2 property
            obtain ⟨f1, f2, hf1_int, hf2_int, hf1_f2_ne, he_f1, he_f2, h_unique⟩ :=
              PlanarityHelpers.interior_edge_two_internal_faces G.toRotationSystem e he_int
            -- f and g both contain e, so they must be f1 and f2 (in some order)
            have hf_is : f = f1 ∨ f = f2 := h_unique f hf_int he_f
            have hg_is : g = f1 ∨ g = f2 := h_unique g hg_int he_g
            -- Similarly for e'
            have he'_f1_f2 : e' ∈ f1 ∧ e' ∈ f2 → e' = e := by
              intro ⟨he'_f1, he'_f2⟩
              -- Both e and e' are interior edges shared by f1 and f2
              -- Use the unique interior edge lemma
              exact faces_share_unique_interior_edge G hNoDigons f1 f2 hf1_int hf2_int hf1_f2_ne e e'
                he_int he'_int he_f1 he_f2 he'_f1 he'_f2
            -- Since e' ∈ f and e' ∈ g, and f,g ⊆ {f1,f2}, we have e' ∈ f1 ∩ f2
            cases hf_is with
            | inl hf_eq =>
              cases hg_is with
              | inl hg_eq =>
                -- f = f1, g = f1, contradicts hfg_ne
                subst hf_eq hg_eq
                exact absurd rfl hfg_ne
              | inr hg_eq =>
                -- f = f1, g = f2, so e' ∈ f1 ∩ f2
                subst hf_eq hg_eq
                exact he'_f1_f2 ⟨he'_f, he'_g⟩
            | inr hf_eq =>
              cases hg_is with
              | inl hg_eq =>
                -- f = f2, g = f1, so e' ∈ f1 ∩ f2
                subst hf_eq hg_eq
                exact he'_f1_f2 ⟨he'_g, he'_f⟩
              | inr hg_eq =>
                -- f = f2, g = f2, contradicts hfg_ne
                subst hf_eq hg_eq
                exact absurd rfl hfg_ne

          have h_same_comp : (dualGraph G).connectedComponentMk f_sub = (dualGraph G).connectedComponentMk g_sub := by
            rw [SimpleGraph.ConnectedComponent.eq]
            exact SimpleGraph.Adj.reachable h_dual_adj

          -- Get the component and its spanning tree
          let comp := (dualGraph G).connectedComponentMk f_sub
          obtain ⟨T, hT_sub, hT_reach, hT_acyclic⟩ := spanning_tree_per_component G comp

          -- f and g are both in this component, so connected via T
          have h_T_reach : T.Reachable f_sub g_sub := by
            apply hT_reach
            · exact rfl
            · exact h_same_comp

          obtain ⟨walk⟩ := h_T_reach

          -- Map the walk to ReflTransGen
          exact walk_to_reflTransGen G T hT_sub walk e he_tree
    }⟩

/-! ## Additional Lemmas (Support Material)

These help prove the sorry's above.
-/

/-- Two distinct internal faces share at most one interior edge.

    **Proof strategy**: Use E2 property - both edges connect the same two faces,
    but E2 says each edge has exactly 2 distinct faces. We need to show that
    if e and e' both are interior edges in faces f and g (with f ≠ g), then
    e = e'.

    The key insight: This follows from the structure of faces in rotation systems.
    Faces are φ-orbit sets, and edges between the same two faces would create
    a contradiction with the orbit structure. -/
lemma faces_share_unique_interior_edge (G : DiskGeometry V E)
    (hNoDigons : NoDigons G)
    (f g : Finset E)
    (hf : f ∈ G.toRotationSystem.internalFaces)
    (hg : g ∈ G.toRotationSystem.internalFaces)
    (hfg : f ≠ g)
    (e e' : E)
    (he_int : e ∉ G.toRotationSystem.boundaryEdges)
    (he'_int : e' ∉ G.toRotationSystem.boundaryEdges)
    (he_f : e ∈ f) (he_g : e ∈ g)
    (he'_f : e' ∈ f) (he'_g : e' ∈ g) :
    e = e' :=
  -- This is EXACTLY the NoDigons property!
  -- NoDigons says: two distinct faces cannot share two different interior edges
  hNoDigons hf hg hfg he_int he'_int he_f he_g he'_f he'_g

/-- Version with full E2 derivation (showing the structure, even though we use the axiom).

    This shows WHY the axiom should be provable. -/
lemma faces_share_unique_interior_edge_via_E2 (G : DiskGeometry V E)
    (f g : Finset E)
    (hf : f ∈ G.toRotationSystem.internalFaces)
    (hg : g ∈ G.toRotationSystem.internalFaces)
    (hfg : f ≠ g)
    (e e' : E)
    (he_int : e ∉ G.toRotationSystem.boundaryEdges)
    (he'_int : e' ∉ G.toRotationSystem.boundaryEdges)
    (he_f : e ∈ f) (he_g : e ∈ g)
    (he'_f : e' ∈ f) (he'_g : e' ∈ g) :
    e = e' := by
  -- Both e and e' are interior edges shared by f and g
  -- By E2, each interior edge is in exactly 2 distinct internal faces
  obtain ⟨f1, f2, _, _, hf1_f2, he_f1, he_f2, h_uniq_e⟩ :=
    PlanarityHelpers.interior_edge_two_internal_faces G.toRotationSystem e he_int
  obtain ⟨f1', f2', _, _, hf1'_f2', he'_f1', he'_f2', h_uniq_e'⟩ :=
    PlanarityHelpers.interior_edge_two_internal_faces G.toRotationSystem e' he'_int

  -- f and g are the two faces containing e
  have hf_in : f = f1 ∨ f = f2 := h_uniq_e f hf he_f
  have hg_in : g = f1 ∨ g = f2 := h_uniq_e g hg he_g

  -- f and g are also the two faces containing e'
  have hf_in' : f = f1' ∨ f = f2' := h_uniq_e' f hf he'_f
  have hg_in' : g = f1' ∨ g = f2' := h_uniq_e' g hg he'_g

  -- Since f ≠ g, we have {f, g} = {f1, f2} = {f1', f2'}
  -- Case analysis on which equals which
  cases hf_in with
  | inl hf_eq =>
    -- f = f1
    cases hg_in with
    | inl hg_eq =>
      -- g = f1, but f = f1 and f ≠ g, contradiction
      subst hf_eq hg_eq
      exact absurd rfl hfg
    | inr hg_eq =>
      -- f = f1, g = f2
      -- So e connects f1 and f2
      subst hf_eq hg_eq
      -- Now show e' also connects f1 and f2
      cases hf_in' with
      | inl hf_eq' =>
        -- f = f1'
        cases hg_in' with
        | inl hg_eq' =>
          -- g = f1', contradiction
          subst hf_eq' hg_eq'
          exact absurd rfl hfg
        | inr hg_eq' =>
          -- f = f1', g = f2'
          -- So both e and e' connect f1' and f2'
          subst hf_eq' hg_eq'
          -- Both e and e' are interior edges connecting f1' and f2'
          -- If we can show DiskGeometry.adj G f1' f2' holds,
          -- then by the uniqueness in adj's definition, e = e'

          -- Build adj from e's witness
          have h_adj_e : DiskGeometry.adj G f1' f2' := ⟨e, he_int, he_f1, he_f2, fun e'' ⟨he''_int, he''_f1', he''_f2'⟩ =>
            faces_share_unique_interior_edge G hNoDigons f1' f2' hf1'_int hf2'_int hf1'_f2'_ne e e'' he_int he''_int he_f1 he_f2 he''_f1' he''_f2'⟩

          -- Extract the unique edge from adj
          obtain ⟨e_uniq, he_uniq_int, he_uniq_f1', he_uniq_f2', h_uniq⟩ := h_adj_e

          -- Show e = e_uniq
          have he_eq : e = e_uniq := h_uniq e ⟨he_int, he_f1, he_f2⟩

          -- Show e' = e_uniq
          have he'_eq : e' = e_uniq := h_uniq e' ⟨he'_int, he'_f1', he'_f2'⟩

          -- Therefore e = e'
          rw [he_eq, he'_eq]
      | inr hf_eq' =>
        -- f = f2'
        cases hg_in' with
        | inl hg_eq' =>
          -- f = f2', g = f1'
          -- So {f1, f2} = {f2', f1'} = {f1', f2'}
          subst hf_eq' hg_eq'
          sorry  -- Same as above, use adj uniqueness
        | inr hg_eq' =>
          -- f = f2', g = f2', contradiction
          subst hf_eq' hg_eq'
          exact absurd rfl hfg
  | inr hf_eq =>
    -- f = f2
    cases hg_in with
    | inl hg_eq =>
      -- f = f2, g = f1, so e connects f2 and f1
      subst hf_eq hg_eq
      cases hf_in' with
      | inl hf_eq' =>
        cases hg_in' with
        | inl hg_eq' =>
          subst hf_eq' hg_eq'
          exact absurd rfl hfg
        | inr hg_eq' =>
          -- f = f1', g = f2', so {f2, f1} = {f1', f2'}
          subst hf_eq' hg_eq'
          sorry  -- Use adj uniqueness
      | inr hf_eq' =>
        cases hg_in' with
        | inl hg_eq' =>
          -- f = f2', g = f1', so {f2, f1} = {f2', f1'}
          subst hf_eq' hg_eq'
          sorry  -- Use adj uniqueness
        | inr hg_eq' =>
          subst hf_eq' hg_eq'
          exact absurd rfl hfg
    | inr hg_eq =>
      -- f = f2, g = f2, contradiction
      subst hf_eq hg_eq
      exact absurd rfl hfg

/-- Every interior edge connects exactly two internal faces (E2 property). -/
lemma interior_edge_has_two_faces (G : DiskGeometry V E) (e : E)
    (he_int : e ∉ G.toRotationSystem.boundaryEdges) :
    ∃ f g,
      f ∈ G.toRotationSystem.internalFaces ∧
      g ∈ G.toRotationSystem.internalFaces ∧
      f ≠ g ∧
      e ∈ f ∧ e ∈ g := by
  -- This is the E2 property from RotationSystem
  obtain ⟨faces, ⟨hcard, hfaces⟩, hunique⟩ :=
    G.toRotationSystem.two_internal_faces_of_interior_edge he_int
  -- faces has exactly 2 elements
  have h2 : faces.card = 2 := hcard
  -- Extract the two faces
  obtain ⟨f, hf_mem, g, hg_mem, hfg_ne, hfg_all⟩ :=
    Finset.card_eq_two.mp h2
  use f, g
  constructor
  · exact (hfaces f hf_mem).1
  constructor
  · exact (hfaces g hg_mem).1
  constructor
  · exact hfg_ne
  constructor
  · exact (hfaces f hf_mem).2
  · exact (hfaces g hg_mem).2

/-- NoDigons property needed for loopless dual graph. -/
lemma adj_not_reflexive (G : DiskGeometry V E)
    (hNoDigons : NoDigons G) (f : Finset E) :
    ¬(dualGraph G).Adj f f := by
  intro ⟨e, _, _, _, _⟩
  -- A face cannot be adjacent to itself
  -- (would require sharing an edge with itself)
  sorry

/-- Map a Walk in the dual tree to a ReflTransGen path.

    **Key**: With subtype vertices, T ≤ dualGraph means T is also over subtype vertices,
    so all walk vertices are internal faces by construction! -/
lemma walk_to_reflTransGen (G : DiskGeometry V E)
    (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces})
    (hT_sub : T ≤ dualGraph G)
    {f g : {f // f ∈ G.toRotationSystem.internalFaces}}
    (walk : T.Walk f g)
    (e_excluded : E)
    (he_not_tree : e_excluded ∉ treeEdgesOfDualTree G T hT_sub) :
    ReflTransGen (fun f' g' => ∃ e' ∈ treeEdgesOfDualTree G T hT_sub,
      e' ≠ e_excluded ∧ e' ∈ f'.val ∧ e' ∈ g'.val) f g := by
  -- Induction on walk - no need to carry face membership proofs (they're in the type!)
  induction walk with
  | nil =>
    -- Base case: f = g, use reflexivity
    exact ReflTransGen.refl
  | cons h_adj walk_tail ih =>
    -- Inductive case: f --edge--> v --walk_tail--> g
    -- h_adj : T.Adj f v (adjacency in tree)
    -- walk_tail : T.Walk v g
    -- ih : ReflTransGen for walk_tail (v to g)

    -- Get the tree edge between f and v
    have h_dual_adj : (dualGraph G).Adj f v := hT_sub h_adj
    obtain ⟨e_tree, he_not_bdry, he_f, he_v, he_unique⟩ := h_dual_adj

    -- v is internal by construction (it's a subtype vertex!)
    -- No proof needed - v.property : v.val ∈ internalFaces

    -- Show e_tree is in treeEdgesOfDualTree
    have he_tree_mem : e_tree ∈ treeEdgesOfDualTree G T hT_sub := by
      unfold treeEdgesOfDualTree
      classical
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      -- We need: ∃ f' g', f' ∈ internalFaces ∧ g' ∈ internalFaces ∧
      --          T.Adj f' g' ∧ e_tree ∈ f' ∧ e_tree ∈ g' ∧ e_tree ∉ boundaryEdges

      -- f and v are subtype vertices - use their values and properties
      use f.val, v.val
      exact ⟨f.property, v.property, h_adj, he_f, he_v, he_not_bdry⟩

    -- Build the path: f --e_tree--> v --ih--> g
    apply ReflTransGen.head
    · -- Show the relation holds for f → v
      use e_tree, he_tree_mem
      constructor
      · -- Show e_tree ≠ e_excluded
        intro h_eq
        subst h_eq
        exact he_not_tree he_tree_mem
      constructor
      · exact he_f
      · exact he_v
    · -- Use IH for rest of path (v to g) - no membership proofs needed!
      exact ih

/-- Tree edges preserve face connectivity. -/
lemma tree_edges_connect_faces (G : DiskGeometry V E)
    (T : SimpleGraph (Finset E))
    (hT_sub : T ≤ dualGraph G)
    (hT_tree : T.IsTree)
    (f g : Finset E) :
    T.Reachable f g →
    ∃ (path : List E), sorry := by  -- Path connects f to g via tree edges
  sorry

end FourColor.Geometry.DualForest
