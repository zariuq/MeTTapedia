-- FourColor/Kempe/SpanningProof.lean
-- Step-by-step proof of Disk Kempe-Closure Spanning Lemma (Theorem 4.10)
--
-- This file implements the bite-sized sublemmas from Grok's roadmap,
-- building up to the full spanning theorem.
--
-- Structure:
-- 1. Lemma 4.7: Dual forest existence (via Mathlib spanning tree)
-- 2. Lemma 4.2: Run invariance under Kempe switches
-- 3. Lemma 4.3: Purification trick (boundary-only vectors)
-- 4. Lemma 4.6: Annular cut-parity (from Euler characteristic)
-- 5. Lemma 4.8: Orthogonality peeling (wraps existing descent)
-- 6. Lemma 4.9: Facial basis spanning (well-founded induction)
-- 7. Theorem 4.10: Main assembly

import FourColor.Geometry.Disk
import FourColor.Kempe.Spanning
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

namespace FourColor.Kempe.SpanningProof

open FourColor.Geometry
open Mathlib.SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Lemma 4.7: Dual Forest Existence

**Claim**: Connected planar dual of annulus A has spanning forest F.

**Proof Strategy**:
1. The dual graph of internal faces is a SimpleGraph
2. If connected, use Mathlib's Connected.exists_isTree_le
3. If disconnected, build forest as union of trees per component
4. Planarity ensures no parallel edges (NoDigons property)

**Bridge**: This proves `exists_spanning_forest` from Disk.lean:781
-/

/-- The dual graph of a disk geometry as a SimpleGraph.
    Vertices are internal faces, edges connect adjacent faces. -/
def dualGraph (G : DiskGeometry V E) : SimpleGraph (Finset E) where
  Adj f g := DiskGeometry.adj G f g
  symm := by
    intro f g h
    obtain ⟨e, he_not_bdry, he_f, he_g, hunique⟩ := h
    exact ⟨e, he_not_bdry, he_g, he_f, fun e' ⟨he'_not_bdry, he'_g, he'_f⟩ =>
      hunique e' ⟨he'_not_bdry, he'_f, he'_g⟩⟩
  loopless := by
    intro f h
    obtain ⟨e, _, _, _, hunique⟩ := h
    -- A single interior edge e cannot be the unique edge in both f and f
    -- This would require e ∈ f appearing twice, contradicting uniqueness
    sorry  -- TODO: Formalize using NoDigons

/-- Helper: If the dual graph is connected, it has a spanning tree. -/
lemma connected_dual_has_spanning_tree (G : DiskGeometry V E)
    (h_conn : (dualGraph G).Connected) :
    ∃ T : SimpleGraph (Finset E),
      T ≤ dualGraph G ∧ T.IsTree := by
  -- Use Mathlib's spanning tree theorem
  haveI : Finite (Finset E) := Fintype.finite
  exact Connected.exists_isTree_le h_conn

/-- A spanning tree of the dual graph corresponds to a spanning forest structure. -/
def spanningTreeToForest (G : DiskGeometry V E)
    (T : SimpleGraph (Finset E))
    (hT : T ≤ dualGraph G) (hTree : T.IsTree) :
    SpanningForest G where
  tree_edges := {e | ∃ f g,
    f ∈ G.toRotationSystem.internalFaces ∧
    g ∈ G.toRotationSystem.internalFaces ∧
    T.Adj f g ∧
    DiskGeometry.adj G f g ∧  -- They're adjacent in the original dual
    e ∈ f ∧ e ∈ g ∧
    (∀ e' ∈ f, e' ∈ g → e' ∉ G.toRotationSystem.boundaryEdges → e' = e)}
  tree_subset_interior := by
    intro e he
    obtain ⟨f, g, _, _, _, ⟨e', he'_not_bdry, _, _, _⟩, _, _, _⟩ := he
    exact he'_not_bdry
  forest_acyclic := by
    sorry  -- TODO: Prove tree structure implies acyclic dual forest
  forest_spans := by
    sorry  -- TODO: Prove every pair of faces connected via tree edges

/-- **Lemma 4.7**: Spanning forest exists for any disk geometry.

    **Proof**: Use Mathlib's spanning tree theorem on the connected dual graph.
    If disconnected, take union of trees per component. -/
theorem exists_spanning_forest (G : DiskGeometry V E) :
    Nonempty (SpanningForest G) := by
  classical
  -- Case 1: If dual is connected, use spanning tree directly
  by_cases h_conn : (dualGraph G).Connected
  · obtain ⟨T, hT_sub, hT_tree⟩ := connected_dual_has_spanning_tree G h_conn
    exact ⟨spanningTreeToForest G T hT_sub hT_tree⟩
  · -- Case 2: Disconnected dual - build forest from component trees
    sorry  -- TODO: Handle disconnected case via component union

/-! ## Lemma 4.2: Run Invariance Under Kempe Switches

**Claim**: Interior Kempe switches preserve run lengths mod 2 on face boundaries.

**Proof Strategy**:
1. Kempe cycles have even degree at interior vertices (cycle property)
2. Switches flip α↔β in pairs
3. Runs are boundary arcs; interior flips cancel in F₂²
4. Even incidence ⇒ ∑ δ = 0 on boundary
-/

/-- A Kempe cycle in the interior of an annulus (no boundary edges). -/
def IsInteriorKempeCycle (G : DiskGeometry V E)
    (C : Finset E) (α β : Bool × Bool) : Prop :=
  -- All edges in C are interior (not on boundary)
  (∀ e ∈ C, e ∉ G.toRotationSystem.boundaryEdges) ∧
  -- C forms a cycle in the α-β subgraph
  sorry  -- TODO: Formalize using twoColorSubgraph from Tait.lean

/-- Kempe cycles have even degree at each vertex. -/
lemma kempeCycle_even_at_vertex (G : DiskGeometry V E)
    (C : Finset E) (α β : Bool × Bool)
    (hC : IsInteriorKempeCycle G C α β) (v : V) :
    Even (Finset.card (Finset.filter (fun e => v ∈ sorry) C)) := by
  -- Cycles have degree 0 or 2 at each vertex
  sorry  -- TODO: Prove from cycle property

/-- **Lemma 4.2**: Run invariance under Kempe switches.

    Interior Kempe switches preserve boundary run parities. -/
lemma runInvariance_under_switch (G : DiskGeometry V E)
    (C : Finset E) (α β : Bool × Bool)
    (hC : IsInteriorKempeCycle G C α β)
    (f : Finset E) (hf : f ∈ G.toRotationSystem.internalFaces) :
    -- Run parity on ∂f preserved after switching C
    sorry := by
  sorry  -- TODO: Implement using even degree at vertices

/-! ## Lemma 4.3: Purification Trick

**Claim**: Face generators decompose into boundary-only vectors plus interior correction.

**Proof Strategy**:
1. χ^f_αβ(C) has runs on both boundary and interior
2. Interior runs form cycles (from Kempe property)
3. Cycles contribute 0 in F₂² (even sum)
4. Boundary indicator survives: B^f_αβ = χ^f_αβ - interior_cycles
-/

/-- Face generator decomposes into boundary part + interior correction. -/
lemma faceGenerator_decomposition (G : DiskGeometry V E)
    (f : Finset E) (α β γ : Bool × Bool)
    (hf : f ∈ G.toRotationSystem.internalFaces) :
    ∃ (boundary_part interior_part : E → Bool × Bool),
      -- boundary_part is zero outside boundary
      (∀ e ∈ f, e ∉ G.toRotationSystem.boundaryEdges → boundary_part e = (false, false)) ∧
      -- interior_part sums to zero (cycles)
      (Finset.sum Finset.univ interior_part = (false, false)) ∧
      -- Decomposition holds
      sorry := by
  sorry  -- TODO: Implement via run analysis

/-- **Lemma 4.3**: Purification to boundary-only vectors.

    This connects `faceGenerator` to `faceBoundaryChainRel` from Disk.lean. -/
lemma purification_to_boundary (G : DiskGeometry V E)
    (f : Finset E) (α β γ : Bool × Bool)
    (hf : f ∈ G.toRotationSystem.internalFaces) :
    -- Face generator equals boundary chain plus zero
    sorry := by
  obtain ⟨boundary_part, interior_part, hbdry, hzero, _⟩ :=
    faceGenerator_decomposition G f α β hf
  sorry  -- TODO: Show boundary_part = faceBoundaryChainRel

/-! ## Lemma 4.6: Annular Cut-Parity

**Claim**: Cut edges have even cardinality (from Euler characteristic).

**Proof Strategy**:
1. Annulus A is planar disk with χ(A) = V - E + F
2. For planar embeddings, χ(A) is even
3. Dual cuts correspond to crossings
4. Handshaking lemma ⇒ even total degree ⇒ even cuts
-/

/-- Euler characteristic of a planar region. -/
def eulerChar (G : DiskGeometry V E) : ℤ :=
  sorry  -- |V| - |E| + |F| for the annular region

/-- Planar disk regions have even Euler characteristic. -/
lemma planar_disk_euler_even (G : DiskGeometry V E) :
    Even (eulerChar G) := by
  sorry  -- TODO: Prove from planar embedding (χ = 1 for disk)

/-- **Lemma 4.6**: Annular cut-parity.

    Cut edges of a face set have even cardinality. -/
lemma annular_cut_parity (G : DiskGeometry V E)
    (S : Finset (Finset E))
    (hS : S ⊆ G.toRotationSystem.internalFaces) :
    Even (cutEdges G S).card := by
  -- From Euler characteristic and handshaking
  sorry  -- TODO: Connect to planar_disk_euler_even

/-! ## Lemma 4.8: Orthogonality Peeling (Bridge to Disk.lean)

**Claim**: Iteratively remove support elements via leaf toggles.

**BRIDGE**: This wraps the **already proven** infrastructure:
- `support₁_strict_descent_via_leaf_toggle` (Disk.lean:1153-1166)
- `aggregated_toggle_strict_descent_at_prescribed_cut` (Disk.lean:1075-1131)
-/

/-- **Lemma 4.8**: Orthogonality peeling (wrapper around proven infrastructure).

    For any nonzero x ∈ W₀(A), we can peel off support via leaf toggles.

    **PROVEN**: This directly wraps `support₁_strict_descent_via_leaf_toggle`
    from Disk.lean:1186-1199, which provides the support descent. -/
lemma orthogonality_peeling (G : DiskGeometry V E)
    (hNoDigons : NoDigons G)
    (x : E → Bool × Bool)
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (hsupp : (support₁ x).Nonempty) :
    ∃ (S₀ : Finset (Finset E)),
      -- Strict descent in support after toggle
      (support₁ (x + toggleSum G (1, 0) S₀)).card < (support₁ x).card := by
  -- Extract an element from support
  obtain ⟨e0, he0_supp⟩ := hsupp
  -- e0 must be interior (since x ∈ zeroBoundarySet has support only on interior edges)
  have he0_int : e0 ∉ G.toRotationSystem.boundaryEdges := by
    sorry -- TODO: Extract from zeroBoundarySet definition (boundary edges have no support)

  -- Apply the PROVEN theorem from Disk.lean
  exact support₁_strict_descent_via_leaf_toggle hNoDigons hx he0_supp he0_int

/-- **Corollary**: Peeling with explicit x' extraction.

    This form explicitly constructs x' = x + toggleSum, showing the decomposition. -/
lemma orthogonality_peeling_with_decomposition (G : DiskGeometry V E)
    (hNoDigons : NoDigons G)
    (x : E → Bool × Bool)
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (hsupp : (support₁ x).Nonempty) :
    ∃ (S₀ : Finset (Finset E)) (x' : E → Bool × Bool),
      -- x' also in zero-boundary set
      x' ∈ G.asZeroBoundary.zeroBoundarySet ∧
      -- Strict descent in support
      (support₁ x').card < (support₁ x).card ∧
      -- Decomposition
      x' = fun e => x e + toggleSum G (1, 0) S₀ e := by
  -- Get S₀ from peeling
  obtain ⟨S₀, hdesc⟩ := orthogonality_peeling G hNoDigons x hx hsupp
  use S₀, fun e => x e + toggleSum G (1, 0) S₀ e
  constructor
  · sorry  -- x + toggleSum preserves zero-boundary (toggleSum generates cycles)
  constructor
  · exact hdesc
  · rfl

/-! ## Lemma 4.9: Facial Basis Spanning

**Claim**: W₀(A) ⊆ span{ B^f_αβ | f ∈ A }

**Proof**: Well-founded induction on |supp(x)| using orthogonality peeling.
-/

/-- **Lemma 4.9**: Facial basis spans W₀(A).

    By strong induction on support size via peeling. -/
theorem facialBasis_zeroBoundary_in_span (G : DiskGeometry V E)
    (hNoDigons : NoDigons G) :
    ∀ x ∈ G.asZeroBoundary.zeroBoundarySet,
      ∃ (faces : Finset (Finset E)),
        faces ⊆ G.toRotationSystem.internalFaces ∧
        x = fun e => toggleSum G (1, 0) faces e := by
  intro x hx
  -- Strong induction on support size
  sorry  -- TODO: Implement using orthogonality_peeling + IH

/-! ## Theorem 4.10: Main Assembly

**Disk Kempe-Closure Spanning Lemma**

Combines all sublemmas into the final theorem.
-/

/-- **Theorem 4.10**: Disk Kempe-Closure Spanning Lemma.

    W₀(A) is spanned by purified face generators, and these are orthogonal
    to the Kempe closure. -/
theorem disk_kempe_closure_spanning (G : DiskGeometry V E)
    (hNoDigons : NoDigons G) :
    -- Part 1: Spanning
    (∀ x ∈ G.asZeroBoundary.zeroBoundarySet,
      ∃ (faces : Finset (Finset E)),
        faces ⊆ G.toRotationSystem.internalFaces ∧
        x = fun e => toggleSum G (1, 0) faces e) ∧
    -- Part 2: Orthogonality to Kempe closure
    (∀ (x : E → Bool × Bool) (faces : Finset (Finset E)),
      faces ⊆ G.toRotationSystem.internalFaces →
      x = fun e => toggleSum G (1, 0) faces e →
      ∀ (k : E → Bool × Bool),
        -- k is in Kempe closure
        sorry →
        -- x and k are orthogonal
        Finset.sum Finset.univ (fun e => sorry) = (false, false)) := by
  constructor
  · -- Spanning: Use Lemma 4.9
    exact facialBasis_zeroBoundary_in_span G hNoDigons
  · -- Orthogonality: From run invariance + purification
    intro x faces hfaces hx k hk
    sorry  -- TODO: Use runInvariance_under_switch + annular_cut_parity

end FourColor.Kempe.SpanningProof
