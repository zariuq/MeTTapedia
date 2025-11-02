-- FourColor/Kempe/SpanningProofCore.lean
-- Core infrastructure for Theorem 4.10 proof
--
-- This file contains ONLY the provable lemmas with minimal dependencies.
-- We build up slowly to avoid compilation issues.

import FourColor.Geometry.Disk

namespace FourColor.Kempe.SpanningProofCore

open FourColor.Geometry

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Infrastructure Lemmas

These connect the existing Disk.lean machinery to Goertzel's proof structure.
-/

/-- **Bridge Lemma**: toggleSum flips exactly the cut edges.

    This is already proven in Disk.lean via:
    - `toggleSum_supported_on_cuts_10` (support iff cut edge)
    - `aggregated_toggle_strict_descent_at_prescribed_cut` (uses this)
-/
lemma toggleSum_flips_exactly_cuts (G : DiskGeometry V E)
    (S₀ : Finset (Finset E))
    (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    (e : E) (he_int : e ∉ G.toRotationSystem.boundaryEdges) :
    (toggleSum G (1, 0) S₀ e).fst ≠ 0 ↔ e ∈ cutEdges G S₀ := by
  -- This is toggleSum_supported_on_cuts_10 from Disk.lean
  exact toggleSum_supported_on_cuts_10 G hS₀ he_int

/-- **Bridge Lemma**: Leaf toggles give strict descent.

    This wraps the PROVEN theorem from Disk.lean:1153-1166.
-/
lemma leaf_toggle_strict_descent (G : DiskGeometry V E)
    (hNoDigons : NoDigons G)
    (x : E → Bool × Bool)
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (e0 : E) (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ (S₀ : Finset (Finset E)),
      (support₁ (x + toggleSum G (1, 0) S₀)).card < (support₁ x).card := by
  -- This is PROVEN in Disk.lean:1153-1166!
  exact support₁_strict_descent_via_leaf_toggle hNoDigons hx he0_supp he0_int

/-! ## Annular Cut-Parity (Lemma 4.6)

**Goal**: Prove that cut edges have even cardinality.

**Strategy**: This follows from the fact that toggleSum is an F₂² operation,
and aggregated toggles preserve parity.
-/

/-- Cut edges are interior edges with unique face incidence. -/
lemma cutEdge_characterization (G : DiskGeometry V E)
    (S₀ : Finset (Finset E)) (e : E) :
    e ∈ cutEdges G S₀ ↔
      e ∉ G.toRotationSystem.boundaryEdges ∧
      (∃! f, f ∈ S₀ ∧ e ∈ f) := by
  unfold cutEdges
  classical
  simp [Finset.mem_filter]

/-- If cutEdges is a singleton, toggleSum flips exactly that edge. -/
lemma toggleSum_singleton_cut (G : DiskGeometry V E)
    (S₀ : Finset (Finset E))
    (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    (e0 : E) (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    (hcut : cutEdges G S₀ = {e0}) :
    ∀ e, (toggleSum G (1, 0) S₀ e).fst ≠ 0 ↔ e = e0 := by
  intro e
  by_cases he : e ∈ G.toRotationSystem.boundaryEdges
  · -- Boundary edges: toggle is zero
    constructor
    · intro h
      exfalso
      have : (toggleSum G (1, 0) S₀ e).fst = 0 :=
        toggleSum_fst_boundary_zero G hS₀ he
      exact h this
    · intro heq
      subst heq
      contradiction
  · -- Interior edges: use cut characterization
    have hiff := toggleSum_supported_on_cuts_10 G hS₀ he
    rw [hcut] at hiff
    simp only [Finset.mem_singleton] at hiff
    exact hiff

/-! ## Well-Founded Induction Setup

We'll use Nat.lt_wfRel for induction on support size.
-/

/-- Support size decreases via leaf toggles (iterative form). -/
theorem support_descends_to_zero (G : DiskGeometry V E)
    (hNoDigons : NoDigons G) :
    ∀ x ∈ G.asZeroBoundary.zeroBoundarySet,
      ∃ (steps : List (Finset (Finset E))),
        -- Applying toggles in sequence drives support to empty
        sorry := by
  intro x hx
  -- Use well-founded induction on support size
  sorry  -- TODO: Implement using leaf_toggle_strict_descent + WellFounded.fix

/-! ## Spanning Theorem (Partial Assembly)

We can now state a version of the spanning theorem using the proven infrastructure.
-/

/-- **Theorem 4.10 (Partial)**: Any x ∈ W₀(A) can be expressed as toggleSum.

    This is the "spanning" part of the theorem. -/
theorem zeroBoundary_in_toggleSpan (G : DiskGeometry V E)
    (hNoDigons : NoDigons G) :
    ∀ x ∈ G.asZeroBoundary.zeroBoundarySet,
      ∃ (faces : Finset (Finset E)),
        faces ⊆ G.toRotationSystem.internalFaces ∧
        ∀ e, x e = toggleSum G (1, 0) faces e := by
  intro x hx
  -- By induction on support size, using leaf_toggle_strict_descent
  sorry  -- TODO: Implement via well-founded recursion

end FourColor.Kempe.SpanningProofCore
