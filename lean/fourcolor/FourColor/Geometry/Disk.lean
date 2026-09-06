/- This file contains the disk geometry infrastructure for the Four Color Theorem formalization.
   It builds on top of RotationSystem and Triangulation to define disk-specific properties. -/

import FourColor.Geometry.DiskTypes
import FourColor.Geometry.SpanningForest
import FourColor.Geometry.NoDigons
import FourColor.Triangulation
import Mathlib.Data.ZMod.Basic
-- import Hammer -- TODO: Enable once build is green

-- Linter configuration: silence warnings pending systematic cleanup
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

namespace FourColor

open Finset BigOperators Relation
open FourColor.Geometry
open FourColor.Geometry.RotationSystem
open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (G : DiskGeometry V E)

-- **Face cycle parity**: For any internal face f and any vertex v, the number of edges
-- in f incident to v is even. This captures the fact that faces are cycles in the planar dual.
-- Accessible via G.face_cycle_parity.

/-- Toggle sum: aggregated toggle operation over a set of faces -/
def toggleSum (G : DiskGeometry V E) (γ : Color) (S : Finset (Finset E)) (e : E) : Color :=
  ∑ f ∈ S, faceBoundaryChain γ f e

/-- **Relative face boundary chain**: Like faceBoundaryChain but zeros out boundary edges. -/
def faceBoundaryChainRel (G : DiskGeometry V E) (γ : Color) (f : Finset E) (e : E) : Color :=
  if e ∈ f ∧ e ∉ G.toRotationSystem.boundaryEdges then γ else 0

/-- First coordinate of relative chain. -/
@[simp] lemma fst_faceBoundaryRel_at {G : DiskGeometry V E} {γ : Color} {f : Finset E} {e : E} :
  (faceBoundaryChainRel G (γ := (1,0)) f e).fst = 
    if e ∈ f ∧ e ∉ G.toRotationSystem.boundaryEdges then (1 : ZMod 2) else 0 := by
  unfold faceBoundaryChainRel
  split_ifs <;> rfl

/-- Second coordinate of relative chain. -/
@[simp] lemma snd_faceBoundaryRel_at {G : DiskGeometry V E} {γ : Color} {f : Finset E} {e : E} :
  (faceBoundaryChainRel G (γ := (0,1)) f e).snd = 
    if e ∈ f ∧ e ∉ G.toRotationSystem.boundaryEdges then (1 : ZMod 2) else 0 := by
  unfold faceBoundaryChainRel
  split_ifs <;> rfl

/-- Cut edges: interior edges with exactly one incident face in S₀ -/
noncomputable def cutEdges (G : DiskGeometry V E) (S₀ : Finset (Finset E)) : Finset E :=
  Finset.univ.filter (fun e ↦
    e ∉ G.toRotationSystem.boundaryEdges ∧ (∃! f, f ∈ S₀ ∧ e ∈ f))

/-! ## Support-aware definitions (for H2/H3) -/

/-- Support-aware cut: only counts interior edges in support₁ x which have
exactly one incident face in S₀. This ensures toggleSum flips only support edges. -/
noncomputable def cutEdges₁ (G : DiskGeometry V E)
    (x : E → Color) (S₀ : Finset (Finset E)) : Finset E :=
  Finset.univ.filter (fun e ↦
    e ∈ support₁ x ∧
    e ∉ G.toRotationSystem.boundaryEdges ∧
    (∃! f, f ∈ S₀ ∧ e ∈ f))

/-- Faces that meet the first-coordinate support of x -/
def facesTouching₁ (x : E → Color) : Finset (Finset E) :=
  G.toRotationSystem.internalFaces.filter (fun f ↦ (f ∩ support₁ x).Nonempty)

/-! ## Basic helper lemmas -/

lemma odd_iff_one_of_le_two {n : Nat} (hn : n ≤ 2) : 
    ((n : ZMod 2) ≠ 0) ↔ n = 1 := by
  interval_cases n <;> decide

/-- Even parity in char 2 gives zero. -/
lemma Even.zmod_two {n : ℕ} (h : Even n) : (n : ZMod 2) = 0 := by
  obtain ⟨k, rfl⟩ := h
  simp [two_mul]

/-- Interior edges are covered by at least one internal face. -/
theorem DiskGeometry.interior_edge_covered (G : DiskGeometry V E) {e : E}
    (he : e ∉ G.toRotationSystem.boundaryEdges) : 
    ∃ f ∈ G.toRotationSystem.internalFaces, e ∈ f := by
  obtain ⟨fg, ⟨hcard, hfg⟩, _⟩ := two_internal_faces_of_interior_edge G.toPlanarGeometry he
  have : fg.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.card_empty] at hcard
    omega
  obtain ⟨f, hf⟩ := this
  have ⟨hf_internal, he_in_f⟩ := hfg f hf
  exact ⟨f, hf_internal, he_in_f⟩

/-! ## Core lemmas -/

/-- **Card equality for interior edges**: Interior edges have exactly 2 incident faces. -/
lemma card_facesIncidence_eq_two 
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) : 
    (G.toRotationSystem.facesIncidence e).card = 2 := by
  classical
  obtain ⟨fg, ⟨hcard, hprop⟩, huniq⟩ := two_internal_faces_of_interior_edge G.toPlanarGeometry he
  -- Step 1: fg ⊆ facesIncidence e
  have h_sub1 : fg ⊆ G.toRotationSystem.facesIncidence e := by
    intro f hf
    obtain ⟨hint, he_mem⟩ := hprop f hf
    unfold RotationSystem.facesIncidence
    simp [hint, he_mem]
  -- Step 2: facesIncidence e ⊆ (dartsOn e).image faceEdges
  have h_sub_image : G.toRotationSystem.facesIncidence e ⊆ 
        (G.toRotationSystem.dartsOn e).image G.toRotationSystem.faceEdges := by
    intro f hf
    unfold RotationSystem.facesIncidence at hf
    simp only [Finset.mem_filter] at hf
    obtain ⟨hint, he_mem⟩ := hf
    have hcov := G.toRotationSystem.facesIncidence_subset_image_faceEdges_of_dartsOnInternal e
    have : f ∈ (G.toRotationSystem.dartsOnInternal e).image G.toRotationSystem.faceEdges := by
      apply hcov
      unfold RotationSystem.facesIncidence
      simp [hint, he_mem]
    obtain ⟨d, hd, hd_eq⟩ := Finset.mem_image.mp this
    have hsub_darts := G.toRotationSystem.dartsOnInternal_subset_dartsOn e
    exact Finset.mem_image.mpr ⟨d, hsub_darts hd, hd_eq⟩

  have h_ge : (G.toRotationSystem.facesIncidence e).card ≥ 2 := by
    calc (G.toRotationSystem.facesIncidence e).card 
      ≥ fg.card := Finset.card_le_card h_sub1
      _ = 2 := hcard

  have h_le : (G.toRotationSystem.facesIncidence e).card ≤ 2 := by
    calc (G.toRotationSystem.facesIncidence e).card 
      ≤ ((G.toRotationSystem.dartsOn e).image G.toRotationSystem.faceEdges).card := Finset.card_le_card h_sub_image
      _ ≤ (G.toRotationSystem.dartsOn e).card := Finset.card_image_le
      _ = 2 := G.toRotationSystem.dartsOn_card_two e

  exact le_antisymm h_le h_ge

/-- Helper lemma: Unique existence is equivalent to singleton cardinality. -/
private lemma unique_face_iff_card_filter_one {S₀ : Finset (Finset E)} {e : E} :
    (∃! f, f ∈ S₀ ∧ e ∈ f) ↔ (S₀.filter (fun f ↦ e ∈ f)).card = 1 := by
  constructor
  · intro ⟨f, ⟨hf, he⟩, huniq⟩
    have : S₀.filter (fun f ↦ e ∈ f) = {f} := by
      ext f'; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨hf', he'⟩; exact huniq f' ⟨hf', he'⟩
      · intro hf'; subst hf'; exact ⟨hf, he⟩
    rw [this]; simp
  · intro hcard
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have : f ∈ S₀.filter (fun f ↦ e ∈ f) := by rw [hf]; simp
    use f
    constructor
    · exact ⟨(Finset.mem_filter.mp this).1, (Finset.mem_filter.mp this).2⟩
    · intro f' ⟨hf', he'⟩
      have : f' ∈ S₀.filter (fun f ↦ e ∈ f) := Finset.mem_filter.mpr ⟨hf', he'⟩
      rw [hf] at this
      exact Finset.mem_singleton.mp this

/-! ## Cut-parity lemmas -/

/-- **Cut-parity for γ=(1,0)**: toggleSum supported exactly on cutEdges in first coordinate -/
lemma toggleSum_supported_on_cuts_10 
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) : 
    (toggleSum G (1,0) S₀ e).fst ≠ 0 ↔ e ∈ cutEdges G S₀ := by
  classical
  unfold toggleSum cutEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  let n := (S₀.filter (fun f ↦ e ∈ f)).card

  have hn_bound : n ≤ 2 := by
    calc n = (S₀.filter (fun f ↦ e ∈ f)).card := rfl
         _ ≤ (G.toRotationSystem.facesIncidence e).card := by
             apply Finset.card_le_card
             intro f hf
             simp [RotationSystem.facesIncidence]
             exact ⟨hS₀ (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
         _ = 2 := card_facesIncidence_eq_two G he

  -- First coordinate computes the parity of incidence
  have hfst : (toggleSum G (1,0) S₀ e).fst = (n : ZMod 2) := by
    show (∑ f ∈ S₀, faceBoundaryChain (1, 0) f e).fst = _
    simp only [Prod.fst_sum]
    simp only [fst_faceBoundary_at]
    rw [Finset.sum_boole]

  have hodd : ((n : ZMod 2) ≠ 0) ↔ n = 1 := odd_iff_one_of_le_two hn_bound
  have huniq : (∃! f, f ∈ S₀ ∧ e ∈ f) ↔ (S₀.filter (fun f ↦ e ∈ f)).card = 1 := 
    unique_face_iff_card_filter_one

  constructor
  · intro hne
    have : n = 1 := hodd.mp (hfst ▸ hne)
    have : (∃! f, f ∈ S₀ ∧ e ∈ f) := huniq.mpr this
    exact ⟨he, this⟩
  · intro hmem
    rcases hmem with ⟨_, huniq'⟩
    have h1 : (S₀.filter (fun f ↦ e ∈ f)).card = 1 := huniq.mp huniq'
    have h2 : n = 1 := by simp [n, h1]
    have : (n : ZMod 2) ≠ 0 := hodd.mpr h2
    exact hfst.symm ▸ this

/-! ## Zero-boundary helper lemmas -/

/-- If `x ∈ W₀`, then a support₁ edge cannot be a boundary edge. -/
lemma support₁_edge_is_interior 
    {x : E → Color}
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet) : 
    ∀ ⦃e⦄, e ∈ support₁ x → e ∉ G.toRotationSystem.boundaryEdges := by
  classical
  intro e he
  have hxB := hx.2
  intro heB
  have heB' : e ∈ G.asZeroBoundary.boundaryEdges := by
    rw [G.boundary_compat]
    exact heB
  have : x e = (0,0) := hxB e heB'
  have : (x e).fst = 0 := by simp [this]
  simp [support₁] at he
  contradiction

/-- Internal faces don't contain boundary edges. -/
lemma DiskGeometry.face_disjoint_boundary 
    (f : Finset E) (hf : f ∈ G.toRotationSystem.internalFaces) : 
    ∀ e : E, e ∈ G.asZeroBoundary.boundaryEdges → e ∉ f := by
  intro e he_bound
  have : e ∈ G.toRotationSystem.boundaryEdges := by
    rw [←G.boundary_compat]
    exact he_bound
  exact internal_face_disjoint_boundary G.toPlanarGeometry hf e this

/-- Wrapper lemma: face boundaries are in zeroBoundarySet. -/
lemma DiskGeometry.faceBoundary_zeroBoundary {γ : Color} {f : Finset E}
    (hf : f ∈ G.toRotationSystem.internalFaces) : 
    faceBoundaryChain (γ := γ) f ∈ G.asZeroBoundary.zeroBoundarySet := by
  constructor
  · -- isZeroBoundary: sum at each vertex is 0
    sorry -- Uses vertex parity
  · -- Boundary edges: internal faces don't contain boundary edges
    intro e he
    -- If e is boundary, then e \notin f
    have : e ∉ f := G.face_disjoint_boundary f hf e he
    -- So faceBoundaryChain is 0
    simp [faceBoundaryChain, indicatorChain, this]
    rfl

/-- Toggle sum equality: the definition matches the expansion. -/
@[simp] lemma toggleSum_eq_sum {γ : Color} {S : Finset (Finset E)} :
    toggleSum G γ S = fun e ↦ ∑ f ∈ S, faceBoundaryChain γ f e := rfl

/-- Wrapper lemma: toggleSum produces chains in zeroBoundarySet. -/
lemma DiskGeometry.toggleSum_mem_zero {S : Finset (Finset E)}
    (hS : S ⊆ G.toRotationSystem.internalFaces) : 
    toggleSum G (1,0) S ∈ G.asZeroBoundary.zeroBoundarySet := by
  have : (∑ f ∈ S, faceBoundaryChain (γ := (1,0)) f) ∈ G.asZeroBoundary.zeroBoundarySet := by
    apply G.asZeroBoundary.sum_mem_zero
    intro f hf
    exact G.faceBoundary_zeroBoundary (hS hf)
  rw [toggleSum_eq_sum]
  convert this using 2
  simp only [Finset.sum_apply]

/-- If `x ∈ W₀` and `t ∈ W₀` then `x + t ∈ W₀`. -/
lemma add_preserves_zeroBoundary 
    {x t : E → Color}
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (ht : t ∈ G.asZeroBoundary.zeroBoundarySet) : 
    x + t ∈ G.asZeroBoundary.zeroBoundarySet := 
  G.asZeroBoundary.mem_zero_add hx ht

/-! ## Helper lemmas for cutEdges singleton reasoning -/

@[simp] lemma zmod2_ne_zero_iff_eq_one (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  constructor
  · intro hne
    fin_cases a
    · exact (hne rfl).elim
    · rfl
  · intro h1; simp [h1]

@[simp] lemma fst_add_apply (x y : E → Color) (e : E) : 
  ((x + y) e).fst = (x e).fst + (y e).fst := by
  simp [Pi.add_apply, Prod.fst_add]

/-- If `e` is a boundary edge and `S ⊆ internalFaces`,
then the first coord of `toggleSum (γ = (1,0))` at `e` is zero. -/
lemma toggleSum_fst_boundary_zero 
    {S : Finset (Finset E)} (hS : S ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∈ G.toRotationSystem.boundaryEdges) : 
    (toggleSum G (1,0) S e).fst = 0 := by
  have hterm : ∀ f ∈ S, (faceBoundaryChain (1,0) f e).fst = 0 := by
    intro f hf
    have hfint : f ∈ G.toRotationSystem.internalFaces := hS hf
    have hdis : e ∉ f := internal_face_disjoint_boundary G.toPlanarGeometry hfint e he
    simp [faceBoundaryChain, indicatorChain, hdis]
  simp only [toggleSum, Prod.fst_sum]
  exact Finset.sum_eq_zero hterm

/-! ### Spanning Forest Infrastructure -/

/-- **Subset Support Cut Theorem**: 
    This requires Planar Duality / Jordan Curve Theorem. -/
theorem forest_gives_subset_support_cut {G : DiskGeometry V E}
    (x : E → Color)
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (e0 : E) (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) : 
    ∃ S' : Finset (Finset E),
      S' ⊆ G.toRotationSystem.internalFaces ∧
      S'.Nonempty ∧
      cutEdges G S' ⊆ support₁ x ∧
      e0 ∈ cutEdges G S' := by
  sorry

/-- **Corrected H2**: Exists a component with cut edges contained in support. -/
lemma exists_S₀_support_aware 
    (hNoDigons : NoDigons G)
    {x : E → Color}
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (e0 : E) (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) : 
    ∃ S' : Finset (Finset E),
      S' ⊆ G.toRotationSystem.internalFaces ∧
      S'.Nonempty ∧
      cutEdges G S' ⊆ support₁ x ∧
      e0 ∈ cutEdges G S' := by
  apply @forest_gives_subset_support_cut V E _ _ _ _ G x hx e0 he0_supp he0_int

/-- **H3. Strict descent via subset-support cut (γ=(1,0))** -/
lemma aggregated_toggle_strict_descent_at_subset_support 
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet) (he0_supp : e0 ∈ support₁ x)
    (h_subset : cutEdges G S₀ ⊆ support₁ x)
    (h_e0_in : e0 ∈ cutEdges G S₀) : 
    (support₁ (x + toggleSum G (1,0) S₀)).card < (support₁ x).card := by
  classical
  let y := toggleSum G (1,0) S₀
  
  -- Pointwise description of the new support: 
  -- support₁ (x + y) = support₁ x \ cutEdges G S₀
  have h_diff : support₁ (x + y) = support₁ x \ cutEdges G S₀ := by
    ext e
    by_cases heB : e ∈ G.toRotationSystem.boundaryEdges
    · -- On boundary edges: toggleSum is zero, so nothing changes.
      have hy : (y e).fst = 0 := toggleSum_fst_boundary_zero G hS₀ heB
      have heCut : e ∉ cutEdges G S₀ := by
        intro h
        rw [cutEdges, Finset.mem_filter] at h
        have : e ∉ G.toRotationSystem.boundaryEdges := h.2.1
        contradiction
      simp [support₁, Pi.add_apply, Prod.fst_add, hy, heCut]
    · -- On interior edges:
      have hiff : (y e).fst ≠ 0 ↔ e ∈ cutEdges G S₀ := 
        toggleSum_supported_on_cuts_10 G hS₀ heB
      by_cases heCut : e ∈ cutEdges G S₀
      · -- e is a cut edge: y e has fst = 1, so we flip x e in Z₂
        have hy1 : (y e).fst = 1 := 
          (zmod2_ne_zero_iff_eq_one _).1 (hiff.mpr heCut)
        have heSupp : e ∈ support₁ x := h_subset heCut
        have hx1 : (x e).fst = 1 := 
          (zmod2_ne_zero_iff_eq_one _).1 (mem_support₁.mp heSupp)
        -- 1 + 1 = 0 in Z₂, so e leaves the support
        simp [support₁, Pi.add_apply, Prod.fst_add, hy1, hx1, heCut]
      · -- e is not a cut edge: y e has fst = 0, so x e is unchanged
        have hy0 : (y e).fst = 0 := by
          by_contra h
          exact heCut (hiff.mp h)
        simp [support₁, Pi.add_apply, Prod.fst_add, hy0, heCut]

  rw [h_diff]
  apply Finset.card_lt_card
  apply Finset.sdiff_ssubset h_subset ⟨e0, h_e0_in⟩

/-- **One-step orthogonality peel** -/
lemma orthogonality_peel_step 
    (hNoDigons : NoDigons G)
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (hsupp : (support₁ x).Nonempty) : 
    ∃ (S₀ : Finset (Finset E)) (x' : E → Color),
      x' ∈ G.asZeroBoundary.zeroBoundarySet ∧ 
      (support₁ x').card < (support₁ x).card ∧ 
      x' = (fun e ↦ x e + toggleSum G (1,0) S₀ e) ∧ 
      S₀.Nonempty ∧ S₀ ⊆ G.toRotationSystem.internalFaces := by
  classical
  obtain ⟨e0, he0_supp⟩ := hsupp
  have he0_int : e0 ∉ G.toRotationSystem.boundaryEdges := 
    support₁_edge_is_interior (G := G) hx he0_supp

  obtain ⟨S₀, hS₀_internal, hS₀_ne, hsubset, hin⟩ := 
    exists_S₀_support_aware (G := G) hNoDigons (x := x) hx e0 he0_supp he0_int

  -- Define the peeled coloring
  let x' : E → Color := fun e ↦ x e + toggleSum G (1,0) S₀ e

  refine ⟨S₀, x', ?_⟩
  -- Split conjunction
  refine ⟨?h_zero, ?h_rest⟩

  · -- x' ∈ zeroBoundarySet
    apply add_preserves_zeroBoundary G hx
    exact DiskGeometry.toggleSum_mem_zero G hS₀_internal

  · -- remaining goals: strict descent, definitional equality, and S₀ properties
    refine ⟨?h_desc, ?h_eq, hS₀_ne, hS₀_internal⟩

    · -- strict descent on support
      have := aggregated_toggle_strict_descent_at_subset_support
        (G := G) (S₀ := S₀) hS₀_internal he0_int hx he0_supp hsubset hin
      exact this

    · -- definitional equality
      rfl

end FourColor