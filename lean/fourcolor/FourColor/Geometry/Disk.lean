/- This file contains the disk geometry infrastructure for the Four Color Theorem formalization.
   It builds on top of RotationSystem and Triangulation to define disk-specific properties. -/

import FourColor.Triangulation
import FourColor.Geometry.RotationSystem
import Mathlib.Data.ZMod.Basic

namespace FourColor

open Finset BigOperators
open FourColor.Geometry

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Disk geometry structure extending rotation system with boundary information -/
structure DiskGeometry (V E : Type*) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] extends
    RotationSystem V E where
  /-- Zero-boundary set: colorings that sum to 0 on the boundary -/
  zeroBoundarySet : Set (E → Color)

variable (G : DiskGeometry V E)

/-- Toggle sum: aggregated toggle operation over a set of faces -/
def toggleSum (G : DiskGeometry V E) (γ : Color) (S : Finset (Finset E)) (e : E) : Color :=
  ∑ f ∈ S, faceBoundaryChain γ f e

/-- Dual adjacency between faces -/
def DiskGeometry.adj (f g : Finset E) : Prop :=
  ∃ e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g ∧
    ∀ e', (e' ∉ G.toRotationSystem.boundaryEdges ∧ e' ∈ f ∧ e' ∈ g) → e' = e

/-- Cut edges: interior edges with exactly one incident face in S₀ -/
noncomputable def cutEdges (G : DiskGeometry V E) (S₀ : Finset (Finset E)) : Finset E := by
  classical
  exact Finset.univ.filter (fun e =>
    e ∉ G.toRotationSystem.boundaryEdges ∧ (∃! f, f ∈ S₀ ∧ e ∈ f))

/-! ## Basic helper lemmas -/

lemma odd_iff_one_of_le_two {n : Nat} (hn : n ≤ 2) :
    ((n : ZMod 2) ≠ 0) ↔ n = 1 := by
  interval_cases n <;> decide

/-! ## Axioms and properties -/

/-- Interior edges are covered by at least one internal face -/
axiom DiskGeometry.interior_edge_covered (G : DiskGeometry V E) {e : E}
    (he : e ∉ G.toRotationSystem.boundaryEdges) :
    ∃ f ∈ G.toRotationSystem.internalFaces, e ∈ f

/-- Adjacency specification: distinct internal faces share either exactly one interior edge or none -/
axiom DiskGeometry.adj_spec (G : DiskGeometry V E)
    {f g : Finset E} (hf : f ∈ G.toRotationSystem.internalFaces)
    (hg : g ∈ G.toRotationSystem.internalFaces) (hne : f ≠ g) :
    (∃! e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g) ∨
    ¬∃ e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g

/-! ## Core lemmas -/

/-- **Card equality for interior edges**: Interior edges have exactly 2 incident faces (E2 axiom) -/
lemma card_facesIncidence_eq_two
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    (G.toRotationSystem.facesIncidence e).card = 2 := by
  classical
  let n := (G.toRotationSystem.facesIncidence e).card
  have hn : n ≤ 2 := E2 he

  have hfst : (∑ f ∈ G.toRotationSystem.internalFaces,
      (if e ∈ f then (1 : ZMod 2) else 0)) = 0 := by sorry

  have hsum_eq : (∑ f ∈ G.toRotationSystem.internalFaces,
      (if e ∈ f then (1 : ZMod 2) else 0))
      = ∑ f ∈ G.toRotationSystem.facesIncidence e, (1 : ZMod 2) := by
    rw [← Finset.sum_filter]
    rfl

  have hpar : (n : ZMod 2) = 0 := by
    sorry

  have hcov : 0 < n := by sorry

  have : n = 2 := by sorry
  exact this

/-- **Extract two incident faces** -/
lemma incident_faces_of_interior_edge
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    ∃ f g, f ∈ G.toRotationSystem.internalFaces ∧
           g ∈ G.toRotationSystem.internalFaces ∧
           e ∈ f ∧ e ∈ g ∧ f ≠ g := by
  classical
  have h2 : (G.toRotationSystem.facesIncidence e).card = 2 :=
    card_facesIncidence_eq_two G E2 he
  obtain ⟨f, g, hfg_ne, hfg_eq⟩ := Finset.card_eq_two.mp h2
  use f, g
  have hf : f ∈ G.toRotationSystem.facesIncidence e := by
    rw [hfg_eq]; simp
  have hg : g ∈ G.toRotationSystem.facesIncidence e := by
    rw [hfg_eq]; simp
  simp [RotationSystem.facesIncidence] at hf hg
  exact ⟨hf.1, hg.1, hf.2, hg.2, hfg_ne⟩

/-- Helper lemma: Unique existence is equivalent to singleton cardinality. -/
private lemma unique_face_iff_card_filter_one {S₀ : Finset (Finset E)} {e : E} :
    (∃! f, f ∈ S₀ ∧ e ∈ f) ↔ (S₀.filter (fun f => e ∈ f)).card = 1 := by
  constructor
  · intro ⟨f, ⟨hf, he⟩, huniq⟩
    have : S₀.filter (fun f => e ∈ f) = {f} := by
      ext f'; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨hf', he'⟩; exact huniq f' ⟨hf', he'⟩
      · intro hf'; subst hf'; exact ⟨hf, he⟩
    rw [this]; simp
  · intro hcard
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have : f ∈ S₀.filter (fun f => e ∈ f) := by rw [hf]; simp
    use f
    constructor
    · exact ⟨(Finset.mem_filter.mp this).1, (Finset.mem_filter.mp this).2⟩
    · intro f' ⟨hf', he'⟩
      have : f' ∈ S₀.filter (fun f => e ∈ f) := Finset.mem_filter.mpr ⟨hf', he'⟩
      rw [hf] at this
      exact Finset.mem_singleton.mp this

/-! ## Cut-parity lemmas (Lemma 4.7 specialized for γ=(1,0) and γ=(0,1)) -/

/-- **Cut-parity for γ=(1,0)**: toggleSum supported exactly on cutEdges in first coordinate -/
lemma toggleSum_supported_on_cuts_10
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    (toggleSum G (1,0) S₀ e).fst ≠ 0 ↔ e ∈ cutEdges G S₀ := by
  classical
  unfold toggleSum cutEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  let n := (S₀.filter (fun f => e ∈ f)).card

  have hn_bound : n ≤ 2 := by
    calc n = (S₀.filter (fun f => e ∈ f)).card := rfl
         _ ≤ (G.toRotationSystem.facesIncidence e).card := by
             apply Finset.card_le_card
             intro f hf
             simp [RotationSystem.facesIncidence]
             exact ⟨hS₀ (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
         _ ≤ 2 := E2 he

  have : (toggleSum G (1,0) S₀ e).fst = (n : ZMod 2) := by sorry

  sorry

/-- **Cut-parity for γ=(0,1)**: toggleSum supported exactly on cutEdges in second coordinate -/
lemma toggleSum_supported_on_cuts_01
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    (toggleSum G (0,1) S₀ e).snd ≠ 0 ↔ e ∈ cutEdges G S₀ := by
  classical
  unfold toggleSum cutEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  let n := (S₀.filter (fun f => e ∈ f)).card

  have hn_bound : n ≤ 2 := by
    calc n = (S₀.filter (fun f => e ∈ f)).card := rfl
         _ ≤ (G.toRotationSystem.facesIncidence e).card := by
             apply Finset.card_le_card
             intro f hf
             simp [RotationSystem.facesIncidence]
             exact ⟨hS₀ (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
         _ ≤ 2 := E2 he

  have : (toggleSum G (0,1) S₀ e).snd = (n : ZMod 2) := by sorry

  sorry

/-! ## Helper lemmas for cutEdges singleton reasoning -/

lemma cutEdges_eq_singleton_iff_unique
    {S₀ : Finset (Finset E)} {e₀ e : E}
    (h : cutEdges G S₀ = {e₀}) :
    e ∈ cutEdges G S₀ ↔ e = e₀ := by sorry

@[simp] lemma snd_faceBoundary_gamma10 {f : Finset E} {e : E} :
    (faceBoundaryChain (1,0) f e).snd = 0 := by sorry

@[simp] lemma snd_toggleSum_gamma10 {S : Finset (Finset E)} {e : E} :
    (toggleSum G (1,0) S e).snd = 0 := by sorry

@[simp] lemma fst_faceBoundary_gamma01 {f : Finset E} {e : E} :
    (faceBoundaryChain (0,1) f e).fst = 0 := by sorry

@[simp] lemma fst_toggleSum_gamma01 {S : Finset (Finset E)} {e : E} :
    (toggleSum G (0,1) S e).fst = 0 := by sorry

/-- **H2. Prescribed-cut leaf-subtree** - TODO: Clean reimplementation needed -/
lemma exists_leaf_subtree_with_prescribed_cut
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {x : E → Color} (hx : x ∈ G.zeroBoundarySet)
    {e0 : E} (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ (S : Finset (Finset E)), S ⊆ G.toRotationSystem.internalFaces ∧
      (∃ f ∈ S, (f ∩ support₁ x).Nonempty) ∧
      ∃ (S₀ : Finset (Finset E)), S₀.Nonempty ∧ S₀ ⊆ S ∧ (cutEdges G S₀) = {e0} := by
  sorry

/-- **H3. Strict descent via prescribed cut** -/
lemma aggregated_toggle_strict_descent_at_prescribed_cut
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀_sub : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    (hcut : cutEdges G S₀ = {e0})
    {x : E → Color} (hx : x ∈ G.zeroBoundarySet) (he0_supp : e0 ∈ support₁ x) :
    (support₁ (x + toggleSum G (1,0) S₀)).card < (support₁ x).card := by
  classical
  have hsupp : ∀ e ∉ G.toRotationSystem.boundaryEdges,
      (toggleSum G (1,0) S₀ e).fst ≠ 0 ↔ e = e0 := by
    intro e he; rw [toggleSum_supported_on_cuts_10 G E2 hS₀_sub he]
    exact cutEdges_eq_singleton_iff_unique G hcut
  have : support₁ (x + toggleSum G (1,0) S₀) = (support₁ x) \ {e0} := by sorry
  sorry

/-- Mirror of H3 for γ=(0,1): strict descent in support₂ -/
lemma aggregated_toggle_strict_descent_at_prescribed_cut_01
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀_sub : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    (hcut : cutEdges G S₀ = {e0})
    {x : E → Color} (hx : x ∈ G.zeroBoundarySet) (he0_supp : e0 ∈ support₂ x) :
    (support₂ (x + toggleSum G (0,1) S₀)).card < (support₂ x).card := by
  classical
  have hsupp : ∀ e ∉ G.toRotationSystem.boundaryEdges,
      (toggleSum G (0,1) S₀ e).snd ≠ 0 ↔ e = e0 := by
    intro e he; rw [toggleSum_supported_on_cuts_01 G E2 hS₀_sub he]
    exact cutEdges_eq_singleton_iff_unique G hcut
  have : support₂ (x + toggleSum G (0,1) S₀) = (support₂ x) \ {e0} := by sorry
  sorry

end FourColor
