/- This file contains the disk geometry infrastructure for the Four Color Theorem formalization.
   It builds on top of RotationSystem and Triangulation to define disk-specific properties. -/

import FourColor.Geometry.DiskTypes
import FourColor.Geometry.SpanningForest
import Mathlib.Data.ZMod.Basic

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

-- DiskGeometry is now imported from DiskTypes


variable (G : DiskGeometry V E)

-- **Face cycle parity**: For any internal face f and any vertex v, the number of edges
-- in f incident to v is even. This captures the fact that faces are cycles in the planar dual:
-- each vertex on the boundary is touched exactly 0 or 2 times (entering and leaving).
-- This is now a definitional property of DiskGeometry (accessible via G.face_cycle_parity).

/-- Toggle sum: aggregated toggle operation over a set of faces -/
def toggleSum (G : DiskGeometry V E) (γ : Color) (S : Finset (Finset E)) (e : E) : Color :=
  ∑ f ∈ S, faceBoundaryChain γ f e

/-- **Relative face boundary chain**: Like faceBoundaryChain but zeros out boundary edges.
This is the correct definition for A4 - we use relative homology. -/
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

/-- Dual adjacency between faces -/
def DiskGeometry.adj (f g : Finset E) : Prop :=
  ∃ e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g ∧
    ∀ e', (e' ∉ G.toRotationSystem.boundaryEdges ∧ e' ∈ f ∧ e' ∈ g) → e' = e

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

/-- Restricted dual adjacency: only across support edges, excluding e0 -/
def adjOnSupportExcept (x : E → Color) (e0 : E) (f g : Finset E) : Prop :=
  f ∈ G.toRotationSystem.internalFaces ∧
  g ∈ G.toRotationSystem.internalFaces ∧
  (∃ e, e ≠ e0 ∧ e ∈ support₁ x ∧ e ∈ f ∧ e ∈ g)

/-- Extract witness edge from adjOnSupportExcept relation -/
private lemma adjOnSupportExcept_exists_support_edge {x : E → Color} {e0 : E} {f g : Finset E}
    (h : adjOnSupportExcept G x e0 f g) :
    ∃ e ∈ support₁ x, e ∈ g := by
  obtain ⟨_, _, e, _, he_supp, _, he_g⟩ := h
  exact ⟨e, he_supp, he_g⟩

/-! ## Basic helper lemmas -/

lemma odd_iff_one_of_le_two {n : Nat} (hn : n ≤ 2) :
    ((n : ZMod 2) ≠ 0) ↔ n = 1 := by
  interval_cases n <;> decide

/-- Even parity in char 2 gives zero. -/
lemma Even.zmod_two {n : ℕ} (h : Even n) : (n : ZMod 2) = 0 := by
  obtain ⟨k, rfl⟩ := h
  simp [two_mul]

/-! ## Axioms and properties -/

/-- Interior edges are covered by at least one internal face.
Proof: By two_internal_faces_of_interior_edge, every interior edge belongs to exactly 2 internal faces. -/
theorem DiskGeometry.interior_edge_covered (G : DiskGeometry V E) {e : E}
    (he : e ∉ G.toRotationSystem.boundaryEdges) :
    ∃ f ∈ G.toRotationSystem.internalFaces, e ∈ f := by
  -- Use the E2 theorem: interior edges have exactly 2 internal faces
  obtain ⟨fg, ⟨hcard, hfg⟩, _⟩ := two_internal_faces_of_interior_edge G.toPlanarGeometry he
  -- fg is nonempty since it has cardinality 2
  have : fg.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.card_empty] at hcard
    omega
  -- Pick any face from fg
  obtain ⟨f, hf⟩ := this
  -- This face is internal and contains e
  have ⟨hf_internal, he_in_f⟩ := hfg f hf
  exact ⟨f, hf_internal, he_in_f⟩

-- **No-digon property**: Two distinct internal faces share at most one interior edge.
-- TODO: This should be proven from rotation system structure (2-cell embedding + simple primal).
-- Proof strategy: In a planar embedding with simple primal, faces are simple 2-cells,
-- so two distinct faces cannot share two edges (this would create a digon/bigon).
-- NoDigons is now imported from DiskTypes

/-- **With `NoDigons`, we get the `adj_spec` property:**
two distinct internal faces share exactly one interior edge or none. -/
theorem DiskGeometry.adj_spec
    (hNoDigons : NoDigons G)
    {f g : Finset E} (hf : f ∈ G.toRotationSystem.internalFaces)
    (hg : g ∈ G.toRotationSystem.internalFaces)
    (hne : f ≠ g) :
    (∃! e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g) ∨
    ¬ ∃ e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g := by
  classical
  -- Collect all shared interior edges
  let S := (f ∩ g).filter (fun e ↦ e ∉ G.toRotationSystem.boundaryEdges)
  have hS_def : ∀ e, e ∈ S ↔ e ∈ f ∧ e ∈ g ∧ e ∉ G.toRotationSystem.boundaryEdges := by
    intro e
    simp only [S, Finset.mem_filter, Finset.mem_inter]
    tauto
  by_cases h0 : S.Nonempty
  · rcases h0 with ⟨e0, he0S⟩
    have he0 : e0 ∈ f ∧ e0 ∈ g ∧ e0 ∉ G.toRotationSystem.boundaryEdges := (hS_def e0).1 he0S
    -- Show S = {e0} using no-digons
    have h_unique : ∀ e ∈ S, e = e0 := by
      intro e heS
      have he : e ∈ f ∧ e ∈ g ∧ e ∉ G.toRotationSystem.boundaryEdges := (hS_def e).1 heS
      by_cases h : e = e0
      · exact h
      · exfalso
        have h' : e0 ≠ e := fun heq => h heq.symm
        exact @hNoDigons f g hf hg hne e0 e h' he0.2.2 he.2.2 he0.1 he0.2.1 he.1 he.2.1
    have hS_singleton : S = {e0} := by
      ext e
      simp only [Finset.mem_singleton]
      constructor
      · exact h_unique e
      · intro h
        rw [h]
        exact he0S
    -- Unique existence
    left
    refine ⟨e0, ?_, ?_⟩
    · exact ⟨he0.2.2, he0.1, he0.2.1⟩
    · intro e ⟨heB, hef, heg⟩
      have : e ∈ S := (hS_def e).2 ⟨hef, heg, heB⟩
      rw [hS_singleton] at this
      exact Finset.mem_singleton.1 this
  · right
    intro ⟨e, he⟩
    have : e ∈ S := (hS_def e).2 ⟨he.2.1, he.2.2, he.1⟩
    exact h0 ⟨e, this⟩

/-! ## Core lemmas -/

/-- **Card equality for interior edges**: Interior edges have exactly 2 incident faces.
This is now a theorem, not an axiom - proven from the RotationSystem structure. -/
lemma card_facesIncidence_eq_two
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    (G.toRotationSystem.facesIncidence e).card = 2 := by
  classical
  -- Use the complete proof from RotationSystem
  obtain ⟨fg, ⟨hcard, hprop⟩, huniq⟩ := two_internal_faces_of_interior_edge G.toPlanarGeometry he

  -- fg is a set of exactly 2 internal faces containing e
  -- facesIncidence e is the set of ALL internal faces containing e
  -- We'll show they're equal, hence card = 2

  -- Strategy: Prove card = 2 using upper and lower bounds (avoids circular reasoning)

  -- Step 1: fg ⊆ facesIncidence e, so card facesIncidence e ≥ 2
  have h_sub1 : fg ⊆ G.toRotationSystem.facesIncidence e := by
    intro f hf
    obtain ⟨hint, he_mem⟩ := hprop f hf
    unfold RotationSystem.facesIncidence
    simp [hint, he_mem]

  have h_ge : 2 ≤ (G.toRotationSystem.facesIncidence e).card := by
    calc 2 = fg.card := hcard.symm
      _ ≤ (G.toRotationSystem.facesIncidence e).card := Finset.card_le_card h_sub1

  -- Step 2: facesIncidence e ⊆ (dartsOn e).image faceEdges, so card facesIncidence e ≤ 2
  have h_le : (G.toRotationSystem.facesIncidence e).card ≤ 2 := by
    -- Use covering lemma: facesIncidence e ⊆ (dartsOnInternal e).image faceEdges
    have hcov := G.toRotationSystem.facesIncidence_subset_image_faceEdges_of_dartsOnInternal e
    have hsub_darts := G.toRotationSystem.dartsOnInternal_subset_dartsOn e
    -- Therefore facesIncidence e ⊆ (dartsOn e).image faceEdges
    have h_sub_image : G.toRotationSystem.facesIncidence e ⊆
          (G.toRotationSystem.dartsOn e).image G.toRotationSystem.faceEdges := by
      intro f hf
      unfold RotationSystem.facesIncidence at hf
      simp only [Finset.mem_filter] at hf
      obtain ⟨hint, he_mem⟩ := hf
      have : f ∈ (G.toRotationSystem.dartsOnInternal e).image G.toRotationSystem.faceEdges := by
        apply hcov
        unfold RotationSystem.facesIncidence
        simp [hint, he_mem]
      obtain ⟨d, hd, hd_eq⟩ := Finset.mem_image.mp this
      exact Finset.mem_image.mpr ⟨d, hsub_darts hd, hd_eq⟩
    -- Image cardinality is at most source cardinality
    calc (G.toRotationSystem.facesIncidence e).card
      ≤ ((G.toRotationSystem.dartsOn e).image G.toRotationSystem.faceEdges).card :=
          Finset.card_le_card h_sub_image
      _ ≤ (G.toRotationSystem.dartsOn e).card := Finset.card_image_le
      _ = 2 := G.toRotationSystem.dartsOn_card_two e

  -- Conclude: card = 2
  omega

/-- **Extract two incident faces** -/
lemma incident_faces_of_interior_edge
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    ∃ f g, f ∈ G.toRotationSystem.internalFaces ∧
           g ∈ G.toRotationSystem.internalFaces ∧
           e ∈ f ∧ e ∈ g ∧ f ≠ g := by
  classical
  have h2 : (G.toRotationSystem.facesIncidence e).card = 2 :=
    card_facesIncidence_eq_two G he
  obtain ⟨f, g, hfg_ne, hfg_eq⟩ := Finset.card_eq_two.mp h2
  use f, g
  have hf : f ∈ G.toRotationSystem.facesIncidence e := by
    rw [hfg_eq]; simp
  have hg : g ∈ G.toRotationSystem.facesIncidence e := by
    rw [hfg_eq]; simp
  simp [RotationSystem.facesIncidence] at hf hg
  exact ⟨hf.1, hg.1, hf.2, hg.2, hfg_ne⟩

/-- **If an internal face f contains interior edge e, then f is one of the two incident faces.** -/
lemma face_mem_incident_pair_of_interior_edge
    {e : E} {f : Finset E}
    (he_int : e ∉ G.toRotationSystem.boundaryEdges)
    (hf_int : f ∈ G.toRotationSystem.internalFaces)
    (he_in_f : e ∈ f)
    (p q : Finset E)
    (hp_int : p ∈ G.toRotationSystem.internalFaces)
    (hq_int : q ∈ G.toRotationSystem.internalFaces)
    (he_in_p : e ∈ p)
    (he_in_q : e ∈ q)
    (hpq_ne : p ≠ q) :
    f = p ∨ f = q := by
  classical
  -- Use facesIncidence which has card 2
  have h_card : (G.toRotationSystem.facesIncidence e).card = 2 :=
    card_facesIncidence_eq_two G he_int
  -- f, p, q are all in facesIncidence e
  have hf_in : f ∈ G.toRotationSystem.facesIncidence e := by
    simp [RotationSystem.facesIncidence]; exact ⟨hf_int, he_in_f⟩
  have hp_in : p ∈ G.toRotationSystem.facesIncidence e := by
    simp [RotationSystem.facesIncidence]; exact ⟨hp_int, he_in_p⟩
  have hq_in : q ∈ G.toRotationSystem.facesIncidence e := by
    simp [RotationSystem.facesIncidence]; exact ⟨hq_int, he_in_q⟩
  -- Since facesIncidence e has exactly 2 elements and contains distinct p, q,
  -- we have facesIncidence e = {p, q}
  have heq : G.toRotationSystem.facesIncidence e = {p, q} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp
      by_contra h
      push_neg at h
      -- x ∈ facesIncidence e, x ≠ p, x ≠ q
      -- But {p, q, x} ⊆ facesIncidence e and card = 2 → contradiction
      have hsub : ({p, q, x} : Finset (Finset E)) ⊆ G.toRotationSystem.facesIncidence e := by
        intro y hy
        simp at hy
        rcases hy with rfl | rfl | rfl
        · exact hp_in
        · exact hq_in
        · exact hx
      have hcard3 : ({p, q, x} : Finset (Finset E)).card ≥ 3 := by
        have heq : ({p, q, x} : Finset (Finset E)) = insert x (insert p {q}) := by
          ext y; simp; tauto
        rw [heq, Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simp; exact hpq_ne
        · simp; exact h
      have hcard_le : ({p, q, x} : Finset (Finset E)).card ≤ 2 := by
        have := Finset.card_le_card hsub
        rw [h_card] at this
        exact this
      omega
    · have : ({p, q} : Finset (Finset E)).card = 2 := by
        simp [Finset.card_insert_of_notMem, hpq_ne]
      omega
  -- Therefore f ∈ {p, q}
  rw [heq] at hf_in
  simpa using hf_in

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

/-! ## Cut-parity lemmas (Lemma 4.7 specialized for γ=(1,0) and γ=(0,1)) -/

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
    -- The sum distributes: (∑ f, g f).coord = ∑ f, (g f).coord
    simp only [Prod.fst_sum]
    -- Now apply fst_faceBoundary_at pointwise
    simp only [fst_faceBoundary_at]
    -- Sum of indicators equals cardinality
    rw [Finset.sum_boole]

  -- In Z₂, "≠ 0" ⇔ "= 1" and under ≤2, parity ≠ 0 ⇔ n = 1
  have hodd : ((n : ZMod 2) ≠ 0) ↔ n = 1 := odd_iff_one_of_le_two hn_bound

  -- Unique face in S₀ containing e ⇔ card (filter ...) = 1
  have huniq : (∃! f, f ∈ S₀ ∧ e ∈ f) ↔ (S₀.filter (fun f ↦ e ∈ f)).card = 1 :=
    unique_face_iff_card_filter_one

  -- Wrap up
  constructor
  · intro hne
    -- hne : (toggleSum …).fst ≠ 0
    have hn_ne : (n : ZMod 2) ≠ 0 := hfst ▸ hne
    have : n = 1 := hodd.mp hn_ne
    -- turn "n=1" into "unique face"
    have : (∃! f, f ∈ S₀ ∧ e ∈ f) := huniq.mpr this
    exact ⟨he, this⟩
  · intro hmem
    -- hmem : e ∉ boundary ∧ ∃! f, f ∈ S₀ ∧ e ∈ f
    rcases hmem with ⟨_, huniq'⟩
    have h1 : (S₀.filter (fun f ↦ e ∈ f)).card = 1 := huniq.mp huniq'
    have h2 : n = 1 := by simp [n, h1]
    have : (n : ZMod 2) ≠ 0 := hodd.mpr h2
    exact hfst.symm ▸ this

/-- **Cut-parity for γ=(0,1)**: toggleSum supported exactly on cutEdges in second coordinate -/
lemma toggleSum_supported_on_cuts_01
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    (toggleSum G (0,1) S₀ e).snd ≠ 0 ↔ e ∈ cutEdges G S₀ := by
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

  -- Second coordinate computes the parity of incidence
  have hsnd : (toggleSum G (0,1) S₀ e).snd = (n : ZMod 2) := by
    show (∑ f ∈ S₀, faceBoundaryChain (0, 1) f e).snd = _
    -- The sum distributes: (∑ f, g f).coord = ∑ f, (g f).coord
    simp only [Prod.snd_sum]
    -- Now apply snd_faceBoundary_at pointwise
    simp only [snd_faceBoundary_at]
    -- Sum of indicators equals cardinality
    rw [Finset.sum_boole]

  -- In Z₂, "≠ 0" ⇔ "= 1" and under ≤2, parity ≠ 0 ⇔ n = 1
  have hodd : ((n : ZMod 2) ≠ 0) ↔ n = 1 := odd_iff_one_of_le_two hn_bound

  -- Unique face in S₀ containing e ⇔ card (filter ...) = 1
  have huniq : (∃! f, f ∈ S₀ ∧ e ∈ f) ↔ (S₀.filter (fun f ↦ e ∈ f)).card = 1 :=
    unique_face_iff_card_filter_one

  -- Wrap up
  constructor
  · intro hne
    -- hne : (toggleSum …).snd ≠ 0
    have hn_ne : (n : ZMod 2) ≠ 0 := hsnd ▸ hne
    have : n = 1 := hodd.mp hn_ne
    -- turn "n=1" into "unique face"
    have : (∃! f, f ∈ S₀ ∧ e ∈ f) := huniq.mpr this
    exact ⟨he, this⟩
  · intro hmem
    -- hmem : e ∉ boundary ∧ ∃! f, f ∈ S₀ ∧ e ∈ f
    rcases hmem with ⟨_, huniq'⟩
    have h1 : (S₀.filter (fun f ↦ e ∈ f)).card = 1 := huniq.mp huniq'
    have h2 : n = 1 := by simp [n, h1]
    have : (n : ZMod 2) ≠ 0 := hodd.mpr h2
    exact hsnd.symm ▸ this

/-! ## Zero-boundary helper lemmas (Section A from GPT-5 Pro) -/

/-- If `x ∈ W₀`, then a support₁ edge cannot be a boundary edge. -/
lemma support₁_edge_is_interior
    {x : E → Color}
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet) :
    ∀ ⦃e⦄, e ∈ support₁ x → e ∉ G.toRotationSystem.boundaryEdges := by
  classical
  intro e he
  have hxB := hx.2
  have : (x e).fst ≠ 0 := by
    -- `support₁` is a `Finset.univ.filter` on the first coordinate
    simp [support₁] at he
    exact he
  intro heB
  -- On the boundary `x e = (0,0)` by definition of W₀
  have heB' : e ∈ G.asZeroBoundary.boundaryEdges := by
    rw [G.boundary_compat]
    exact heB
  have : x e = (0,0) := hxB e heB'
  have : (x e).fst = 0 := by simp [this]
  contradiction

/-- If `x ∈ W₀`, then a support₂ edge cannot be a boundary edge. -/
lemma support₂_edge_is_interior
    {x : E → Color}
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet) :
    ∀ ⦃e⦄, e ∈ support₂ x → e ∉ G.toRotationSystem.boundaryEdges := by
  classical
  intro e he
  have hxB := hx.2
  have : (x e).snd ≠ 0 := by
    -- `support₂` is a `Finset.univ.filter` on the second coordinate
    simp [support₂] at he
    exact he
  intro heB
  -- On the boundary `x e = (0,0)` by definition of W₀
  have heB' : e ∈ G.asZeroBoundary.boundaryEdges := by
    rw [G.boundary_compat]
    exact heB
  have : x e = (0,0) := hxB e heB'
  have : (x e).snd = 0 := by simp [this]
  contradiction

/-- **Boundary/internal separation theorem** (formerly axiom): Internal faces don't contain boundary edges.
Proven from the RotationSystem structure: internal faces are exactly the non-outer φ-orbits,
so they cannot contain edges from the outer face (boundaryEdges). -/
lemma DiskGeometry.face_disjoint_boundary
    (f : Finset E) (hf : f ∈ G.toRotationSystem.internalFaces) :
    ∀ e : E, e ∈ G.asZeroBoundary.boundaryEdges → e ∉ f := by
  intro e he_bound
  -- Use compatibility axiom to translate between the two boundary definitions
  have : e ∈ G.toRotationSystem.boundaryEdges := by
    rw [←G.boundary_compat]
    exact he_bound
  exact internal_face_disjoint_boundary G.toPlanarGeometry hf e this

/-- Wrapper lemma: face boundaries are in zeroBoundarySet.
Proof: Internal faces are cycles where each vertex has exactly 0 or 2 incident edges.
Since 2γ = γ + γ = 0 in F₂ × F₂, the sum at each vertex is 0. -/
lemma DiskGeometry.faceBoundary_zeroBoundary {γ : Color} {f : Finset E}
    (hf : f ∈ G.toRotationSystem.internalFaces) :
    faceBoundaryChain (γ := γ) f ∈ G.asZeroBoundary.zeroBoundarySet := by
  constructor
  · -- isZeroBoundary: sum at each vertex is 0
    -- TODO: Prove using face_cycle_parity
    sorry
  · -- Boundary edges: internal faces don't contain boundary edges
    -- TODO: Prove that internal faces don't contain boundary edges
    sorry

/-- Toggle sum equality: the definition matches the expansion. -/
@[simp] lemma toggleSum_eq_sum {γ : Color} {S : Finset (Finset E)} :
    toggleSum G γ S = fun e ↦ ∑ f ∈ S, faceBoundaryChain γ f e := rfl

/-- Sum of zero-boundary chains is zero-boundary (specialized convenience wrapper). -/
lemma toggleSum_mem_zeroBoundary
    {γ : Color} {S : Finset (Finset E)}
    (hS : S ⊆ G.toRotationSystem.internalFaces) :
    (∑ f ∈ S, faceBoundaryChain (γ := γ) f) ∈ G.asZeroBoundary.zeroBoundarySet := by
  apply G.asZeroBoundary.sum_mem_zero
  intro f hf
  exact G.faceBoundary_zeroBoundary (hS hf)

/-- Wrapper lemma: toggleSum produces chains in zeroBoundarySet.
This uses sum_mem_zero from Triangulation to prove the result. -/
lemma DiskGeometry.toggleSum_mem_zero {S : Finset (Finset E)}
    (hS : S ⊆ G.toRotationSystem.internalFaces) :
    toggleSum G (1,0) S ∈ G.asZeroBoundary.zeroBoundarySet := by
  -- toggleSum G (1,0) S = ∑ f ∈ S, faceBoundaryChain (1,0) f by definition
  have : (∑ f ∈ S, faceBoundaryChain (γ := (1,0)) f) ∈ G.asZeroBoundary.zeroBoundarySet := by
    apply G.asZeroBoundary.sum_mem_zero
    intro f hf
    exact G.faceBoundary_zeroBoundary (hS hf)
  -- Convert between eta-expanded and direct forms
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

lemma cutEdges_eq_singleton_iff_unique
    {S₀ : Finset (Finset E)} {e₀ e : E}
    (h : cutEdges G S₀ = {e₀}) :
    e ∈ cutEdges G S₀ ↔ e = e₀ := by
  classical
  simp [h]

/-- Extend a reachability chain by one step at the end -/
lemma rtransgen_tail {α : Type*} {R : α → α → Prop} {a b c : α}
    (hab : Relation.ReflTransGen R a b) (hbc : R b c) :
    Relation.ReflTransGen R a c :=
  hab.tail hbc

/-- In Z₂, "≠ 0" ⇔ "= 1" -/
@[simp] lemma zmod2_ne_zero_iff_eq_one (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  constructor
  · intro hne
    -- In Z₂, only values are 0 and 1
    fin_cases a
    · contradiction
    · rfl
  · intro h1; simp [h1]

@[simp] lemma fst_add_apply (x y : E → Color) (e : E) :
  ((x + y) e).fst = (x e).fst + (y e).fst := by
  simp [Pi.add_apply, Prod.fst_add]

@[simp] lemma snd_add_apply (x y : E → Color) (e : E) :
  ((x + y) e).snd = (x e).snd + (y e).snd := by
  simp [Pi.add_apply, Prod.snd_add]

@[simp] lemma snd_faceBoundary_gamma10 {f : Finset E} {e : E} :
    (faceBoundaryChain (1,0) f e).snd = 0 := by
  classical
  by_cases he : e ∈ f <;> simp [faceBoundaryChain, indicatorChain, he]

@[simp] lemma snd_toggleSum_gamma10 {S : Finset (Finset E)} {e : E} :
    (toggleSum G (1,0) S e).snd = 0 := by
  classical
  -- Sum of zeros is zero
  show (∑ f ∈ S, faceBoundaryChain (1, 0) f e).snd = 0
  simp only [Prod.snd_sum]
  simp [snd_faceBoundary_at]

@[simp] lemma fst_faceBoundary_gamma01 {f : Finset E} {e : E} :
    (faceBoundaryChain (0,1) f e).fst = 0 := by
  classical
  by_cases he : e ∈ f <;> simp [faceBoundaryChain, indicatorChain, he]

@[simp] lemma fst_toggleSum_gamma01 {S : Finset (Finset E)} {e : E} :
    (toggleSum G (0,1) S e).fst = 0 := by
  classical
  -- Sum of zeros is zero
  show (∑ f ∈ S, faceBoundaryChain (0, 1) f e).fst = 0
  simp only [Prod.fst_sum]
  simp [fst_faceBoundary_at]

/-- Pointwise toggling lemma: if y has fst = 0 off {e₀} and fst ≠ 0 at e₀,
then adding y toggles membership at e₀ only -/
private lemma support₁_add_toggles_singleton
    {x y : E → Color} {e₀ : E}
    (hy0 : ∀ e, e ≠ e₀ → (y e).fst = 0)
    (hy1 : (y e₀).fst ≠ 0) :
    support₁ (x + y) = (support₁ x \ {e₀}) ∪ ({e₀} \ support₁ x) := by
  classical
  ext e
  by_cases h : e = e₀
  · -- At e₀: fst toggles in Z₂
    subst h
    have hy_eq_1 : (y e).fst = (1 : ZMod 2) :=
      (zmod2_ne_zero_iff_eq_one _).1 hy1
    have toggle_iff : ((x e).fst + 1) ≠ 0 ↔ (x e).fst = 0 := by
      by_cases hx : (x e).fst = 0
      · simp [hx]
      · have : (x e).fst = 1 := (zmod2_ne_zero_iff_eq_one _).1 hx
        simp [this]
    -- In Z₂: x = 0 ↔ x ≠ 1
    have z2_iff : (x e).fst = 0 ↔ ¬(x e).fst = 1 := by
      constructor
      · intro h; simp [h]
      · intro h
        by_contra h0
        have : (x e).fst = 1 := (zmod2_ne_zero_iff_eq_one _).1 h0
        exact h this
    -- membership equivalence
    simp [support₁, Pi.add_apply, Prod.fst_add, hy_eq_1, toggle_iff, z2_iff]
  · -- Off e₀: fst is unchanged
    have h0 : (y e).fst = 0 := hy0 e h
    simp [support₁, Pi.add_apply, Prod.fst_add, h0, h, Finset.mem_union, Finset.mem_sdiff]

/-! ## Boundary edge helpers -/

/-- Internal faces don't contain boundary edges (wrapper for the RS lemma). -/
lemma face_disjoint_boundary
    {f : Finset E} (hf : f ∈ G.toRotationSystem.internalFaces)
    (e : E) (he : e ∈ G.toRotationSystem.boundaryEdges) :
    e ∉ f :=
  internal_face_disjoint_boundary G.toPlanarGeometry hf e he

/-- If `e` is a boundary edge and `S ⊆ internalFaces`,
then the first coord of `toggleSum (γ = (1,0))` at `e` is zero. -/
lemma toggleSum_fst_boundary_zero
    {S : Finset (Finset E)} (hS : S ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∈ G.toRotationSystem.boundaryEdges) :
    (toggleSum G (1,0) S e).fst = 0 := by
  -- Each term vanishes because boundary edges don't occur in internal faces.
  have hterm : ∀ f ∈ S, (faceBoundaryChain (1,0) f e).fst = 0 := by
    intro f hf
    have hfint : f ∈ G.toRotationSystem.internalFaces := hS hf
    have hdis : e ∉ f := internal_face_disjoint_boundary G.toPlanarGeometry hfint e he
    simp [faceBoundaryChain, indicatorChain, hdis]
  -- Summing zeros gives zero.
  simp only [toggleSum, Prod.fst_sum]
  exact Finset.sum_eq_zero hterm

/-- If `e` is a boundary edge and `S ⊆ internalFaces`,
then the second coord of `toggleSum (γ = (0,1))` at `e` is zero. -/
lemma toggleSum_snd_boundary_zero
    {S : Finset (Finset E)} (hS : S ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∈ G.toRotationSystem.boundaryEdges) :
    (toggleSum G (0,1) S e).snd = 0 := by
  -- Each term vanishes because boundary edges don't occur in internal faces.
  have hterm : ∀ f ∈ S, (faceBoundaryChain (0,1) f e).snd = 0 := by
    intro f hf
    have hfint : f ∈ G.toRotationSystem.internalFaces := hS hf
    have hdis : e ∉ f := internal_face_disjoint_boundary G.toPlanarGeometry hfint e he
    simp [faceBoundaryChain, indicatorChain, hdis]
  -- Summing zeros gives zero.
  simp only [toggleSum, Prod.snd_sum]
  exact Finset.sum_eq_zero hterm

/-! ### Spanning Forest Infrastructure

The correct approach to H2 uses a spanning forest on the interior dual graph.
This gives us the fundamental cut theorem from graph theory: removing a tree edge
splits the forest into exactly two components, making that edge the unique bridge.
-/

-- dualAdjacent and SpanningForest are now imported from DiskTypes

/-- Every graph has a spanning forest.

    **Proof**: See FourColor.Geometry.DualForest for the complete construction.
    We use Mathlib's spanning tree theorem on the dual graph and map it to
    the primal SpanningForest structure.

    **Status**: ✅ COMPLETE - Proven in DualForest.lean (Lemma 4.7) -/
theorem exists_spanning_forest (G : DiskGeometry V E) (hNoDigons : NoDigons G) :
    Nonempty (SpanningForest G) := by
  obtain ⟨F, _⟩ := FourColor.Geometry.exists_spanning_forest G
  exact ⟨F⟩


/-- We can always get a spanning forest containing any given interior edge
by swapping edges if needed. -/
-- TODO: Prove via forest construction
theorem exists_forest_containing_edge (G : DiskGeometry V E) {e0 : E}
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ F : SpanningForest G, e0 ∈ F.tree_edges
    := by sorry


/-- Reachability in the forest after removing an edge: two faces are connected
if there's a path via tree edges excluding the removed edge. -/
def forestReachable (G : DiskGeometry V E) (F : SpanningForest G) (e_removed : E) (f g : Finset E) : Prop :=
  ReflTransGen (fun f' g' ↦ ∃ e' ∈ F.tree_edges, e' ≠ e_removed ∧ e' ∈ f' ∧ e' ∈ g') f g

/-- The component containing a face after removing an edge from the forest. -/
noncomputable def forestComponent (G : DiskGeometry V E) (F : SpanningForest G) (e_removed : E) (f_seed : Finset E) :
    Finset (Finset E) :=
  G.toRotationSystem.internalFaces.filter (fun f ↦ forestReachable G F e_removed f_seed f)

/-- The seed face is in its component. -/
lemma seed_in_forestComponent {G : DiskGeometry V E} (F : SpanningForest G) {e : E} {f : Finset E}
    (hf : f ∈ G.toRotationSystem.internalFaces) :
    f ∈ forestComponent G F e f := by
  simp [forestComponent, hf]
  exact ReflTransGen.refl

/-- Forest components are subsets of internal faces. -/
lemma forestComponent_subset {G : DiskGeometry V E} (F : SpanningForest G) {e : E} {f : Finset E} :
    forestComponent G F e f ⊆ G.toRotationSystem.internalFaces := by
  intro g hg
  simp [forestComponent] at hg
  exact hg.1

/-- **Subset Support Cut Theorem**:
    Instead of a singleton cut (which requires bridges in the dual graph),
    we find a set `S'` such that `cutEdges G S' \subseteq support x`.
    This implies that `toggleSum S'` flips `e0` (if `e0 \in cutEdges`) and potentially
    other edges, but ONLY edges that are already in `support x`.
    This guarantees `support(x') < support(x)`. -/
theorem forest_gives_subset_support_cut {G : DiskGeometry V E}
    (x : E → Color) (e0 : E) (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ S' : Finset (Finset E),
      S' ⊆ G.toRotationSystem.internalFaces ∧
      S'.Nonempty ∧
      cutEdges G S' ⊆ support₁ x ∧
      e0 ∈ cutEdges G S' := by
  sorry -- Requires cycle logic or support-aware spanning tree

/-- **Corrected H2**: Exists a component with cut edges contained in support. -/
lemma exists_S₀_support_aware
    (hNoDigons : NoDigons G)
    {x : E → Color} (e0 : E) (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ S' : Finset (Finset E),
      S' ⊆ G.toRotationSystem.internalFaces ∧
      S'.Nonempty ∧
      cutEdges G S' ⊆ support₁ x ∧
      e0 ∈ cutEdges G S' := by
  exact forest_gives_subset_support_cut x e0 he0_supp he0_int

/-- **H3. Strict descent via subset-support cut (γ=(1,0))**
    If `cutEdges G S₀ \subseteq support₁ x` and `e0 ∈ cutEdges G S₀`,
    then toggling `S₀` reduces support size by at least 1 (since `e0` flips 1->0). -/
lemma aggregated_toggle_strict_descent_at_subset_support
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet) (he0_supp : e0 ∈ support₁ x)
    (h_subset : cutEdges G S₀ ⊆ support₁ x)
    (h_e0_in : e0 ∈ cutEdges G S₀) :
    (support₁ (x + toggleSum G (1,0) S₀)).card < (support₁ x).card := by
  classical
  let y := toggleSum G (1,0) S₀
  
  -- Analyze change in support
  have h_diff : support₁ (x + y) = support₁ x \ cutEdges G S₀ := by
    ext e
    by_cases heB : e ∈ G.toRotationSystem.boundaryEdges
    · -- Boundary: unchanged
      have hy : (y e).fst = 0 := toggleSum_fst_boundary_zero G hS₀ heB
      have heCut : e ∉ cutEdges G S₀ := by simp [cutEdges, heB]
      simp [support₁, Pi.add_apply, Prod.fst_add, hy, heCut]
    · -- Interior
      have hiff : (y e).fst ≠ 0 ↔ e ∈ cutEdges G S₀ :=
        toggleSum_supported_on_cuts_10 G hS₀ heB
      by_cases heCut : e ∈ cutEdges G S₀
      · -- In cut: flips
        have hy1 : (y e).fst = 1 := (zmod2_ne_zero_iff_eq_one _).1 (hiff.mpr heCut)
        have heSupp : e ∈ support₁ x := h_subset heCut
        have hx1 : (x e).fst = 1 := (zmod2_ne_zero_iff_eq_one _).1 (mem_support₁.mp heSupp)
        simp [support₁, Pi.add_apply, Prod.fst_add, hy1, hx1]
        -- (1+1 = 0) -> not in new support
        simp [heCut]
      · -- Not in cut: no flip
        have hy0 : (y e).fst = 0 := by
          by_contra h; exact heCut (hiff.mp h)
        simp [support₁, Pi.add_apply, Prod.fst_add, hy0, heCut]

  have h_proper : support₁ (x + y) ⊂ support₁ x := by
    rw [h_diff]
    apply Finset.sdiff_ssubset
    · exact h_subset
    · use e0
      constructor
      · exact h_e0_in
      · exact he0_supp
  exact Finset.card_lt_card h_proper

/-- **H2+H3 Combined: Full strict descent theorem (γ=(1,0))** -/
theorem support₁_strict_descent_via_leaf_toggle
    (hNoDigons : NoDigons G)
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    {e0 : E} (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ (S₀ : Finset (Finset E)),
      (support₁ (x + toggleSum G (1,0) S₀)).card < (support₁ x).card := by
  classical
  obtain ⟨S₀, hS₀_internal, _hne, hsubset, hin⟩ := exists_S₀_support_aware G hNoDigons e0 he0_supp he0_int
  exact ⟨S₀, aggregated_toggle_strict_descent_at_subset_support G hS₀_internal he0_int hx he0_supp hsubset hin⟩

/-! ## One-step orthogonality peel wrapper (Section C from GPT-5 Pro) -/

/-- One-step orthogonality peel with explicit `x'` construction. -/
lemma orthogonality_peel_step
    (hNoDigons : NoDigons G)
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (hsupp : (support₁ x).Nonempty) :
    ∃ (S₀ : Finset (Finset E)) (x' : E → Color),
      x' ∈ G.asZeroBoundary.zeroBoundarySet ∧
      (support₁ x').card < (support₁ x).card ∧
      x' = fun e ↦ x e + toggleSum G (1,0) S₀ e ∧
      S₀.Nonempty ∧ S₀ ⊆ G.toRotationSystem.internalFaces := by
  classical
  obtain ⟨e0, he0_supp⟩ := hsupp
  have he0_int : e0 ∉ G.toRotationSystem.boundaryEdges :=
    support₁_edge_is_interior (G := G) hx he0_supp

  obtain ⟨S₀, hdesc⟩ := support₁_strict_descent_via_leaf_toggle G hNoDigons hx he0_supp he0_int
  obtain ⟨_, hS₀_sub, hS₀_ne, _, _⟩ := exists_S₀_support_aware G hNoDigons e0 he0_supp he0_int

  use S₀
  use (fun e ↦ x e + toggleSum G (1,0) S₀ e)
  repeat' constructor
  · apply G.asZeroBoundary.mem_zero_add hx
    rw [toggleSum_eq_sum]
    apply toggleSum_mem_zeroBoundary G hS₀_sub
  · exact hdesc
  · exact hS₀_ne
  · exact hS₀_sub

/-- One-step orthogonality peel for support₂ (mirror of support₁ version). -/
lemma orthogonality_peel_step_support₂
    (hNoDigons : NoDigons G)
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (hsupp : (support₂ x).Nonempty) :
    ∃ (S₀ : Finset (Finset E)) (x' : E → Color),
      x' ∈ G.asZeroBoundary.zeroBoundarySet ∧
      (support₂ x').card < (support₂ x).card ∧
      x' = fun e ↦ x e + toggleSum G (0,1) S₀ e := by
  sorry -- Symmetric to support1

/-- **Mirror of H3 for γ=(0,1): strict descent in support₂**

Identical structure to the (1,0) version, but using .snd and support₂.
-/
lemma aggregated_toggle_strict_descent_at_prescribed_cut_01
    {S₀ : Finset (Finset E)} (hS₀_sub : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    (hcut : cutEdges G S₀ = {e0})
    {x : E → Color} (hx : x ∈ G.zeroBoundarySet) (he0_supp : e0 ∈ support₂ x) :
    (support₂ (x + toggleSum G (0,1) S₀)).card < (support₂ x).card := by
  sorry

/-- Wrapper lemma: aggregated peel witness (single face version).
This packages the descent lemmas for the single-face peel interface. -/
-- TODO: Prove peel witness exists
theorem DiskGeometry.exists_agg_peel_witness
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (hsupp : support₁ x ≠ ∅) :
    ∃ f ∈ G.toRotationSystem.internalFaces, ∃ x',
      x' ∈ G.asZeroBoundary.zeroBoundarySet ∧
      x = x' + faceBoundaryChain (γ := (1,0)) f ∧
      Finset.card (support₁ x') < Finset.card (support₁ x) := by sorry

/-- Wrapper lemma: aggregated peel witness (multi-face sum version).
This packages the descent lemmas for the multi-face peel interface. -/
theorem DiskGeometry.exists_agg_peel_witness_sum
    (hNoDigons : NoDigons G)
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (hsupp : support₁ x ≠ ∅) :
    ∃ S₀ : Finset (Finset E),
      S₀.Nonempty ∧
      S₀ ⊆ G.toRotationSystem.internalFaces ∧
      ∃ x',
        x' ∈ G.asZeroBoundary.zeroBoundarySet ∧
        x = x' + (∑ f ∈ S₀, faceBoundaryChain (γ := (1,0)) f) ∧
        Finset.card (support₁ x') < Finset.card (support₁ x) := by
  classical
  have : (support₁ x).Nonempty := by rwa [Finset.nonempty_iff_ne_empty]
  obtain ⟨S₀, x', hx', hdesc, heq, hne, hsub⟩ := orthogonality_peel_step G hNoDigons hx this
  refine ⟨S₀, hne, hsub, x', hx', ?_, hdesc⟩
  · rw [heq, toggleSum_eq_sum]

/-- **Vertex parity theorem** (formerly axiom): For any internal face, the boundary chain sums to zero at each vertex.
Proven from face_cycle_parity: each vertex has an even number of incident edges in f,
combined with γ + γ = 0 in F₂×F₂. -/
lemma DiskGeometry.parity_at_vertices
    (γ : Color) (f : Finset E) (hf : f ∈ G.toRotationSystem.internalFaces) :
    ∀ v : V, ∑ e ∈ G.asZeroBoundary.incident v, faceBoundaryChain (γ := γ) f e = (0, 0) := by
  intro v
  -- Split sum into edges in f vs not in f
  trans (∑ e ∈ G.asZeroBoundary.incident v ∩ f, faceBoundaryChain γ f e)
  · symm
    apply Finset.sum_subset
    · exact Finset.inter_subset_left
    intro e he hnot
    simp only [Finset.mem_inter, not_and] at hnot
    have : e ∉ f := hnot he
    simp [faceBoundaryChain, indicatorChain, this]
  -- For edges in f, faceBoundaryChain gives γ
  trans (∑ e ∈ G.asZeroBoundary.incident v ∩ f, γ)
  · apply Finset.sum_congr rfl
    intro e he
    have : e ∈ f := (Finset.mem_inter.mp he).2
    simp [faceBoundaryChain, indicatorChain, this]
  -- Use even parity: card = 2k, so sum = (2k) • γ = k•γ + k•γ = k•(γ+γ) = k•0 = 0
  have heven := G.face_cycle_parity hf v
  obtain ⟨k, hk⟩ := heven
  simp only [Finset.sum_const, hk, color_add_self, add_nsmul, nsmul_zero, add_zero]

/-- **Vertex parity theorem** (formerly axiom): For any internal face, the relative boundary
chain sums to zero at each vertex. Proven from φ-orbit structure in RotationSystem. -/
lemma DiskGeometry.parity_at_vertices_rel
    (γ : Color) (f : Finset E) (hf : f ∈ G.toRotationSystem.internalFaces) :
    ∀ v : V, ∑ e ∈ G.asZeroBoundary.incident v, faceBoundaryChainRel G (γ := γ) f e = (0, 0) := by
  intro v
  -- Reduce the sum to the interior edges of f incident to v
  have sum_eq :
      ∑ e ∈ G.asZeroBoundary.incident v, faceBoundaryChainRel G (γ := γ) f e =
      ((G.asZeroBoundary.incident v ∩ f).filter
          (fun e => e ∉ G.toRotationSystem.boundaryEdges)).card • γ := by
    classical
    -- First, restrict the domain to edges that (a) are in f and (b) are not boundary
    -- Using sum_subset: sum over filtered set = sum over full set if extras contribute 0
    have sum_restrict : ∑ e ∈ G.asZeroBoundary.incident v, faceBoundaryChainRel G (γ := γ) f e =
        ∑ e ∈ (G.asZeroBoundary.incident v ∩ f).filter
              (fun e => e ∉ G.toRotationSystem.boundaryEdges),
          faceBoundaryChainRel G (γ := γ) f e := by
      symm
      apply Finset.sum_subset
      · -- Show filtered set ⊆ incident v
        intro e he
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact he.1.1
      · -- Show elements in incident v but not in filtered set contribute 0
        intro e he_incident he_not_filtered
        unfold faceBoundaryChainRel
        -- Either e ∉ f or e ∈ boundary; in both cases the value is 0
        split_ifs with h_cond
        · -- This case: e ∈ f ∧ e ∉ boundaryEdges
          -- But then e would be in the filtered set, contradiction
          exfalso
          apply he_not_filtered
          simp only [Finset.mem_filter, Finset.mem_inter]
          exact ⟨⟨he_incident, h_cond.1⟩, h_cond.2⟩
        · -- This case: ¬(e ∈ f ∧ e ∉ boundaryEdges), so value is 0
          rfl
    rw [sum_restrict]
    -- On the filtered set, every summand equals γ
    have all_eq_gamma : ∀ e ∈ (G.asZeroBoundary.incident v ∩ f).filter
                          (fun e => e ∉ G.toRotationSystem.boundaryEdges),
                   faceBoundaryChainRel G (γ := γ) f e = γ := by
      intro e he
      unfold faceBoundaryChainRel
      simp only [Finset.mem_filter, Finset.mem_inter] at he
      -- e ∈ f and e ∉ boundaryEdges, so the if-condition is true
      simp [he.1.2, he.2]
    -- Sum of constant γ over a set is card • γ
    trans ((G.asZeroBoundary.incident v ∩ f).filter
            (fun e => e ∉ G.toRotationSystem.boundaryEdges)).card • γ
    · rw [← Finset.sum_const]
      apply Finset.sum_congr rfl all_eq_gamma
    · rfl

  -- Use the equality to card • γ, and kill even multiples in F₂×F₂
  rw [sum_eq]

  -- Show the *filtered* set has even cardinality
  -- This uses that internal faces contain no boundary edges,
  -- so the filter is actually identity on (incident v ∩ f)
  have h_filter_id :
      ((G.asZeroBoundary.incident v ∩ f).filter
          (fun e => e ∉ G.toRotationSystem.boundaryEdges))
      = (G.asZeroBoundary.incident v ∩ f) := by
    ext e
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).1
    · intro he
      -- e ∈ incident v ∩ f → e ∉ boundaryEdges (internal faces disjoint boundary)
      have hf' : e ∈ f := (Finset.mem_inter.mp he).2
      have hbnd : e ∉ G.toRotationSystem.boundaryEdges := by
        -- If e were boundary, we'd contradict hf' using internal_face_disjoint_boundary
        intro hb
        exact (internal_face_disjoint_boundary G.toPlanarGeometry hf e hb) hf'
      exact Finset.mem_filter.mpr ⟨he, hbnd⟩

  -- Parity of the intersection uses face_cycle_parity
  have h_even_inter : Even (G.asZeroBoundary.incident v ∩ f).card :=
    G.face_cycle_parity hf v
  have h_even_filtered :
      Even ((G.asZeroBoundary.incident v ∩ f).filter
              (fun e => e ∉ G.toRotationSystem.boundaryEdges)).card := by
    rw [h_filter_id]
    exact h_even_inter

  -- Even multiples vanish in characteristic 2: (2k)•γ = k•(γ+γ) = k•0 = 0
  obtain ⟨k, hk⟩ := h_even_filtered
  rw [hk, add_nsmul]
  simp [color_add_self]



end FourColor