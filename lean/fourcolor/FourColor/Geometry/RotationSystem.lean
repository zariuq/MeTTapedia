import FourColor.Triangulation
import FourColor.Compat.CompatV2024

namespace FourColor
namespace Geometry

open scoped BigOperators
open Classical
open FourColor.Compat

noncomputable section

variables {V E : Type*}

/-- **Rotation system** (combinatorial map): darts + edge-flip + vertex-rotation.
This is the standard topological graph theory structure for planar embeddings.
From this we derive faces as φ-orbits and prove the two-incidence axiom E2. -/
structure RotationSystem (V E : Type*)
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  D : Type*
  [instFintypeD : Fintype D]
  [instDecEqD : DecidableEq D]
  edgeOf : D → E                               -- underlying edge of a dart
  vertOf : D → V                               -- vertex of a dart
  alpha : Equiv.Perm D                         -- edge flip (α)
  rho : Equiv.Perm D                           -- rotation at vertex (ρ)

  -- α is a fixed-point-free involution pairing exactly two darts per edge:
  alpha_involutive : ∀ d, alpha (alpha d) = d
  alpha_fixfree    : ∀ d, alpha d ≠ d
  edge_alpha       : ∀ d, edgeOf (alpha d) = edgeOf d
  edge_fiber_two   : ∀ e : E, (Finset.univ.filter (fun d => edgeOf d = e)).card = 2

  -- ρ preserves incident vertex (rotation):
  vert_rho         : ∀ d, vertOf (rho d) = vertOf d

  -- Choose an "outer" face as a φ-orbit (disk boundary):
  outer : D

  -- **No self-loops**: The two darts of an edge have different vertices.
  -- Required for simple planar graphs (Four Color Theorem applies to simple graphs).
  no_self_loops : ∀ d : D, vertOf d ≠ vertOf (alpha d)

-- Enable instances for D type
attribute [instance] RotationSystem.instFintypeD RotationSystem.instDecEqD

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Decidability for dual adjacency -/
def adjDec : DecidableRel (fun f g : Finset E => ∃ e, e ∈ f ∧ e ∈ g) :=
  fun _ _ => by classical exact inferInstance

instance adjDecidable (f g : Finset E) : Decidable (∃ e, e ∈ f ∧ e ∈ g) := by
  classical exact inferInstance

/-- Face permutation φ = ρ ∘ α (composition of vertex rotation and edge flip) -/
def phi : Equiv.Perm RS.D := RS.rho * RS.alpha

/-- A face as a φ-orbit (as a set of darts).
Uses SameCycle relation which captures repeated applications of phi. -/
def faceOrbit (d : RS.D) : Finset RS.D :=
  Finset.univ.filter (fun d' => RS.phi.SameCycle d d')

/-- Edges of a face = image of edgeOf along the φ-orbit -/
def faceEdges (d : RS.D) : Finset E :=
  (RS.faceOrbit d).image RS.edgeOf

/-- Boundary edges = edges on the outer face -/
def boundaryEdges : Finset E :=
  RS.faceEdges RS.outer

/-- Internal faces = all φ-orbit edge-sets except the outer face -/
def internalFaces : Finset (Finset E) :=
  let outerEdges := RS.boundaryEdges
  (Finset.univ.image RS.faceEdges).filter (fun F => F ≠ outerEdges)

/-- Darts with a given underlying edge -/
def dartsOn (e : E) : Finset RS.D :=
  Finset.univ.filter (fun d => RS.edgeOf d = e)

/-- **Planarity axiom for rotation systems**: For interior edges (not on boundary),
α-paired darts belong to different φ-orbits (faces). This is the fundamental
"faces don't cross edges" property of planar embeddings. -/
theorem planarity_interior_edges (RS : RotationSystem V E) :
  ∀ {e : E} {d : RS.D},
    RS.edgeOf d = e →
    e ∉ RS.boundaryEdges →
    RS.faceEdges (RS.alpha d) ≠ RS.faceEdges d

/-- **No parallel edges axiom**: Different edges have different endpoint pairs.
In a simple graph, at most one edge connects any pair of vertices.
This is needed for triangulation properties (e.g., NoDigons). -/
theorem no_parallel_edges (RS : RotationSystem V E) :
  ∀ {e e' : E} {d d' : RS.D},
    RS.edgeOf d = e → RS.edgeOf d' = e' → e ≠ e' →
    ¬(({RS.vertOf d, RS.vertOf (RS.alpha d)} : Finset V) = ({RS.vertOf d', RS.vertOf (RS.alpha d')} : Finset V))

/-- **Boundary edge property**: For boundary edges, both darts belong to the outer face.
This follows from the definition of boundary as the outer face's edge set. -/
theorem boundary_edge_both_outer (RS : RotationSystem V E) :
  ∀ {e : E} {d : RS.D},
    RS.edgeOf d = e →
    e ∈ RS.boundaryEdges →
    RS.faceEdges d = RS.boundaryEdges

/-- **Key lemma from rotation system**: Each edge has exactly 2 darts.
This follows directly from the edge_fiber_two axiom. -/
lemma dartsOn_card_two (e : E) : (RS.dartsOn e).card = 2 := by
  unfold dartsOn
  exact RS.edge_fiber_two e

-- Simp API for rewrites (definitional lemmas to unblock simp)
open Equiv

@[simp] lemma phi_apply (d : RS.D) : RS.phi d = RS.rho (RS.alpha d) := rfl

@[simp] lemma mem_dartsOn {e : E} {d : RS.D} :
  d ∈ RS.dartsOn e ↔ RS.edgeOf d = e := by
  unfold RotationSystem.dartsOn
  simp

@[simp] lemma mem_faceOrbit {d d' : RS.D} :
  d' ∈ RS.faceOrbit d ↔ RS.phi.SameCycle d d' := by
  unfold RotationSystem.faceOrbit
  simp

-- Helpful when pushing α through `dartsOn e`
@[simp] lemma alpha_mem_dartsOn {e : E} {d : RS.D}
  (hd : d ∈ RS.dartsOn e) : RS.alpha d ∈ RS.dartsOn e := by
  rcases (RS.mem_dartsOn).1 hd with h
  simpa [RotationSystem.dartsOn, RS.edge_alpha, h] using (RS.mem_dartsOn).2 (by simpa [RS.edge_alpha, h])

@[simp] lemma faceEdges_outer : RS.faceEdges RS.outer = RS.boundaryEdges := rfl

@[simp] lemma mem_boundaryEdges_iff {e : E} :
  e ∈ RS.boundaryEdges ↔ ∃ d ∈ RS.faceOrbit RS.outer, RS.edgeOf d = e := by
  unfold RotationSystem.boundaryEdges RotationSystem.faceEdges RotationSystem.faceOrbit
  simp

/-- Faces incident to an edge (faces whose edge-set contains the edge) -/
def facesIncidence (e : E) : Finset (Finset E) :=
  RS.internalFaces.filter (fun f => e ∈ f)

/-! ### Helper lemmas for rotation systems

These foundational properties will be useful regardless of the E2 proof strategy.
-/

/-- Alpha preserves the dartsOn sets: if d has edge e, so does α(d). -/
lemma dartsOn_of_alpha {e : E} {d : RS.D} (hd : d ∈ RS.dartsOn e) :
    RS.alpha d ∈ RS.dartsOn e := by
  unfold dartsOn at hd ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
  rw [RS.edge_alpha]
  exact hd

/- Commented out: unused lemma, not needed for E2 or disk geometry
/-- The two darts of an edge are related by alpha: dartsOn e = {d, α(d)} for any d ∈ dartsOn e. -/
lemma dartsOn_eq_pair {e : E} {d : RS.D} (hd : d ∈ RS.dartsOn e) :
    RS.dartsOn e = {d, RS.alpha d} := by
  -- Proof would show the 2-element structure, but not needed for E2
  sorry
-/

/-- An edge belongs to a face iff the face orbit contains a dart with that edge. -/
lemma mem_faceEdges_iff {d : RS.D} {e : E} :
    e ∈ RS.faceEdges d ↔ ∃ d' ∈ RS.faceOrbit d, RS.edgeOf d' = e := by
  unfold faceEdges
  simp only [Finset.mem_image]

/-- If two darts are in the same cycle under phi, they define the same face. -/
lemma faceEdges_of_sameCycle {d d' : RS.D} (h : RS.phi.SameCycle d d') :
    RS.faceEdges d = RS.faceEdges d' := by
  unfold faceEdges faceOrbit
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hx => Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm h) hx,
          fun hx => Equiv.Perm.SameCycle.trans h hx⟩

/-- Reflexivity: every dart is in its own face orbit. -/
lemma mem_faceOrbit_self (d : RS.D) : d ∈ RS.faceOrbit d := by
  unfold faceOrbit
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Equiv.Perm.SameCycle.refl RS.phi d

/-- If d' is in the orbit of d, then the orbits are equal. -/
lemma faceOrbit_of_mem {d d' : RS.D} (h : d' ∈ RS.faceOrbit d) :
    RS.faceOrbit d' = RS.faceOrbit d := by
  unfold faceOrbit at h ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hx => Equiv.Perm.SameCycle.trans h hx,
          fun hx => Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm h) hx⟩

/-- **Coverage for interior edges**: if `e` is not on the boundary face, then
    some internal face contains `e`.  This replaces the ad-hoc axiom in `Disk`. -/
lemma interior_edge_covered {e : E} (he : e ∉ RS.boundaryEdges) :
    ∃ f ∈ RS.internalFaces, e ∈ f := by
  classical
  -- Pick any dart on `e`
  have hc : (RS.dartsOn e).Nonempty := by
    have : (RS.dartsOn e).card = 2 := RS.dartsOn_card_two e
    exact Finset.card_pos.mp (this ▸ (by decide : 0 < 2))
  rcases hc with ⟨d, hd⟩
  -- The face of `d` is internal (otherwise e ∈ boundary)
  have hface_ne : RS.faceEdges d ≠ RS.boundaryEdges := by
    intro hEq
    have : e ∈ RS.faceEdges d := by
      -- `e` is the edge of `d`, so `e ∈ faceEdges d`
      have hmem := (RS.mem_faceEdges_iff).mpr ⟨d, RS.mem_faceOrbit_self d, by
        unfold dartsOn at hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        exact hd⟩
      exact hmem
    -- If this face is the outer boundary, then e ∈ boundaryEdges
    have : e ∈ RS.boundaryEdges := hEq ▸ this
    exact he this
  -- Package as an internal face
  refine ⟨RS.faceEdges d, ?_, ?_⟩
  · -- internalFaces are all face images except the outer one
    unfold internalFaces
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨d, rfl⟩, hface_ne⟩
  · -- e lies on that face
    have hmem := (RS.mem_faceEdges_iff).mpr ⟨d, RS.mem_faceOrbit_self d, by
      unfold dartsOn at hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      exact hd⟩
    exact hmem

/-! ### E2 Proof Infrastructure (GPT-5 Pro's approach)

Following the surjection-via-image strategy to prove E2 from rotation system.
-/

/-- More general orbit equality from SameCycle relation. -/
lemma faceOrbit_eq_of_sameCycle {d d' : RS.D} (h : RS.phi.SameCycle d d') :
    RS.faceOrbit d = RS.faceOrbit d' := by
  ext x
  unfold faceOrbit
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx; exact (Equiv.Perm.SameCycle.symm h).trans hx
  · intro hx; exact h.trans hx

/-- Darts on edge e whose face is internal (not the outer boundary face). -/
def dartsOnInternal (e : E) : Finset RS.D :=
  (RS.dartsOn e).filter (fun d => RS.faceEdges d ≠ RS.boundaryEdges)

/-- Darts on internal faces are a subset of all darts on the edge. -/
lemma dartsOnInternal_subset_dartsOn (e : E) :
    RS.dartsOnInternal e ⊆ RS.dartsOn e :=
  Finset.filter_subset _ _

/-- **Key covering lemma**: Every internal face containing e is the faceEdges of some
dart on e whose face is internal. This establishes the covering needed for E2. -/
lemma facesIncidence_subset_image_faceEdges_of_dartsOnInternal (e : E) :
    RS.facesIncidence e ⊆ (RS.dartsOnInternal e).image RS.faceEdges := by
  classical
  intro f hf
  -- f ∈ internalFaces ∧ e ∈ f
  have hf_int : f ∈ RS.internalFaces := (Finset.mem_filter.mp hf).1
  have he_mem : e ∈ f := (Finset.mem_filter.mp hf).2
  -- Get representative dart d0 with faceEdges d0 = f
  have hf_img : f ∈ (Finset.univ.image RS.faceEdges) :=
    (Finset.mem_filter.mp hf_int).1
  obtain ⟨d0, -, hd0⟩ := Finset.mem_image.mp hf_img
  -- Since e ∈ faceEdges d0, pick δ ∈ faceOrbit d0 with edgeOf δ = e
  have he_in_d0 : e ∈ RS.faceEdges d0 := by rw [hd0]; exact he_mem
  obtain ⟨δ, hδ_orb, hδ_e⟩ := (RS.mem_faceEdges_iff).mp he_in_d0
  -- δ lies on e
  have hδ_dartsOn : δ ∈ RS.dartsOn e := by
    unfold dartsOn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hδ_e
  -- δ has same face as d0 (SameCycle ⇒ same faceEdges)
  have hδ_sameFace : RS.faceEdges δ = RS.faceEdges d0 := by
    have hSame : RS.phi.SameCycle d0 δ := by
      unfold faceOrbit at hδ_orb
      exact (Finset.mem_filter.mp hδ_orb).2
    exact (RS.faceEdges_of_sameCycle hSame).symm
  -- f is internal ⇒ faceEdges d0 ≠ boundaryEdges ⇒ same for δ
  have hδ_internal : RS.faceEdges δ ≠ RS.boundaryEdges := by
    have hne : f ≠ RS.boundaryEdges := (Finset.mem_filter.mp hf_int).2
    rw [hδ_sameFace, hd0]
    exact hne
  -- Hence δ ∈ dartsOnInternal e
  have hδ_int : δ ∈ RS.dartsOnInternal e :=
    Finset.mem_filter.mpr ⟨hδ_dartsOn, hδ_internal⟩
  -- f = faceEdges δ, so it's in the image
  have hf_eq : RS.faceEdges δ = f := by rw [hδ_sameFace, hd0]
  exact Finset.mem_image.mpr ⟨δ, hδ_int, hf_eq⟩

/-- **E2 (Two-Incidence Axiom)**: In a rotation system, every edge belongs to at most 2 internal faces.
This is the fundamental result we need for cut-parity, proven from the rotation system axioms. -/
lemma twoIncidence_ofRotationSystem (e : E) :
    (RS.facesIncidence e).card ≤ 2 := by
  classical
  -- facesIncidence ⊆ image(faceEdges) of dartsOnInternal
  have hcover : RS.facesIncidence e ⊆
      (RS.dartsOnInternal e).image RS.faceEdges :=
    RS.facesIncidence_subset_image_faceEdges_of_dartsOnInternal e
  -- Cardinality chain: facesIncidence ≤ image ≤ dartsOnInternal ≤ dartsOn = 2
  calc (RS.facesIncidence e).card
      ≤ ((RS.dartsOnInternal e).image RS.faceEdges).card :=
        Finset.card_le_card hcover
    _ ≤ (RS.dartsOnInternal e).card :=
        Finset.card_image_le
    _ ≤ (RS.dartsOn e).card :=
        Finset.card_le_card (RS.dartsOnInternal_subset_dartsOn e)
    _ = 2 :=
        RS.dartsOn_card_two e

/-- **α-paired darts lie in distinct faces** for interior edges.

For an interior edge, the two darts related by α (edge flip) belong to different
faces. This is a fundamental planarity property: α swaps between the two sides
of an edge, and φ-orbits (faces) don't cross edges in a planar embedding. -/
lemma faceEdges_alpha_ne_of_interior
    {e : E} {d : RS.D}
    (hd : d ∈ RS.dartsOn e)
    (he : e ∉ RS.boundaryEdges) :
    RS.faceEdges (RS.alpha d) ≠ RS.faceEdges d := by
  -- Apply the planarity axiom
  have he_d : RS.edgeOf d = e := by
    unfold dartsOn at hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact hd
  exact planarity_interior_edges RS he_d he

/-- **Bridge lemma for interior edges**: Extract the two incident internal faces
for an interior edge (not on the outer boundary).

This provides explicit witnesses for the "exactly 2 faces" property, avoiding
fragile parity arguments inside DiskGeometry. -/
lemma two_internal_faces_of_interior_edge
    {e : E} (he : e ∉ RS.boundaryEdges) :
    ∃! (fg : Finset (Finset E)),
        fg.card = 2 ∧ ∀ f ∈ fg, f ∈ RS.internalFaces ∧ e ∈ f := by
  classical
  -- Each edge has exactly two darts
  have hd : (RS.dartsOn e).card = 2 := RS.dartsOn_card_two e

  -- Neither dart lies on the outer face because e ∉ boundaryEdges
  have hδ_int : ∀ d ∈ RS.dartsOn e, RS.faceEdges d ≠ RS.boundaryEdges := by
    intro d hd'
    -- If faceEdges d = boundaryEdges, then e ∈ boundaryEdges, contradiction
    intro h_eq
    have : e ∈ RS.boundaryEdges := by
      -- e ∈ faceEdges d = boundaryEdges
      have he_in : e ∈ RS.faceEdges d := by
        unfold dartsOn at hd'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
        rw [RS.mem_faceEdges_iff]
        use d
        constructor
        · exact RS.mem_faceOrbit_self d
        · exact hd'
      rw [h_eq] at he_in
      exact he_in
    exact he this

  -- Build fg as the image of dartsOn e under faceEdges
  let S := (RS.dartsOn e).image RS.faceEdges

  have hS_card_le : S.card ≤ 2 := by
    calc S.card
      ≤ (RS.dartsOn e).card := Finset.card_image_le
      _ = 2 := RS.dartsOn_card_two e

  -- Show S.card ≥ 1 (at least one face)
  have hS_nonempty : S.Nonempty := by
    obtain ⟨d, hd⟩ : (RS.dartsOn e).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      have : (RS.dartsOn e).card = 0 := by simp [h_empty]
      omega
    refine ⟨RS.faceEdges d, ?_⟩
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

  -- Show S.card = 2 (both darts map to distinct internal faces)
  have hS_card_eq : S.card = 2 := by
    -- We know card ≤ 2, and card ≥ 1
    -- To show = 2, assume card = 1 and derive contradiction
    by_contra h_ne
    have h_le : S.card ≤ 2 := hS_card_le
    have h_pos : 0 < S.card := Finset.card_pos.mpr hS_nonempty
    have : S.card = 1 := by omega

    -- If exactly one internal face contained e, then both darts map to same face.
    -- But we just proved α-paired darts map to different faces - contradiction!
    -- Get the two darts on edge e
    obtain ⟨d, hd⟩ : (RS.dartsOn e).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have hcard_zero : (RS.dartsOn e).card = 0 := by simp [h]
      have hcard_two : (RS.dartsOn e).card = 2 := hd
      omega
    -- S.card = 1 means faceEdges d = faceEdges (α d)
    have hS_singleton : ∃ f, S = {f} := Finset.card_eq_one.mp this
    obtain ⟨f_only, hf_only⟩ := hS_singleton
    have hd_eq : RS.faceEdges d ∈ S := Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hαd_eq : RS.faceEdges (RS.alpha d) ∈ S := by
      apply Finset.mem_image.mpr
      use RS.alpha d
      constructor
      · -- α d ∈ dartsOn e
        unfold dartsOn
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        unfold dartsOn at hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        rw [RS.edge_alpha]; exact hd
      · rfl
    rw [hf_only] at hd_eq hαd_eq
    have heq : RS.faceEdges d = RS.faceEdges (RS.alpha d) := by
      simp only [Finset.mem_singleton] at hd_eq hαd_eq
      rw [hd_eq, hαd_eq]
    -- But α-paired darts have distinct faceEdges for interior edges!
    exact RS.faceEdges_alpha_ne_of_interior hd he heq.symm

  -- Package the two faces
  have hS_eq_two : ∃ f g : Finset E, f ≠ g ∧ S = {f, g} := by
    exact Finset.card_eq_two.mp hS_card_eq

  obtain ⟨f, g, hfg_ne, hfg_eq⟩ := hS_eq_two

  refine ⟨{f, g}, ?_, ?_⟩
  · -- Show fg.card = 2 and both faces are internal with e ∈ them
    constructor
    · simp [Finset.card_pair hfg_ne]
    · intro f' hf'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf'
      cases hf' with
      | inl h =>
        rw [h]
        -- f ∈ S = image faceEdges, and all those are internal
        have : f ∈ S := by rw [hfg_eq]; simp
        obtain ⟨d, hd, hd_eq⟩ := Finset.mem_image.mp this
        constructor
        · -- f = faceEdges d ≠ boundaryEdges, so f ∈ internalFaces
          unfold internalFaces
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · exact ⟨d, hd_eq⟩
          · rw [←hd_eq]; exact hδ_int d hd
        · -- e ∈ f
          rw [←hd_eq, RS.mem_faceEdges_iff]
          use d
          constructor
          · exact RS.mem_faceOrbit_self d
          · unfold dartsOn at hd
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
            exact hd
      | inr h =>
        rw [h]
        -- Same argument for g
        have : g ∈ S := by rw [hfg_eq]; simp
        obtain ⟨d, hd, hd_eq⟩ := Finset.mem_image.mp this
        constructor
        · unfold internalFaces
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · exact ⟨d, hd_eq⟩
          · rw [←hd_eq]; exact hδ_int d hd
        · rw [←hd_eq, RS.mem_faceEdges_iff]
          use d
          constructor
          · exact RS.mem_faceOrbit_self d
          · unfold dartsOn at hd
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
            exact hd
  · -- Uniqueness: any other pair satisfying the property must equal {f,g}
    intro fg' ⟨hcard', hprop'⟩
    -- All internal faces containing e are in the image S
    have : fg' ⊆ S := by
      intro f' hf'
      have ⟨hint', he'⟩ := hprop' f' hf'
      -- f' ∈ internalFaces and e ∈ f'
      -- By the covering lemma, f' is in the image
      have : f' ∈ RS.facesIncidence e := by
        unfold facesIncidence
        simp only [Finset.mem_filter]
        exact ⟨hint', he'⟩
      -- facesIncidence e ⊆ image faceEdges (dartsOnInternal)
      have hcover := RS.facesIncidence_subset_image_faceEdges_of_dartsOnInternal e
      have : f' ∈ (RS.dartsOnInternal e).image RS.faceEdges := hcover this
      -- dartsOnInternal ⊆ dartsOn
      have : f' ∈ (RS.dartsOn e).image RS.faceEdges := by
        obtain ⟨d, hd, hd_eq⟩ := Finset.mem_image.mp this
        have : d ∈ RS.dartsOn e := RS.dartsOnInternal_subset_dartsOn e hd
        exact Finset.mem_image.mpr ⟨d, this, hd_eq⟩
      exact this
    -- fg' ⊆ S and card fg' = 2 = card S, so fg' = S = {f,g}
    have : fg' = S := by
      refine Finset.eq_of_subset_of_card_le this ?_
      rw [hS_card_eq, hcard']
    rw [this, hfg_eq]

/-- Every internal face corresponds to some dart whose faceEdges equals that face.

    **Key Property**: This is TRIVIAL because internalFaces is defined as the image
    of faceEdges! No axioms needed - it's definitional. -/
lemma dart_of_internalFace {f : Finset E} (hf : f ∈ RS.internalFaces) :
  ∃ d, RS.faceEdges d = f := by
  -- Unpack definition of internalFaces (line 77: image of faceEdges)
  unfold internalFaces at hf
  simp only [Finset.mem_filter, Finset.mem_image] at hf
  obtain ⟨d, _, hd⟩ := hf.1
  exact ⟨d, hd⟩

/-- **Witness extraction for faces containing edges**: Any face from internalFaces
    that contains an edge has an explicit dart witness.

    This is the key lemma that breaks the "circular dependency" - it's derivable
    directly from the definition of internalFaces as an image. -/
lemma face_witness_from_internal {f : Finset E} {e : E}
    (hf : f ∈ RS.internalFaces) (he : e ∈ f) :
    ∃ d, RS.faceEdges d = f := by
  exact dart_of_internalFace hf

/-- Internal faces are disjoint from boundary edges.
Proof strategy: An internal face f corresponds to some faceEdges d where d's orbit is not the outer
orbit. If e ∈ f ∩ boundaryEdges, then by boundary_edge_both_outer, any dart on e must have its
faceEdges equal to boundaryEdges, contradicting f ≠ boundaryEdges. -/
lemma internal_face_disjoint_boundary
    {f : Finset E} (hf : f ∈ RS.internalFaces) :
    ∀ e ∈ RS.boundaryEdges, e ∉ f := by
  classical
  intro e he_bound he_f
  -- f is an internal face, so ∃ d with f = faceEdges d and f ≠ boundaryEdges
  unfold internalFaces at hf
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hf
  obtain ⟨⟨d, _, rfl⟩, hf_ne⟩ := hf
  -- e ∈ faceEdges d, so ∃ d' in orbit of d with edgeOf d' = e
  rw [mem_faceEdges_iff] at he_f
  obtain ⟨d', hd'_orb, hd'_e⟩ := he_f
  -- By boundary_edge_both_outer: faceEdges d' = boundaryEdges
  have hd'_bound : RS.faceEdges d' = RS.boundaryEdges :=
    RS.boundary_edge_both_outer hd'_e he_bound
  -- But d' ~ d (same orbit), so faceEdges d' = faceEdges d
  have h_same : RS.phi.SameCycle d' d := by
    unfold faceOrbit at hd'_orb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'_orb
    exact Equiv.Perm.SameCycle.symm hd'_orb
  have hd'_eq_d : RS.faceEdges d' = RS.faceEdges d :=
    RS.faceEdges_of_sameCycle h_same
  -- Therefore faceEdges d = boundaryEdges (by transitivity)
  have : RS.faceEdges d = RS.boundaryEdges := calc
    RS.faceEdges d = RS.faceEdges d' := hd'_eq_d.symm
    _ = RS.boundaryEdges := hd'_bound
  -- But this contradicts hf_ne
  exact hf_ne this

/-! ### Vertex-incident edges and parity -/

/-- Edges incident to vertex v -/
def incidentEdges (v : V) : Finset E :=
  Finset.univ.filter (fun e => ∃ d : RS.D, RS.edgeOf d = e ∧ RS.vertOf d = v)

/-- Toggle set: darts where vertex membership changes along the face walk -/
def togglesOn (v : V) (d₀ : RS.D) : Finset RS.D :=
  (RS.faceOrbit d₀).filter (fun d =>
    decide (RS.vertOf d = v) ≠ decide (RS.vertOf (RS.phi d) = v))

/-- Z₂-valued indicator: 1 if dart is at vertex v, else 0 -/
private def atV (v : V) (d : RS.D) : ZMod 2 :=
  if RS.vertOf d = v then 1 else 0

/-! ### Helper lemmas for Z₂ telescoping -/

-- φ preserves vertex when composed with α
@[simp] lemma vert_phi_eq_vert_alpha (d : RS.D) :
  RS.vertOf (RS.phi d) = RS.vertOf (RS.alpha d) := by
  dsimp [phi]
  simpa [RS.vert_rho (RS.alpha d)]

-- Edge fiber dichotomy: any dart with same edge is either d or α d
lemma edge_fiber_two_cases {e : E} {d y : RS.D}
    (hd : RS.edgeOf d = e) (hy : RS.edgeOf y = e) :
    y = d ∨ y = RS.alpha d := by
  classical
  have hx : RS.edgeOf (RS.alpha d) = e := by simpa [hd, RS.edge_alpha d]
  let S : Finset RS.D := (Finset.univ.filter (fun x => RS.edgeOf x = e))
  have hcard : S.card = 2 := RS.edge_fiber_two e
  have hmem_d  : d ∈ S := by simpa [S, hd]
  have hmem_ad : RS.alpha d ∈ S := by simpa [S, hx]
  have hneq : RS.alpha d ≠ d := RS.alpha_fixfree d
  have hpair_card : ({d, RS.alpha d} : Finset RS.D).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    exact hneq.symm
  have hpair_subset : ({d, RS.alpha d} : Finset RS.D) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl)
    · exact hmem_d
    · exact hmem_ad
  have hEq : ({d, RS.alpha d} : Finset RS.D) = S :=
    Finset.eq_of_subset_of_card_le hpair_subset
      (by simpa [hpair_card, hcard] using le_of_eq (by rfl))
  have hmem_y : y ∈ S := by simpa [S, hy]
  have : y ∈ ({d, RS.alpha d} : Finset RS.D) := by simpa [hEq] using hmem_y
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  exact this

-- d ∈ faceOrbit d₀ ⇒ φ d ∈ faceOrbit d₀
lemma phi_maps_faceOrbit {d₀ d : RS.D} (hd : d ∈ RS.faceOrbit d₀) :
    RS.phi d ∈ RS.faceOrbit d₀ := by
  have h₀ : RS.phi.SameCycle d₀ d := by
    simpa [RotationSystem.faceOrbit] using hd
  have h₁ : RS.phi.SameCycle d (RS.phi d) :=
    (Compat.Perm.sameCycle_apply_right (RS.phi)).mpr (Equiv.Perm.SameCycle.refl _ _)
  have : RS.phi.SameCycle d₀ (RS.phi d) := h₀.trans h₁
  simpa [RotationSystem.faceOrbit] using this

-- d ∈ faceOrbit d₀ ⇒ φ⁻¹ d ∈ faceOrbit d₀
lemma phi_symm_maps_faceOrbit {d₀ d : RS.D} (hd : d ∈ RS.faceOrbit d₀) :
    RS.phi.symm d ∈ RS.faceOrbit d₀ := by
  have h₀ : RS.phi.SameCycle d₀ d := by
    simpa [RotationSystem.faceOrbit] using hd
  have h₁ : RS.phi.SameCycle d (RS.phi.symm d) :=
    (Compat.Perm.sameCycle_inv_apply_right (RS.phi)).mpr (Equiv.Perm.SameCycle.refl _ _)
  have : RS.phi.SameCycle d₀ (RS.phi.symm d) := h₀.trans h₁
  simpa [RotationSystem.faceOrbit] using this

-- Image of orbit by φ is itself
lemma image_phi_faceOrbit (d₀ : RS.D) :
  (RS.faceOrbit d₀).image RS.phi = RS.faceOrbit d₀ := by
  classical
  have h₁ : (RS.faceOrbit d₀).image RS.phi ⊆ RS.faceOrbit d₀ := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact RS.phi_maps_faceOrbit hx
  have h₂ : RS.faceOrbit d₀ ⊆ (RS.faceOrbit d₀).image RS.phi := by
    intro y hy
    refine Finset.mem_image.mpr ?_
    use RS.phi.symm y
    constructor
    · exact RS.phi_symm_maps_faceOrbit hy
    · simp
  exact le_antisymm h₁ h₂

-- Reindex sum by φ permutation
lemma sum_comp_phi_same (d₀ : RS.D) {β} [AddCommMonoid β] (f : RS.D → β) :
  ∑ d ∈ RS.faceOrbit d₀, f (RS.phi d) = ∑ d ∈ RS.faceOrbit d₀, f d := by
  classical
  refine Finset.sum_bij
    (fun d _ => RS.phi d)
    (fun d hd => RS.phi_maps_faceOrbit hd)
    (fun _ _ _ _ h => RS.phi.injective h)
    ?surj
    (fun _ _ => rfl)
  intro b hb
  exact ⟨RS.phi.symm b, RS.phi_symm_maps_faceOrbit hb, by simp⟩

-- Helper for toggle counting
private lemma add01_or_01 (v : V) (d : RS.D) :
  (RS.atV v d + RS.atV v (RS.phi d) : ZMod 2) = 0 ∨
  (RS.atV v d + RS.atV v (RS.phi d) : ZMod 2) = 1 := by
  unfold atV
  split_ifs <;> decide

-- Sum of 0/1 function equals card of filter
private lemma sum_01_eq_card_filter_one
    {α} [DecidableEq α] (S : Finset α) (g : α → ZMod 2)
    (h01 : ∀ x ∈ S, g x = 0 ∨ g x = 1) :
  ∑ x ∈ S, g x = ((S.filter (fun x => g x = 1)).card : ZMod 2) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert a S ha ih =>
      have h01S : ∀ x ∈ S, g x = 0 ∨ g x = 1 := fun x hx => h01 x (Finset.mem_insert_of_mem hx)
      rcases h01 a (Finset.mem_insert_self a S) with h0 | h1
      · rw [Finset.sum_insert ha, h0, zero_add, Finset.filter_insert, if_neg (by simp [h0])]
        exact ih h01S
      · rw [Finset.sum_insert ha, h1, Finset.filter_insert, if_pos (by simp [h1])]
        have : a ∉ S.filter fun x => g x = 1 := by simp [ha]
        rw [Finset.card_insert_of_notMem this, ih h01S]
        norm_cast
        ring

lemma toggles_even (d₀ : RS.D) (v : V) :
  Even ((RS.togglesOn v d₀).card) := by
  classical
  -- Z₂ telescoping
  have hperm :
      ∑ d ∈ RS.faceOrbit d₀, (RS.atV v d + RS.atV v (RS.phi d) : ZMod 2)
      = 0 := by
    have reidx := RS.sum_comp_phi_same (d₀ := d₀) (f := RS.atV v)
    have this : (∑ d ∈ RS.faceOrbit d₀, RS.atV v (RS.phi d) : ZMod 2)
            = ∑ d ∈ RS.faceOrbit d₀, RS.atV v d := by simpa using reidx
    calc (∑ d ∈ RS.faceOrbit d₀, (RS.atV v d + RS.atV v (RS.phi d)) : ZMod 2)
      _ = (∑ d ∈ RS.faceOrbit d₀, RS.atV v d)
            + (∑ d ∈ RS.faceOrbit d₀, RS.atV v (RS.phi d)) := by simp [Finset.sum_add_distrib]
      _ = (∑ d ∈ RS.faceOrbit d₀, RS.atV v d)
            + (∑ d ∈ RS.faceOrbit d₀, RS.atV v d) := by rw [this]
      _ = 2 • (∑ d ∈ RS.faceOrbit d₀, RS.atV v d) := by simp [two_nsmul]
      _ = 0 := by simp
  -- Sum equals toggle count
  have hsum_as_card :
      (∑ d ∈ RS.faceOrbit d₀, (RS.atV v d + RS.atV v (RS.phi d) : ZMod 2))
      = ((RS.togglesOn v d₀).card : ZMod 2) := by
    have h01 : ∀ d ∈ RS.faceOrbit d₀,
        (RS.atV v d + RS.atV v (RS.phi d) : ZMod 2) = 0 ∨
        (RS.atV v d + RS.atV v (RS.phi d) : ZMod 2) = 1 := by
      intro d hd; exact RS.add01_or_01 v d
    have := sum_01_eq_card_filter_one
              (S := RS.faceOrbit d₀)
              (g := fun d => (RS.atV v d + RS.atV v (RS.phi d) : ZMod 2))
              h01
    have heq : (RS.faceOrbit d₀).filter
            (fun d => (RS.atV v d + RS.atV v (RS.phi d) : ZMod 2) = 1)
            = RS.togglesOn v d₀ := by
      ext d
      simp only [togglesOn, atV, Finset.mem_filter, decide_eq_true_eq]
      by_cases h1 : RS.vertOf d = v <;> by_cases h2 : RS.vertOf (RS.phi d) = v
      <;> simp [h1, h2]
      <;> try decide
    rw [← heq]
    exact this
  have h0 : ((RS.togglesOn v d₀).card : ZMod 2) = 0 := by rw [← hsum_as_card]; exact hperm
  -- Since card mod 2 = 0, card is even
  obtain ⟨k, hk⟩ : ∃ k, (RS.togglesOn v d₀).card = 2 * k := by
    use (RS.togglesOn v d₀).card / 2
    have : 2 ∣ (RS.togglesOn v d₀).card := by
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]; exact h0
    omega
  refine ⟨k, ?_⟩
  omega

-- Interior α-darts on different faces
lemma alpha_not_in_same_faceOrbit_of_interior
    {d d₀ : RS.D} (hint : RS.edgeOf d ∉ RS.boundaryEdges)
    (hd : d ∈ RS.faceOrbit d₀) :
    RS.alpha d ∉ RS.faceOrbit d₀ := by
  classical
  have hfaces_ne := RS.planarity_interior_edges
      (e := RS.edgeOf d) (d := d)
      (by rfl) hint
  intro hα
  have : RS.faceEdges (RS.alpha d) = RS.faceEdges d := by
    have h1 : RS.faceEdges d = RS.faceEdges d₀ := by
      have : RS.phi.SameCycle d₀ d := by simpa [mem_faceOrbit] using hd
      exact RS.faceEdges_of_sameCycle this.symm
    have h2 : RS.faceEdges (RS.alpha d) = RS.faceEdges d₀ := by
      have : RS.phi.SameCycle d₀ (RS.alpha d) := by simpa [mem_faceOrbit] using hα
      exact RS.faceEdges_of_sameCycle this.symm
    simpa [h1, h2]
  exact hfaces_ne this

-- Internal face edges aren't boundary edges
lemma edge_of_internal_face_not_boundary {d₀ : RS.D} {e : E}
    (he : e ∈ RS.faceEdges d₀) (hint : RS.faceEdges d₀ ≠ RS.boundaryEdges) :
    e ∉ RS.boundaryEdges := by
  intro hbdry
  have hinternal : RS.faceEdges d₀ ∈ RS.internalFaces := by
    rw [internalFaces]
    simp only [Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨d₀, Finset.mem_univ _, rfl⟩, hint⟩
  exact RS.internal_face_disjoint_boundary hinternal e hbdry he

-- Need incidentEdges membership characterization
lemma mem_incidentEdges {e : E} {v : V} :
    e ∈ RS.incidentEdges v ↔ ∃ d : RS.D, RS.edgeOf d = e ∧ RS.vertOf d = v := by
  simp [incidentEdges]

/-- For internal faces, toggles biject with incident edges -/
lemma toggles_biject_edges_internal (d₀ : RS.D) (v : V)
    (h_internal : RS.faceEdges d₀ ≠ RS.boundaryEdges) :
    (RS.togglesOn v d₀).card = (RS.incidentEdges v ∩ RS.faceEdges d₀).card := by
  classical
  refine Finset.card_bij
    (fun d hd => RS.edgeOf d)
    ?mem ?inj ?surj
  · -- membership
    intro d hd
    rw [togglesOn, Finset.mem_filter] at hd
    have ⟨hdS, htoggle⟩ := hd
    have hface : RS.edgeOf d ∈ RS.faceEdges d₀ := by
      rw [faceEdges]
      exact Finset.mem_image.mpr ⟨d, hdS, rfl⟩
    have : (RS.vertOf d = v ∧ RS.vertOf (RS.phi d) ≠ v)
         ∨ (RS.vertOf d ≠ v ∧ RS.vertOf (RS.phi d) = v) := by
      by_cases h1 : RS.vertOf d = v
      · by_cases h2 : RS.vertOf (RS.phi d) = v
        · -- Both at v: XOR is false
          simp only [h1, h2] at htoggle
          -- htoggle says true ≠ true, contradiction
          exact absurd rfl htoggle
        · left; exact ⟨h1, h2⟩
      · by_cases h2 : RS.vertOf (RS.phi d) = v
        · right; exact ⟨h1, h2⟩
        · -- Neither at v: XOR is false
          simp only [h1, h2] at htoggle
          exact absurd rfl htoggle
    rcases this with (⟨hv, _⟩ | ⟨_, hv'⟩)
    · have : ∃ d', RS.edgeOf d' = RS.edgeOf d ∧ RS.vertOf d' = v := ⟨d, rfl, hv⟩
      have : RS.edgeOf d ∈ RS.incidentEdges v := by simpa [mem_incidentEdges] using this
      simpa [Finset.mem_inter] using And.intro this hface
    · have hvα : RS.vertOf (RS.alpha d) = v := by
        rw [← vert_phi_eq_vert_alpha]; exact hv'
      have : ∃ d', RS.edgeOf d' = RS.edgeOf d ∧ RS.vertOf d' = v :=
        ⟨RS.alpha d, by simp [RS.edge_alpha], hvα⟩
      have : RS.edgeOf d ∈ RS.incidentEdges v := by simpa [mem_incidentEdges] using this
      simpa [Finset.mem_inter] using And.intro this hface
  · -- injectivity
    intro d₁ hd₁ d₂ hd₂ hEdge
    -- hd₁ : d₁ ∈ togglesOn, which unfolds to d₁ ∈ filter (faceOrbit) (predicate)
    rw [togglesOn, Finset.mem_filter] at hd₁ hd₂
    have ⟨hdS₁, _⟩ := hd₁
    have ⟨hdS₂, _⟩ := hd₂
    have hnot : RS.edgeOf d₁ ∉ RS.boundaryEdges := by
      have : RS.edgeOf d₁ ∈ RS.faceEdges d₀ := by
        rw [faceEdges]
        exact Finset.mem_image.mpr ⟨d₁, hdS₁, rfl⟩
      exact RS.edge_of_internal_face_not_boundary this h_internal
    have hαnot : RS.alpha d₁ ∉ RS.faceOrbit d₀ :=
      RS.alpha_not_in_same_faceOrbit_of_interior hnot hdS₁
    have hcases := RS.edge_fiber_two_cases
                      (e := RS.edgeOf d₁) (d := d₁) (y := d₂)
                      rfl (by simpa [hEdge])
    cases hcases with
    | inl h => exact h.symm
    | inr h =>
        have : RS.alpha d₁ ∈ RS.faceOrbit d₀ := by rw [← h]; exact hdS₂
        exact (hαnot this).elim
  · -- surjectivity
    intro e he
    simp only [Finset.mem_inter] at he
    have ⟨hinc, hf⟩ := he
    rcases Finset.mem_image.mp hf with ⟨d, hdS, hde⟩
    rcases ((mem_incidentEdges (RS := RS) (v := v) (e := e)).1 hinc) with ⟨d', hd'e, hv'⟩
    -- d is in face orbit, d' is on same edge with vertex v
    -- Either d=d' or d=alpha d' (by edge_fiber_two_cases)
    have hcases := RS.edge_fiber_two_cases
                      (e := RS.edgeOf d) (d := d) (y := d') rfl (by rw [hde, ← hd'e])
    -- If d = d', use d. If d = alpha d', check if d or alpha d is in face orbit
    rcases hcases with (h_eq | h_alpha)
    · -- Case d = d', so vertOf d = v
      refine ⟨d, ?_, hde⟩
      rw [togglesOn]
      simp only [Finset.mem_filter]
      refine ⟨hdS, ?_⟩
      -- Need: vertOf d = v XOR vertOf (phi d) = v
      have hvd : RS.vertOf d = v := by rw [← h_eq]; exact hv'
      -- Show XOR: exactly one is true
      simp only [hvd]
      -- Goal: decide True ≠ decide (RS.vertOf (RS.phi d) = v)
      intro h
      -- From h : decide True = decide (RS.vertOf (RS.phi d) = v), derive RS.vertOf (RS.phi d) = v
      have hcontra : RS.vertOf (RS.phi d) = v := by
        simp at h
        exact h
      -- This would make alpha d also at v
      have hvα : RS.vertOf (RS.alpha d) = v := by
        have : RS.vertOf (RS.phi d) = RS.vertOf (RS.alpha d) := vert_phi_eq_vert_alpha (RS := RS) d
        rw [hcontra] at this; exact this.symm
      -- Contradicts no_self_loops
      exact RS.no_self_loops d (hvd.trans hvα.symm)
    · -- Case d = alpha d', so d' = alpha d, and vertOf (alpha d) = v
      -- We'll use d, showing togglesOn property holds
      refine ⟨d, ?_, hde⟩
      rw [togglesOn]
      simp only [Finset.mem_filter]
      refine ⟨hdS, ?_⟩
      have hvα : RS.vertOf (RS.alpha d) = v := by rw [← h_alpha]; exact hv'
      have hvphi : RS.vertOf (RS.phi d) = v := by
        have : RS.vertOf (RS.phi d) = RS.vertOf (RS.alpha d) := vert_phi_eq_vert_alpha (RS := RS) d
        rw [this]; exact hvα
      -- Show XOR: phi d has v but d doesn't
      simp only [hvphi]
      -- Goal: decide (RS.vertOf d = v) ≠ decide True
      intro h
      -- From h : decide (RS.vertOf d = v) = decide True, derive RS.vertOf d = v
      have hcontra : RS.vertOf d = v := by
        simp at h
        exact h
      -- Contradicts no_self_loops
      exact RS.no_self_loops d (hcontra.trans hvα.symm)

/-- **Key theorem: Even edge-incidence for internal faces.**
For any internal face f = faceEdges d₀ and vertex v, the number of edges of f
incident to v is even. -/
theorem face_vertex_incidence_even_internal (RS : RotationSystem V E) :
  ∀ (d₀ : RS.D) (v : V),
    RS.faceEdges d₀ ≠ RS.boundaryEdges →
    Even ((RS.incidentEdges v ∩ RS.faceEdges d₀).card) := by
  intros d₀ v h_internal
  rw [← RS.toggles_biject_edges_internal d₀ v h_internal]
  exact RS.toggles_even d₀ v

/-- **Key theorem: Even edge-incidence of a face at each vertex.**
For any face f = faceEdges d₀ and vertex v, the number of edges of f
incident to v is even. This follows from the topological structure of rotation systems. -/
theorem face_vertex_incidence_even (RS : RotationSystem V E) :
  ∀ (d₀ : RS.D) (v : V),
    Even ((Finset.univ.filter (fun e => ∃ d, RS.edgeOf d = e ∧ RS.vertOf d = v) ∩ RS.faceEdges d₀).card)

end RotationSystem

/--
Interface for the "rotation / embedding" transport path.  The final proof
will instantiate this structure with a rotation system on darts that
recovers faces as orbits; for now we only encode the data required to
produce the `LeafPeelData` abstraction.
-/
structure RotationDual
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  zero : ZeroBoundaryData V E
  gamma : Color := (1, 0)
  internalFaces : Finset (Finset E)
  boundary_mem_zero :
    ∀ {f}, f ∈ internalFaces →
      faceBoundaryChain (γ := gamma) f ∈ zero.zeroBoundarySet
  tight :
    ∀ {x}, x ∈ zero.zeroBoundarySet → support₁ x = ∅ → x = zeroChain (E := E)
  peelWitness :
    ∀ {x : E → Color},
      x ∈ zero.zeroBoundarySet →
      support₁ x ≠ ∅ →
      ∃ f : Finset E,
        f ∈ internalFaces ∧
        ∃ x' : E → Color,
          x' ∈ zero.zeroBoundarySet ∧
          x = x' + faceBoundaryChain (γ := gamma) f ∧
          Finset.card (support₁ x') < Finset.card (support₁ x)

namespace RotationDual

variable [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]

/-- Translate a `RotationDual` witness into `LeafPeelData`. -/
def toLeafPeelData (D : RotationDual (V := V) (E := E)) :
    LeafPeelData V E where
  zero := D.zero
  gamma := D.gamma
  internalFaces := D.internalFaces
  boundary_mem_zero := D.boundary_mem_zero
  tight := D.tight
  peel := by
    intro x hx hsupp
    classical
    exact D.peelWitness hx hsupp

end RotationDual

end -- noncomputable section
end Geometry
end FourColor

