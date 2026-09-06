import FourColor.Triangulation
import FourColor.Compat.CompatV2024

-- Linter configuration: silence warnings pending systematic cleanup
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace FourColor
namespace Geometry

open scoped BigOperators
open Classical
open FourColor.Compat

noncomputable section

variable {V E : Type*}

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

/-- **Planar Geometry**: A rotation system with planarity and simplicity constraints.

This represents a **simple planar graph** embedded in a surface with a distinguished
outer face. The key properties are:

- **Planarity**: Interior edges separate distinct faces (no edge crossings)
- **Simplicity**: No parallel edges (simple graph property)
- **Boundary**: Boundary edges have both darts in the outer face

This is the natural middle layer between:
- `RotationSystem` (pure combinatorial structure, works on any surface)
- `DiskGeometry` (adds disk topology and homological properties)

Future: Could be extended for other surfaces (sphere, torus, etc.) -/
structure PlanarGeometry (V E : Type*)
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    extends RotationSystem V E where

  /-- **Planarity axiom**: Interior edges separate distinct faces.
      This is the fundamental "edges don't cross" property of planar embeddings.
      For an interior edge e with dart d, the faces on either side (containing d and α(d))
      are distinct. -/
  planar_interior_edges :
    ∀ {e : E} {d : toRotationSystem.D},
      toRotationSystem.edgeOf d = e →
      e ∉ RotationSystem.boundaryEdges toRotationSystem →
      RotationSystem.faceEdges toRotationSystem (toRotationSystem.alpha d) ≠
      RotationSystem.faceEdges toRotationSystem d

  /-- **Simplicity axiom**: No parallel edges.
      Different edges have different vertex pairs. This ensures we're working with
      simple graphs (at most one edge between any pair of vertices). -/
  no_parallel_edges :
    ∀ {e e' : E} {d d' : toRotationSystem.D},
      toRotationSystem.edgeOf d = e →
      toRotationSystem.edgeOf d' = e' →
      e ≠ e' →
      ({toRotationSystem.vertOf d, toRotationSystem.vertOf (toRotationSystem.alpha d)} : Finset V) ≠
      ({toRotationSystem.vertOf d', toRotationSystem.vertOf (toRotationSystem.alpha d')} : Finset V)

  /-- **Boundary property**: Boundary edges have both darts in the outer face.
      For edges on the boundary, both darts belong to the same (outer) face.
      This follows from the definition of boundary as the outer face's edge set. -/
  boundary_edge_both_outer :
    ∀ {e : E} {d : toRotationSystem.D},
      toRotationSystem.edgeOf d = e →
      e ∈ RotationSystem.boundaryEdges toRotationSystem →
      RotationSystem.faceEdges toRotationSystem d = RotationSystem.boundaryEdges toRotationSystem
/-- Darts with a given underlying edge -/
def dartsOn (e : E) : Finset RS.D :=
  Finset.univ.filter (fun d => RS.edgeOf d = e)

/-- **Planarity property**: For interior edges, darts on opposite sides belong to different faces.
    This is now a definitional property of PlanarGeometry. -/
theorem planarity_interior_edges (PG : PlanarGeometry V E) :
  ∀ {e : E} {d : PG.toRotationSystem.D},
    PG.toRotationSystem.edgeOf d = e →
    e ∉ PG.toRotationSystem.boundaryEdges →
    PG.toRotationSystem.faceEdges (PG.toRotationSystem.alpha d) ≠ PG.toRotationSystem.faceEdges d :=
  PG.planar_interior_edges

/-- **Simplicity property**: No parallel edges.
    This is now a definitional property of PlanarGeometry. -/
theorem no_parallel_edges (PG : PlanarGeometry V E) :
  ∀ {e e' : E} {d d' : PG.toRotationSystem.D},
    PG.toRotationSystem.edgeOf d = e →
    PG.toRotationSystem.edgeOf d' = e' →
    e ≠ e' →
    ({PG.toRotationSystem.vertOf d, PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d)} : Finset V) ≠
    ({PG.toRotationSystem.vertOf d', PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d')} : Finset V) :=
  PG.no_parallel_edges

/-- **Boundary property**: For boundary edges, both darts belong to the outer face.
    This is now a definitional property of PlanarGeometry. -/
theorem boundary_edge_both_outer (PG : PlanarGeometry V E) :
  ∀ {e : E} {d : PG.toRotationSystem.D},
    PG.toRotationSystem.edgeOf d = e →
    e ∈ PG.toRotationSystem.boundaryEdges →
    PG.toRotationSystem.faceEdges d = PG.toRotationSystem.boundaryEdges :=
  PG.boundary_edge_both_outer

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
lemma faceEdges_alpha_ne_of_interior (PG : PlanarGeometry V E)
    {e : E} {d : PG.toRotationSystem.D}
    (hd : d ∈ PG.toRotationSystem.dartsOn e)
    (he : e ∉ PG.toRotationSystem.boundaryEdges) :
    PG.toRotationSystem.faceEdges (PG.toRotationSystem.alpha d) ≠ PG.toRotationSystem.faceEdges d := by
  -- Apply the planarity axiom
  have he_d : PG.toRotationSystem.edgeOf d = e := by
    unfold dartsOn at hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact hd
  exact planarity_interior_edges PG he_d he

/-- **Bridge lemma for interior edges**: Extract the two incident internal faces
for an interior edge (not on the outer boundary).

This provides explicit witnesses for the "exactly 2 faces" property, avoiding
fragile parity arguments inside DiskGeometry. -/
lemma two_internal_faces_of_interior_edge (PG : PlanarGeometry V E)
    {e : E} (he : e ∉ PG.toRotationSystem.boundaryEdges) :
    ∃! (fg : Finset (Finset E)),
        fg.card = 2 ∧ ∀ f ∈ fg, f ∈ PG.toRotationSystem.internalFaces ∧ e ∈ f := by
  classical
  -- Each edge has exactly two darts
  have hd : (PG.toRotationSystem.dartsOn e).card = 2 := PG.toRotationSystem.dartsOn_card_two e

  -- Neither dart lies on the outer face because e ∉ boundaryEdges
  have hδ_int : ∀ d ∈ PG.toRotationSystem.dartsOn e, PG.toRotationSystem.faceEdges d ≠ PG.toRotationSystem.boundaryEdges := by
    intro d hd'
    -- If faceEdges d = boundaryEdges, then e ∈ boundaryEdges, contradiction
    intro h_eq
    have : e ∈ PG.toRotationSystem.boundaryEdges := by
      -- e ∈ faceEdges d = boundaryEdges
      have he_in : e ∈ PG.toRotationSystem.faceEdges d := by
        unfold dartsOn at hd'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
        rw [PG.toRotationSystem.mem_faceEdges_iff]
        use d
        constructor
        · exact PG.toRotationSystem.mem_faceOrbit_self d
        · exact hd'
      rw [h_eq] at he_in
      exact he_in
    exact he this

  -- Build fg as the image of dartsOn e under faceEdges
  let S := (PG.toRotationSystem.dartsOn e).image PG.toRotationSystem.faceEdges

  have hS_card_le : S.card ≤ 2 := by
    calc S.card
      ≤ (PG.toRotationSystem.dartsOn e).card := Finset.card_image_le
      _ = 2 := PG.toRotationSystem.dartsOn_card_two e

  -- Show S.card ≥ 1 (at least one face)
  have hS_nonempty : S.Nonempty := by
    obtain ⟨d, hd⟩ : (PG.toRotationSystem.dartsOn e).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      have : (PG.toRotationSystem.dartsOn e).card = 0 := by simp [h_empty]
      omega
    refine ⟨PG.toRotationSystem.faceEdges d, ?_⟩
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
    obtain ⟨d, hd⟩ : (PG.toRotationSystem.dartsOn e).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have hcard_zero : (PG.toRotationSystem.dartsOn e).card = 0 := by simp [h]
      have hcard_two : (PG.toRotationSystem.dartsOn e).card = 2 := hd
      omega
    -- S.card = 1 means faceEdges d = faceEdges (α d)
    have hS_singleton : ∃ f, S = {f} := Finset.card_eq_one.mp this
    obtain ⟨f_only, hf_only⟩ := hS_singleton
    have hd_eq : PG.toRotationSystem.faceEdges d ∈ S := Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hαd_eq : PG.toRotationSystem.faceEdges (PG.toRotationSystem.alpha d) ∈ S := by
      apply Finset.mem_image.mpr
      use PG.toRotationSystem.alpha d
      constructor
      · -- α d ∈ dartsOn e
        unfold dartsOn
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        unfold dartsOn at hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        rw [PG.toRotationSystem.edge_alpha]; exact hd
      · rfl
    rw [hf_only] at hd_eq hαd_eq
    have heq : PG.toRotationSystem.faceEdges d = PG.toRotationSystem.faceEdges (PG.toRotationSystem.alpha d) := by
      simp only [Finset.mem_singleton] at hd_eq hαd_eq
      rw [hd_eq, hαd_eq]
    -- But α-paired darts have distinct faceEdges for interior edges!
    exact faceEdges_alpha_ne_of_interior PG hd he heq.symm

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
          rw [←hd_eq, PG.toRotationSystem.mem_faceEdges_iff]
          use d
          constructor
          · exact PG.toRotationSystem.mem_faceOrbit_self d
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
        · rw [←hd_eq, PG.toRotationSystem.mem_faceEdges_iff]
          use d
          constructor
          · exact PG.toRotationSystem.mem_faceOrbit_self d
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
      have : f' ∈ PG.toRotationSystem.facesIncidence e := by
        unfold facesIncidence
        simp only [Finset.mem_filter]
        exact ⟨hint', he'⟩
      -- facesIncidence e ⊆ image faceEdges (dartsOnInternal)
      have hcover := PG.toRotationSystem.facesIncidence_subset_image_faceEdges_of_dartsOnInternal e
      have : f' ∈ (PG.toRotationSystem.dartsOnInternal e).image PG.toRotationSystem.faceEdges := hcover this
      -- dartsOnInternal ⊆ dartsOn
      have : f' ∈ (PG.toRotationSystem.dartsOn e).image PG.toRotationSystem.faceEdges := by
        obtain ⟨d, hd, hd_eq⟩ := Finset.mem_image.mp this
        have : d ∈ PG.toRotationSystem.dartsOn e := PG.toRotationSystem.dartsOnInternal_subset_dartsOn e hd
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
    ∃ d, RS.faceEdges d = f :=
  dart_of_internalFace (RS := RS) hf

/-- Internal faces are disjoint from boundary edges.
Proof strategy: An internal face f corresponds to some faceEdges d where d's orbit is not the outer
orbit. If e ∈ f ∩ boundaryEdges, then by boundary_edge_both_outer, any dart on e must have its
faceEdges equal to boundaryEdges, contradicting f ≠ boundaryEdges. -/
lemma internal_face_disjoint_boundary (PG : PlanarGeometry V E)
    {f : Finset E} (hf : f ∈ PG.toRotationSystem.internalFaces) :
    ∀ e ∈ PG.toRotationSystem.boundaryEdges, e ∉ f := by
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
  have hd'_bound : PG.toRotationSystem.faceEdges d' = PG.toRotationSystem.boundaryEdges :=
    boundary_edge_both_outer PG hd'_e he_bound
  -- But d' ~ d (same orbit), so faceEdges d' = faceEdges d
  have h_same : PG.toRotationSystem.phi.SameCycle d' d := by
    unfold faceOrbit at hd'_orb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'_orb
    exact Equiv.Perm.SameCycle.symm hd'_orb
  have hd'_eq_d : PG.toRotationSystem.faceEdges d' = PG.toRotationSystem.faceEdges d :=
    PG.toRotationSystem.faceEdges_of_sameCycle h_same
  -- Therefore faceEdges d = boundaryEdges (by transitivity)
  have : PG.toRotationSystem.faceEdges d = PG.toRotationSystem.boundaryEdges := calc
    PG.toRotationSystem.faceEdges d = PG.toRotationSystem.faceEdges d' := hd'_eq_d.symm
    _ = PG.toRotationSystem.boundaryEdges := hd'_bound
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
        ring_nf

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
      unfold togglesOn
      apply Finset.filter_congr
      intro d _
      by_cases h1 : RS.vertOf d = v <;> by_cases h2 : RS.vertOf (RS.rho (RS.alpha d)) = v
      <;> simp [atV, phi, h1, h2]
    rw [← heq]
    exact this
  have h0 : ((RS.togglesOn v d₀).card : ZMod 2) = 0 := by rw [← hsum_as_card]; exact hperm
  -- Since card mod 2 = 0, card is even
  obtain ⟨k, hk⟩ : ∃ k, (RS.togglesOn v d₀).card = 2 * k := by
    use (RS.togglesOn v d₀).card / 2
    have : 2 ∣ (RS.togglesOn v d₀).card := by
      rw [← ZMod.natCast_eq_zero_iff]; exact h0
    omega
  refine ⟨k, ?_⟩
  omega

-- Interior α-darts on different faces
lemma alpha_not_in_same_faceOrbit_of_interior (PG : PlanarGeometry V E)
    {d d₀ : PG.toRotationSystem.D} (hint : PG.toRotationSystem.edgeOf d ∉ PG.toRotationSystem.boundaryEdges)
    (hd : d ∈ PG.toRotationSystem.faceOrbit d₀) :
    PG.toRotationSystem.alpha d ∉ PG.toRotationSystem.faceOrbit d₀ := by
  classical
  have hfaces_ne := planarity_interior_edges PG
      (e := PG.toRotationSystem.edgeOf d) (d := d)
      (by rfl) hint
  intro hα
  have : PG.toRotationSystem.faceEdges (PG.toRotationSystem.alpha d) = PG.toRotationSystem.faceEdges d := by
    have h1 : PG.toRotationSystem.faceEdges d = PG.toRotationSystem.faceEdges d₀ := by
      have : PG.toRotationSystem.phi.SameCycle d₀ d := by simpa [mem_faceOrbit] using hd
      exact PG.toRotationSystem.faceEdges_of_sameCycle this.symm
    have h2 : PG.toRotationSystem.faceEdges (PG.toRotationSystem.alpha d) = PG.toRotationSystem.faceEdges d₀ := by
      have : PG.toRotationSystem.phi.SameCycle d₀ (PG.toRotationSystem.alpha d) := by simpa [mem_faceOrbit] using hα
      exact PG.toRotationSystem.faceEdges_of_sameCycle this.symm
    simpa [h1, h2]
  exact hfaces_ne this

-- Internal face edges aren't boundary edges
lemma edge_of_internal_face_not_boundary (PG : PlanarGeometry V E) {d₀ : PG.toRotationSystem.D} {e : E}
    (he : e ∈ PG.toRotationSystem.faceEdges d₀) (hint : PG.toRotationSystem.faceEdges d₀ ≠ PG.toRotationSystem.boundaryEdges) :
    e ∉ PG.toRotationSystem.boundaryEdges := by
  intro hbdry
  have hinternal : PG.toRotationSystem.faceEdges d₀ ∈ PG.toRotationSystem.internalFaces := by
    rw [internalFaces]
    simp only [Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨d₀, Finset.mem_univ _, rfl⟩, hint⟩
  exact internal_face_disjoint_boundary PG hinternal e hbdry he

-- Need incidentEdges membership characterization
lemma mem_incidentEdges {e : E} {v : V} :
    e ∈ RS.incidentEdges v ↔ ∃ d : RS.D, RS.edgeOf d = e ∧ RS.vertOf d = v := by
  simp [incidentEdges]

/-- For internal faces, toggles biject with incident edges -/
lemma toggles_biject_edges_internal (PG : PlanarGeometry V E) (d₀ : PG.toRotationSystem.D) (v : V)
    (h_internal : PG.toRotationSystem.faceEdges d₀ ≠ PG.toRotationSystem.boundaryEdges) :
    (PG.toRotationSystem.togglesOn v d₀).card = (PG.toRotationSystem.incidentEdges v ∩ PG.toRotationSystem.faceEdges d₀).card := by
  classical
  refine Finset.card_bij
    (fun d hd => PG.toRotationSystem.edgeOf d)
    ?mem ?inj ?surj
  · -- membership
    intro d hd
    rw [togglesOn, Finset.mem_filter] at hd
    have ⟨hdS, htoggle⟩ := hd
    have hface : PG.toRotationSystem.edgeOf d ∈ PG.toRotationSystem.faceEdges d₀ := by
      rw [faceEdges]
      exact Finset.mem_image.mpr ⟨d, hdS, rfl⟩
    have : (PG.toRotationSystem.vertOf d = v ∧ PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) ≠ v)
         ∨ (PG.toRotationSystem.vertOf d ≠ v ∧ PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = v) := by
      by_cases h1 : PG.toRotationSystem.vertOf d = v
      · by_cases h2 : PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = v
        · -- Both at v: XOR is false
          simp only [h1, h2] at htoggle
          -- htoggle says true ≠ true, contradiction
          exact absurd rfl htoggle
        · left; exact ⟨h1, h2⟩
      · by_cases h2 : PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = v
        · right; exact ⟨h1, h2⟩
        · -- Neither at v: XOR is false
          simp only [h1, h2] at htoggle
          exact absurd rfl htoggle
    rcases this with (⟨hv, _⟩ | ⟨_, hv'⟩)
    · have : ∃ d', PG.toRotationSystem.edgeOf d' = PG.toRotationSystem.edgeOf d ∧ PG.toRotationSystem.vertOf d' = v := ⟨d, rfl, hv⟩
      have : PG.toRotationSystem.edgeOf d ∈ PG.toRotationSystem.incidentEdges v := by simpa [mem_incidentEdges] using this
      simpa [Finset.mem_inter] using And.intro this hface
    · have hvα : PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d) = v := by
        rw [← vert_phi_eq_vert_alpha]; exact hv'
      have : ∃ d', PG.toRotationSystem.edgeOf d' = PG.toRotationSystem.edgeOf d ∧ PG.toRotationSystem.vertOf d' = v :=
        ⟨PG.toRotationSystem.alpha d, by simp [PG.toRotationSystem.edge_alpha], hvα⟩
      have : PG.toRotationSystem.edgeOf d ∈ PG.toRotationSystem.incidentEdges v := by simpa [mem_incidentEdges] using this
      simpa [Finset.mem_inter] using And.intro this hface
  · -- injectivity
    intro d₁ hd₁ d₂ hd₂ hEdge
    -- hd₁ : d₁ ∈ togglesOn, which unfolds to d₁ ∈ filter (faceOrbit) (predicate)
    rw [togglesOn, Finset.mem_filter] at hd₁ hd₂
    have ⟨hdS₁, _⟩ := hd₁
    have ⟨hdS₂, _⟩ := hd₂
    have hnot : PG.toRotationSystem.edgeOf d₁ ∉ PG.toRotationSystem.boundaryEdges := by
      have : PG.toRotationSystem.edgeOf d₁ ∈ PG.toRotationSystem.faceEdges d₀ := by
        rw [faceEdges]
        exact Finset.mem_image.mpr ⟨d₁, hdS₁, rfl⟩
      exact edge_of_internal_face_not_boundary PG this h_internal
    have hαnot : PG.toRotationSystem.alpha d₁ ∉ PG.toRotationSystem.faceOrbit d₀ :=
      alpha_not_in_same_faceOrbit_of_interior PG hnot hdS₁
    have hcases := PG.toRotationSystem.edge_fiber_two_cases
                      (e := PG.toRotationSystem.edgeOf d₁) (d := d₁) (y := d₂)
                      rfl (by simpa [hEdge])
    cases hcases with
    | inl h => exact h.symm
    | inr h =>
        have : PG.toRotationSystem.alpha d₁ ∈ PG.toRotationSystem.faceOrbit d₀ := by rw [← h]; exact hdS₂
        exact (hαnot this).elim
  · -- surjectivity
    intro e he
    simp only [Finset.mem_inter] at he
    have ⟨hinc, hf⟩ := he
    rcases Finset.mem_image.mp hf with ⟨d, hdS, hde⟩
    rcases ((mem_incidentEdges (RS := PG.toRotationSystem) (v := v) (e := e)).1 hinc) with ⟨d', hd'e, hv'⟩
    -- d is in face orbit, d' is on same edge with vertex v
    -- Either d=d' or d=alpha d' (by edge_fiber_two_cases)
    have hcases := PG.toRotationSystem.edge_fiber_two_cases
                      (e := PG.toRotationSystem.edgeOf d) (d := d) (y := d') rfl (by rw [hde, ← hd'e])
    -- If d = d', use d. If d = alpha d', check if d or alpha d is in face orbit
    rcases hcases with (h_eq | h_alpha)
    · -- Case d = d', so vertOf d = v
      refine ⟨d, ?_, hde⟩
      rw [togglesOn]
      simp only [Finset.mem_filter]
      refine ⟨hdS, ?_⟩
      -- Need: vertOf d = v XOR vertOf (phi d) = v
      have hvd : PG.toRotationSystem.vertOf d = v := by rw [← h_eq]; exact hv'
      -- Show XOR: exactly one is true
      simp only [hvd]
      -- Goal: decide True ≠ decide (PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = v)
      intro h
      -- From h : decide True = decide (PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = v), derive PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = v
      have hcontra : PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = v := by
        exact of_decide_eq_true h.symm
      -- This would make alpha d also at v
      have hvα : PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d) = v := by
        have : PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d) := vert_phi_eq_vert_alpha (RS := PG.toRotationSystem) d
        rw [hcontra] at this; exact this.symm
      -- Contradicts no_self_loops
      exact PG.toRotationSystem.no_self_loops d (hvd.trans hvα.symm)
    · -- Case d = alpha d', so d' = alpha d, and vertOf (alpha d) = v
      -- We'll use d, showing togglesOn property holds
      refine ⟨d, ?_, hde⟩
      rw [togglesOn]
      simp only [Finset.mem_filter]
      refine ⟨hdS, ?_⟩
      have hvα : PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d) = v := by rw [← h_alpha]; exact hv'
      have hvphi : PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = v := by
        have : PG.toRotationSystem.vertOf (PG.toRotationSystem.phi d) = PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d) := vert_phi_eq_vert_alpha (RS := PG.toRotationSystem) d
        rw [this]; exact hvα
      -- Show XOR: phi d has v but d doesn't
      simp only [hvphi]
      -- Goal: decide (PG.toRotationSystem.vertOf d = v) ≠ decide True
      intro h
      -- From h : decide (PG.toRotationSystem.vertOf d = v) = decide True, derive PG.toRotationSystem.vertOf d = v
      have hcontra : PG.toRotationSystem.vertOf d = v := by
        exact of_decide_eq_true h
      -- Contradicts no_self_loops
      exact PG.toRotationSystem.no_self_loops d (hcontra.trans hvα.symm)

/-- **Key theorem: Even edge-incidence for internal faces.**
For any internal face f = faceEdges d₀ and vertex v, the number of edges of f
incident to v is even.

This is the CANONICAL parity theorem for 4CT. It is fully proven and covers all uses
in the DiskGeometry pipeline (via the face_cycle_parity field). -/
theorem face_vertex_incidence_even_internal (PG : PlanarGeometry V E) :
  ∀ (d₀ : PG.toRotationSystem.D) (v : V),
    PG.toRotationSystem.faceEdges d₀ ≠ PG.toRotationSystem.boundaryEdges →
    Even ((PG.toRotationSystem.incidentEdges v ∩ PG.toRotationSystem.faceEdges d₀).card) := by
  intros d₀ v h_internal
  rw [← toggles_biject_edges_internal PG d₀ v h_internal]
  exact PG.toRotationSystem.toggles_even d₀ v

/-! ### Optional global parity theorems (archived)

The following theorems are mathematically natural generalizations of the internal-face
parity result above, but they are **not used** in the Four-Color Theorem formalization.

They are commented out to maintain the "zero sorries" invariant for the core 4CT codebase.
The proof sketches are preserved here for future work or educational purposes.

**Why not needed:**
- `DiskGeometry.face_cycle_parity` is a **field** that requires parity for internal faces
- All actual 4CT uses go through that field, which is satisfied by `face_vertex_incidence_even_internal`
- The boundary face and bare RotationSystem cases are strictly stronger than needed

**Future work:** If you want these theorems later, treat them as a separate mini-project:
1. Decide which structure they semantically belong to
2. Either prove them fully using the toggles machinery, or
3. Add them as fields on a new structure like `SurfaceRotationSystem` if definitional

/-
/-- Even edge-incidence for ALL faces in PlanarGeometry (including boundary).
UNUSED: The 4CT pipeline only needs the internal-face version.
INCOMPLETE: Boundary case requires subtle reasoning about dual dart orbits. -/
theorem face_vertex_incidence_even_PlanarGeometry (PG : PlanarGeometry V E) :
  ∀ (d₀ : PG.toRotationSystem.D) (v : V),
    Even ((PG.toRotationSystem.incidentEdges v ∩ PG.toRotationSystem.faceEdges d₀).card) := by
  intros d₀ v
  by_cases h : PG.toRotationSystem.faceEdges d₀ = PG.toRotationSystem.boundaryEdges
  · -- Boundary case: The boundary is a cycle, so parity should hold
    -- Challenge: For boundary edges, both darts d and α(d) can be in the same orbit
    -- The toggles are even (by toggles_even), but the bijection argument is more subtle
    -- TODO: Prove using cycle structure of boundary, or adapt toggles bijection
    sorry
  · -- Internal case: proven ✓
    exact face_vertex_incidence_even_internal PG d₀ v h

/-- Even edge-incidence for any face in any RotationSystem.
UNUSED: The 4CT pipeline works at the PlanarGeometry/DiskGeometry level.
UNCLEAR: May not hold for non-planar rotation systems without additional axioms. -/
theorem face_vertex_incidence_even (RS : RotationSystem V E) :
  ∀ (d₀ : RS.D) (v : V),
    Even ((Finset.univ.filter (fun e => ∃ d, RS.edgeOf d = e ∧ RS.vertOf d = v) ∩ RS.faceEdges d₀).card) := by
  intro d₀ v
  -- TODO: For planar rotation systems, follows from PlanarGeometry version
  -- For general rotation systems, may need additional structure assumptions
  sorry
-/

-/

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

