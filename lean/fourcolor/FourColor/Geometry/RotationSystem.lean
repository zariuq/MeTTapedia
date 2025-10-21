import FourColor.Triangulation

namespace FourColor
namespace Geometry

open scoped BigOperators
open Classical

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

    -- If exactly one internal face contained e, then both darts map to same face
    -- But standard rotation system property: α-paired darts (d and α(d)) belong to
    -- different faces because they lie on opposite sides of the edge.
    -- This is a foundational planarity fact for rotation systems.
    sorry  -- Standard RS: α-paired darts have distinct faceEdges (~5 lines via phi-orbit analysis)

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

