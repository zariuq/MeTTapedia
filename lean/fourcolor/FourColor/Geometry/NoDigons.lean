/-
Copyright (c) 2025 Zar Goertzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zar Goertzel, GPT-5.1 Pro, Codex
-/ 

import FourColor.Geometry.DiskTypes
import FourColor.Geometry.PlanarityHelpers
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# No digons: basic combinatorial facts

This file packages a few small facts about endpoints and incidence that are
used as supporting lemmas elsewhere (e.g. degree-sum/handshake).  The previous
version had several unfinished proof sketches; this rewrite keeps the same
API surface where it was stable while providing short, total proofs.
-/

namespace FourColor.Geometry

open BigOperators
open scoped BigOperators
open RotationSystem
open FourColor.Geometry.PlanarityHelpers

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The set of endpoints of an edge (size 2). -/
def endpoints (PG : PlanarGeometry V E) (e : E) : Finset V :=
  (PG.toRotationSystem.dartsOn e).image PG.toRotationSystem.vertOf

/-- Degree of a vertex `v` within a face `f`. -/
def faceDeg (G : DiskGeometry V E) (f : Finset E) (v : V) : Nat :=
  (G.asZeroBoundary.incident v ∩ f).card

/-- Incident edges agree with the endpoint relation. -/
lemma incident_iff_endpoint (G : DiskGeometry V E) {e : E} {v : V} :
    e ∈ G.asZeroBoundary.incident v ↔ v ∈ endpoints G.toPlanarGeometry e := by
  classical
  simp [endpoints, RotationSystem.dartsOn, G.incident_compat, Finset.mem_image,
    Finset.mem_filter, and_left_comm, and_assoc, and_comm]

/-- Each edge has exactly two endpoints. -/
lemma endpoints_card_two (PG : PlanarGeometry V E) (e : E) :
    (endpoints PG e).card = 2 := by
  classical
  -- Choose the two darts over `e`
  obtain ⟨d1, d2, hne, hdarts⟩ :=
    Finset.card_eq_two.mp (PG.toRotationSystem.dartsOn_card_two e)
  have hd1_edge : PG.toRotationSystem.edgeOf d1 = e :=
    (PG.toRotationSystem.mem_dartsOn).1 (by simpa [hdarts])
  have hd2_edge : PG.toRotationSystem.edgeOf d2 = e :=
    (PG.toRotationSystem.mem_dartsOn).1 (by simpa [hdarts])

  -- The second dart is the α-partner (since the fiber has size 2)
  have hd2_alpha : d2 = PG.toRotationSystem.alpha d1 := by
    have hcases :=
      PG.toRotationSystem.edge_fiber_two_cases (e := e) (d := d1) (y := d2) hd1_edge hd2_edge
    rcases hcases with h | h
    · exact (hne h.symm).elim
    · exact h

  -- Distinct vertices (loop-free)
  have hv_ne : PG.toRotationSystem.vertOf d1 ≠ PG.toRotationSystem.vertOf d2 := by
    subst hd2_alpha
    exact PG.toRotationSystem.no_self_loops d1

  -- Compute the image explicitly
  have hcard :
      ({PG.toRotationSystem.vertOf d1,
        PG.toRotationSystem.vertOf d2} : Finset V).card = 2 := by
    simp [Finset.card_pair, hv_ne]
  unfold endpoints
  simpa [hdarts, hne] using hcard

/-- Distinct edges have distinct endpoint sets (simplicity). -/
lemma endpoints_injective (PG : PlanarGeometry V E) {e1 e2 : E} (h : e1 ≠ e2) :
    endpoints PG e1 ≠ endpoints PG e2 := by
  classical
  -- Fix explicit darts on each edge (the two-element fibers)
  obtain ⟨d1, d1', hne1, hdarts1⟩ :=
    Finset.card_eq_two.mp (PG.toRotationSystem.dartsOn_card_two e1)
  obtain ⟨d2, d2', hne2, hdarts2⟩ :=
    Finset.card_eq_two.mp (PG.toRotationSystem.dartsOn_card_two e2)

  have hedge1 : PG.toRotationSystem.edgeOf d1 = e1 :=
    (PG.toRotationSystem.mem_dartsOn).1 (by simpa [hdarts1])
  have hedge2 : PG.toRotationSystem.edgeOf d2 = e2 :=
    (PG.toRotationSystem.mem_dartsOn).1 (by simpa [hdarts2])

  -- The second dart on each edge is the α-partner
  have hd1'_alpha : d1' = PG.toRotationSystem.alpha d1 := by
    have hd1'_edge : PG.toRotationSystem.edgeOf d1' = e1 :=
      (PG.toRotationSystem.mem_dartsOn).1 (by simpa [hdarts1])
    rcases PG.toRotationSystem.edge_fiber_two_cases
        (e := e1) (d := d1) (y := d1') hedge1 hd1'_edge with h' | h'
    · exact (hne1 h'.symm).elim
    · exact h'
  have hd2'_alpha : d2' = PG.toRotationSystem.alpha d2 := by
    have hd2'_edge : PG.toRotationSystem.edgeOf d2' = e2 :=
      (PG.toRotationSystem.mem_dartsOn).1 (by simpa [hdarts2])
    rcases PG.toRotationSystem.edge_fiber_two_cases
        (e := e2) (d := d2) (y := d2') hedge2 hd2'_edge with h' | h'
    · exact (hne2 h'.symm).elim
    · exact h'

  -- Rewrite endpoints using these darts
  have hend1 : endpoints PG e1 =
      ({PG.toRotationSystem.vertOf d1,
        PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d1)} : Finset V) := by
    unfold endpoints
    simp [hdarts1, hd1'_alpha, hne1, Finset.insert_comm]
  have hend2 : endpoints PG e2 =
      ({PG.toRotationSystem.vertOf d2,
        PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d2)} : Finset V) := by
    unfold endpoints
    simp [hdarts2, hd2'_alpha, hne2, Finset.insert_comm]

  intro h_eq
  have hno :=
    PG.no_parallel_edges (d := d1) (d' := d2) hedge1 hedge2 h
  exact hno (by simpa [hend1, hend2] using h_eq)

/-! ### Degree sum (handshake) -/

/-- `faceDeg` as a bipartite fiber cardinality. -/
lemma faceDeg_eq_card_bipartiteAbove (G : DiskGeometry V E) (f : Finset E) (v : V) :
    faceDeg G f v =
      (Finset.bipartiteAbove (fun v e => e ∈ G.asZeroBoundary.incident v) f v).card := by
  classical
  unfold faceDeg
  have hset :
      G.asZeroBoundary.incident v ∩ f =
        Finset.bipartiteAbove (fun v e => e ∈ G.asZeroBoundary.incident v) f v := by
    ext e
    simp [Finset.mem_bipartiteAbove, Finset.mem_inter, and_left_comm, and_assoc, and_comm]
  simpa [hset]

/-- Each edge is incident to exactly two vertices, expressed via the bipartite fiber. -/
lemma card_bipartiteBelow_eq_two (G : DiskGeometry V E) (e : E) :
    (Finset.bipartiteBelow (fun v e => e ∈ G.asZeroBoundary.incident v)
        (Finset.univ : Finset V) e).card = 2 := by
  classical
  have hset :
      Finset.bipartiteBelow (fun v e => e ∈ G.asZeroBoundary.incident v)
          (Finset.univ : Finset V) e =
        endpoints G.toPlanarGeometry e := by
    ext v
    simp [Finset.mem_bipartiteBelow, incident_iff_endpoint (G := G)]
  simpa [hset] using endpoints_card_two (PG := G.toPlanarGeometry) e

/-- Handshake lemma restricted to a finite edge set `f`. -/
lemma sum_faceDeg_eq_two_card (G : DiskGeometry V E) (f : Finset E) :
    ∑ v, faceDeg G f v = 2 * f.card := by
  classical
  let r : V → E → Prop := fun v e => e ∈ G.asZeroBoundary.incident v

  -- Rewrite the left-hand side using the bipartite fibers on the vertex side
  have hLHS :
      (∑ v : V, faceDeg G f v) =
        Finset.sum (Finset.univ : Finset V) (fun v => (Finset.bipartiteAbove r f v).card) := by
    classical
    have hfun :
        (fun v : V => faceDeg G f v) =
          fun v : V => (Finset.bipartiteAbove r f v).card := by
      funext v
      simpa [r] using faceDeg_eq_card_bipartiteAbove (G := G) (f := f) v
    have : ∑ v : V, faceDeg G f v = ∑ v : V, (Finset.bipartiteAbove r f v).card := by
      simpa [hfun]
    -- change the right side to a `Finset` sum over `univ`
    simpa using this

  -- Swap the double sum using the library double-counting lemma
  have hSwap :
      Finset.sum (Finset.univ : Finset V) (fun v => (Finset.bipartiteAbove r f v).card) =
        Finset.sum f (fun e => (Finset.bipartiteBelow r (Finset.univ : Finset V) e).card) := by
    simpa using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := r) (s := (Finset.univ : Finset V)) (t := f))

  -- Evaluate the edge-side fiber: exactly two endpoints
  have hBelow :
      Finset.sum f (fun e => (Finset.bipartiteBelow r (Finset.univ : Finset V) e).card) =
        Finset.sum f (fun _ => (2 : Nat)) := by
    refine Finset.sum_congr rfl ?_
    intro e he
    simpa [r] using card_bipartiteBelow_eq_two (G := G) e

  -- Sum the constant 2 over `f`
  have hConst : Finset.sum f (fun _ => (2 : Nat)) = 2 * f.card := by
    simp [Finset.sum_const, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

  calc
    ∑ v : V, faceDeg G f v
        = Finset.sum (Finset.univ : Finset V) (fun v => (Finset.bipartiteAbove r f v).card) := hLHS
    _   = Finset.sum f (fun e => (Finset.bipartiteBelow r (Finset.univ : Finset V) e).card) := hSwap
    _   = Finset.sum f (fun _ => (2 : Nat)) := hBelow
    _   = 2 * f.card := hConst

/-- A direct alias to the `NoDigons` axiom: two faces cannot share two distinct interior edges. -/
lemma faces_share_at_most_one_interior_edge (G : DiskGeometry V E)
    (hNoDigons : NoDigons G)
    {f g : Finset E} (hf : f ∈ G.toRotationSystem.internalFaces)
    (hg : g ∈ G.toRotationSystem.internalFaces) (hfg : f ≠ g)
    {e1 e2 : E} (he1_ne_e2 : e1 ≠ e2)
    (he1_int : e1 ∉ G.toRotationSystem.boundaryEdges)
    (he2_int : e2 ∉ G.toRotationSystem.boundaryEdges)
    (he1_f : e1 ∈ f) (he1_g : e1 ∈ g)
    (he2_f : e2 ∈ f) (he2_g : e2 ∈ g) :
    False :=
  hNoDigons hf hg hfg he1_ne_e2 he1_int he2_int he1_f he1_g he2_f he2_g

end FourColor.Geometry
