import Mettapedia.GSLT.Causality.DoCalculus.Adjustment

/-!
# A collider separates only after the incoming arrows are deleted

The graph is `Z → X ← Y`. Conditioning on `X` opens the trail while the arrows
into `X` remain. Deleting those arrows leaves three isolated vertices, so the
same sets are fully d-separated. This is the separation hypothesis of
do-calculus rule 1, and it is not the separation hypothesis of the corollary
that starts from the outgoing-deleted graph.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open DirectedGraph
open DSeparation

/-- Vertices of the collider `Z → X ← Y`. -/
inductive Collider
  | z
  | x
  | y
  deriving DecidableEq

instance : Fintype Collider where
  elems := {Collider.z, Collider.x, Collider.y}
  complete := by
    intro v
    cases v
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- `Z → X` and `Y → X`. -/
def colliderGraph : DirectedGraph Collider where
  edges a b := (a = .z ∧ b = .x) ∨ (a = .y ∧ b = .x)

/-- Rank increases along every edge, so the collider is acyclic. -/
def colliderRank : Collider → ℕ
  | .z => 0
  | .y => 0
  | .x => 1

lemma collider_edge_increases {a b : Collider} (h : colliderGraph.edges a b) :
    colliderRank a < colliderRank b := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst ha
    subst hb
    exact Nat.zero_lt_one
  · subst ha
    subst hb
    exact Nat.zero_lt_one

lemma collider_reachable_rank {a b : Collider} (h : colliderGraph.Reachable a b) :
    colliderRank a ≤ colliderRank b := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact le_trans (Nat.le_of_lt (collider_edge_increases hedge)) ih

/-- The collider has no directed cycle. -/
lemma colliderAcyclic : colliderGraph.IsAcyclic := by
  intro v ⟨src, hedge, hreach⟩
  exact lt_irrefl _ <|
    lt_of_lt_of_le (collider_edge_increases hedge) (collider_reachable_rank hreach)

/-! ## The outgoing-deleted graph still has the collider -/

lemma collider_out_zx :
    UndirectedEdge (deleteOutgoing colliderGraph ({Collider.x} : Finset Collider))
      Collider.z Collider.x :=
  Or.inl ⟨Or.inl ⟨rfl, rfl⟩,
    Finset.notMem_singleton.mpr (by decide : Collider.z ≠ Collider.x)⟩

lemma collider_out_xy :
    UndirectedEdge (deleteOutgoing colliderGraph ({Collider.x} : Finset Collider))
      Collider.x Collider.y :=
  Or.inr ⟨Or.inr ⟨rfl, rfl⟩,
    Finset.notMem_singleton.mpr (by decide : Collider.y ≠ Collider.x)⟩

def colliderOutTriple :
    PathTriple (deleteOutgoing colliderGraph ({.x} : Finset Collider)) where
  a := .z
  b := .x
  c := .y
  edge_ab := collider_out_zx
  edge_bc := collider_out_xy
  a_ne_c := by decide

lemma collider_out_isCollider :
    IsCollider (deleteOutgoing colliderGraph ({Collider.x} : Finset Collider))
      colliderOutTriple := by
  unfold IsCollider colliderOutTriple
  exact ⟨⟨Or.inl ⟨rfl, rfl⟩,
      Finset.notMem_singleton.mpr (by decide : Collider.z ≠ Collider.x)⟩,
    ⟨Or.inr ⟨rfl, rfl⟩,
      Finset.notMem_singleton.mpr (by decide : Collider.y ≠ Collider.x)⟩⟩

/-- Conditioning on `X` opens `Z — X — Y` while the arrows into `X` remain. -/
lemma collider_outgoing_active :
    IsActive (deleteOutgoing colliderGraph ({.x} : Finset Collider))
      ({.x} : Set Collider) colliderOutTriple := by
  intro hblocked
  rcases hblocked with ⟨hnon, _⟩ | ⟨_, hbNot, _⟩
  · exact hnon collider_out_isCollider
  · exact hbNot (by
      unfold colliderOutTriple
      exact Set.mem_singleton _)

lemma collider_outgoing_trail :
    ActiveTrail (deleteOutgoing colliderGraph ({.x} : Finset Collider))
      ({.x} : Set Collider) [Collider.z, Collider.x, Collider.y] := by
  exact ActiveTrail.cons colliderOutTriple.edge_ab colliderOutTriple.edge_bc
    colliderOutTriple.a_ne_c collider_outgoing_active
    (ActiveTrail.two colliderOutTriple.edge_bc)

lemma collider_outgoing_endpoints :
    PathEndpoints [Collider.z, Collider.x, Collider.y] = some (Collider.z, Collider.y) := by
  rfl

/-- Outgoing deletion does not d-separate `Z` from `Y` given `X`. -/
theorem collider_rule1_outgoing_not_separated :
    ¬ DSeparatedFull (deleteOutgoing colliderGraph ({.x} : Finset Collider))
        ({.z} : Set Collider) ({.y} : Set Collider) ({.x} : Set Collider) := by
  intro hsep
  exact hsep Collider.z (Set.mem_singleton _) Collider.y (Set.mem_singleton _) (by decide)
    ⟨[Collider.z, Collider.x, Collider.y], List.cons_ne_nil _ _, collider_outgoing_endpoints,
      collider_outgoing_trail⟩

/-! ## Incoming deletion removes both arrows -/

lemma collider_incoming_no_edge (src dst : Collider) :
    ¬ (deleteIncoming colliderGraph ({Collider.x} : Finset Collider)).edges src dst := by
  intro h
  rcases h with ⟨hedge, hdst⟩
  rcases hedge with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · subst hs
    subst hd
    exact hdst (Finset.mem_singleton_self _)
  · subst hs
    subst hd
    exact hdst (Finset.mem_singleton_self _)

lemma collider_incoming_no_undirected (src dst : Collider) :
    ¬ UndirectedEdge (deleteIncoming colliderGraph ({.x} : Finset Collider)) src dst := by
  intro h
  rcases h with h | h
  · exact collider_incoming_no_edge src dst h
  · exact collider_incoming_no_edge dst src h

/-- Incoming deletion d-separates `Z` from `Y` given `X`. -/
theorem collider_rule1_incoming_separated :
    DSeparatedFull (deleteIncoming colliderGraph ({.x} : Finset Collider))
      ({.z} : Set Collider) ({.y} : Set Collider) ({.x} : Set Collider) := by
  intro a _ b _ hab htrail
  rcases htrail with ⟨_p, _hne, hends, hact⟩
  cases hact with
  | single v =>
      have hvv : PathEndpoints [v] = some (v, v) := rfl
      injection hvv.symm.trans hends with hpair
      injection hpair with hva hvb
      exact hab (hva.symm.trans hvb)
  | two hEdge =>
      exact collider_incoming_no_undirected _ _ hEdge
  | cons habEdge _ _ _ _ =>
      exact collider_incoming_no_undirected _ _ habEdge

/-- Rule 1's incoming-deleted hypothesis holds on this collider, and the
outgoing-deleted hypothesis does not. -/
theorem collider_rule1_separation_strict :
    DSeparatedFull (deleteIncoming colliderGraph ({.x} : Finset Collider))
      ({.z} : Set Collider) ({.y} : Set Collider) ({.x} : Set Collider) ∧
    ¬ DSeparatedFull (deleteOutgoing colliderGraph ({.x} : Finset Collider))
      ({.z} : Set Collider) ({.y} : Set Collider) ({.x} : Set Collider) :=
  ⟨collider_rule1_incoming_separated, collider_rule1_outgoing_not_separated⟩

end Mettapedia.GSLT.Causality.DoCalculus
