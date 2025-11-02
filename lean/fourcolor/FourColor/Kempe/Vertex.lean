-- FourColor/Kempe/Vertex.lean
-- Vertex-based Kempe chains for 4-vertex-colorings (classic world)
--
-- This is the VertexKempeChain we factored out from Tait.lean.
-- It lives separately to avoid name collision with edge-based Kempe chains.

import FourColor.Tait

namespace FourColor.VertexKempe

open Relation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two vertices are adjacent in the αβ-subgraph if they are connected by an edge
    and their colors are exactly α and β (in some order). -/
def twoColorSubgraph (adj : V → V → Prop) (coloring : V → VertexColor)
    (c₁ c₂ : VertexColor) (u v : V) : Prop :=
  adj u v ∧ (coloring u = c₁ ∨ coloring u = c₂) ∧ (coloring v = c₁ ∨ coloring v = c₂)

/-- A Kempe chain is the connected component containing vertex v in the αβ-subgraph. -/
def VertexKempeChain {V : Type*}
    (adj : V → V → Prop) (coloring : V → VertexColor)
    (c₁ c₂ : VertexColor) (v : V) : Set V :=
  {w | Relation.ReflTransGen (twoColorSubgraph adj coloring c₁ c₂) v w}

/-- Vertices in a Kempe chain are colored c₁ or c₂. -/
lemma kempe_chain_colors {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (coloring : V → VertexColor)
    (c₁ c₂ : VertexColor) (v w : V)
    (hv : coloring v = c₁ ∨ coloring v = c₂)
    (hw : w ∈ VertexKempeChain adj coloring c₁ c₂ v) :
    coloring w = c₁ ∨ coloring w = c₂ := by
  unfold VertexKempeChain at hw
  simp at hw
  induction hw with
  | refl => exact hv
  | tail _ hadj ih =>
    rcases hadj with ⟨_, _, hwcol⟩
    exact hwcol

/-- Predicate-based adjacency in the αβ-subgraph (mirror of edge-side pattern).
    Two vertices are adjacent if connected and have different colors from {α,β}. -/
def twoColorAdjP (adj : V → V → Prop) (col : V → VertexColor) (α β : VertexColor) :
    V → V → Prop :=
  fun u w => adj u w ∧ (col u = α ∨ col u = β) ∧ (col w = α ∨ col w = β) ∧ col u ≠ col w

/-- Predicate-based Kempe chain: set of vertices reachable from v via αβ-path. -/
def ChainPv (adj : V → V → Prop) (col : V → VertexColor) (v : V) (α β : VertexColor) : Set V :=
  {u | (col u = α ∨ col u = β) ∧ ReflTransGen (twoColorAdjP adj col α β) v u}

/-- Membership in the predicate chain is all-or-none at a vertex.
    If one αβ-edge at v is in the chain, both are (by connectivity). -/
lemma chainP_touches_both_edges (adj : V → V → Prop) (col : V → VertexColor)
    (v u w : V) (α β : VertexColor)
    (hadj_u : twoColorAdjP adj col α β v u)
    (hadj_w : twoColorAdjP adj col α β v w)
    (hu_in : u ∈ ChainPv adj col v α β) :
    w ∈ ChainPv adj col v α β := by
  -- Strategy: u is in chain means there's a path v → ... → u
  -- We want to show w is in chain, i.e., path v → ... → w exists
  -- Since v is adjacent to w via twoColorAdjP, we have immediate path v → w
  unfold ChainPv at hu_in ⊢
  simp at hu_in ⊢
  constructor
  · -- Show col w = α ∨ col w = β
    rcases hadj_w with ⟨_, ⟨hw_col, _⟩, _⟩
    exact hw_col
  · -- Show ReflTransGen (twoColorAdjP ...) v w
    -- Direct path: v → w in one step
    apply ReflTransGen.single
    exact hadj_w

end FourColor.VertexKempe
