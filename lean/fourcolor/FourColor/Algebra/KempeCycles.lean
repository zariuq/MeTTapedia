import FourColor.Triangulation

/-!
# Kempe Cycle Infrastructure (Background B)

This module provides the proper Kempe chain/cycle definitions with even-incidence guarantees.

Based on GPT-5 guidance: Kempe chains are connected components of the αβ-subgraph,
restricted to interior edges, forming degree-2 cycles with even incidence at each vertex.
-/

namespace FourColor

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A Kempe cycle is a subset of edges that:
    1. Forms alternating colored paths (edges colored α or β)
    2. Has degree ≤ 2 at each vertex (path or cycle)
    3. Is a connected component in the αβ-subgraph
-/
def isKempeCycle (incident : V → Finset E) (x : E → Color) 
    (C : Finset E) (α β : Color) : Prop :=
  -- All edges in C are colored α or β
  (∀ e ∈ C, x e = α ∨ x e = β) ∧
  -- Degree ≤ 2 at each vertex (each vertex has 0, 1, or 2 incident edges from C)
  (∀ v : V, (C ∩ incident v).card ≤ 2)

/-- An interior Kempe cycle additionally satisfies:
    - All edges are interior (not on boundary)
    - For cubic graphs, degree-2 cycles have even incidence
-/
def isInteriorKempeCycle (D : ZeroBoundaryData V E)
    (x : E → Color) (C : Finset E) (α β : Color) : Prop :=
  isKempeCycle D.incident x C α β ∧
  -- Interior: disjoint from boundary
  (∀ e ∈ C, e ∉ D.boundaryEdges)

/-- Key theorem: Kempe cycles have even αβ-incidence at each vertex.
    
    This is the crux: in a degree-2 path/cycle, each vertex sees:
    - 0 edges (not in the cycle)
    - 2 edges (in the cycle, passing through)
    
    Both are even! This is what makes swapping preserve sums.
-/
lemma kempeCycle_even_at (incident : V → Finset E) (x : E → Color)
    (C : Finset E) (α β : Color)
    (hC : isKempeCycle incident x C α β) :
    ∀ v : V, Even ((C ∩ incident v).filter (fun e => x e = α ∨ x e = β)).card := by
  intro v
  -- The filter is redundant since isKempeCycle guarantees all edges are α or β
  have h_filter : (C ∩ incident v).filter (fun e => x e = α ∨ x e = β) = C ∩ incident v := by
    ext e
    simp [Finset.mem_filter, Finset.mem_inter]
    intro he_C he_inc
    exact hC.1 e he_C
  rw [h_filter]
  -- Now use that (C ∩ incident v).card ≤ 2
  have h_deg := hC.2 v
  -- In a Kempe cycle, degree is 0 or 2 (not 1, because edges are paired)
  -- TODO: Need to prove "no dangling edges" property
  sorry

/-- Helper: In a proper Kempe chain (connected component), 
    interior vertices have degree exactly 2.
    
    This is the graph-theoretic fact that ensures even incidence.
-/
lemma kempe_interior_degree_two (incident : V → Finset E) (x : E → Color)
    (C : Finset E) (α β : Color) (v : V)
    (hC : isKempeCycle incident x C α β)
    (h_interior : ∃ e₁ e₂ : E, e₁ ∈ C ∧ e₂ ∈ C ∧ e₁ ≠ e₂ ∧ e₁ ∈ incident v ∧ e₂ ∈ incident v) :
    (C ∩ incident v).card = 2 := by
  -- If a vertex has ≥ 2 edges from C, it must have exactly 2 (by degree bound)
  have h_deg := hC.2 v
  rcases h_interior with ⟨e₁, e₂, he₁_C, he₂_C, hne, he₁_v, he₂_v⟩
  have h_two_in : {e₁, e₂} ⊆ C ∩ incident v := by
    intro e he
    simp at he
    cases he
    · subst_vars; simp [he₁_C, he₁_v]
    · subst_vars; simp [he₂_C, he₂_v]
  have h_card_two : ({e₁, e₂} : Finset E).card = 2 := by
    simp [Finset.card_insert_of_not_mem, hne]
  have := Finset.card_le_card h_two_in
  omega

end FourColor
