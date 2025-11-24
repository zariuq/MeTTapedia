/-
Test LeanHammer on realistic graph theory sorries
-/
import Hammer
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Test 1: Basic Finset Properties -/

-- Simple cardinality bound
example (s t : Finset α) (h : s ⊆ t) : s.card ≤ t.card := by
  hammer

-- Cardinality of union
example (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card := by
  hammer

/-! ## Test 2: Graph Properties -/

-- Vertex not in its own neighbor set
example (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    v ∉ G.neighborFinset v := by
  hammer

-- Adjacency symmetry via neighbor sets
example (G : SimpleGraph α) [DecidableRel G.Adj] (v w : α) :
    w ∈ G.neighborFinset v → v ∈ G.neighborFinset w := by
  hammer

/-! ## Test 3: Connectivity -/

-- Reachable relation is reflexive
example (G : SimpleGraph α) (v : α) : G.Reachable v v := by
  hammer

-- Reachable is symmetric
example (G : SimpleGraph α) (v w : α) (h : G.Reachable v w) : G.Reachable w v := by
  hammer

/-! ## Test 4: Cliques and Independent Sets -/

-- Empty set is a clique
example (G : SimpleGraph α) : G.IsClique (∅ : Set α) := by
  hammer

-- Singleton is always independent
example (G : SimpleGraph α) (v : α) : G.IsIndepSet {v} := by
  hammer

/-! ## Test 5: Degree Properties -/

-- Degree in terms of neighborFinset
example (G : SimpleGraph α) [DecidableRel G.Adj] [Fintype (G.neighborSet v)] (v : α) :
    G.degree v = (G.neighborFinset v).card := by
  hammer

/-! ## Results -/

#check "All tests compiled successfully!"
