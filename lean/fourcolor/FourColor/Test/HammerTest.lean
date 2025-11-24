/-
Test file for LeanHammer integration
-/
import Hammer
import Mathlib.Combinatorics.SimpleGraph.Basic

-- Basic sanity test (Aesop only)
example : True := by
  hammer

-- Test with installed Zipperposition
example : True := by
  hammer {solver := zipperposition}

-- Test on simple graph theory statement
example {α : Type*} (G : SimpleGraph α) (v : α) : v ∈ G.neighborSet v → False := by
  intro h
  exact G.loopless v h

-- Test premise selection on a finset lemma
example {α : Type*} (s t : Finset α) (h : s ⊆ t) : s.card ≤ t.card := by
  hammer
