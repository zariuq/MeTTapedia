/-
# Module 5: Line Graph Adjacency

## The Pattern

**Given**: Definition of edge adjacency
**Prove**: Basic properties (iff, symmetry)

## Why This Matters

Blocks:
- `adj_iff_shared_edge` (Tait.lean:269)
- `adj_symm` (Tait.lean:278)

These are EASY - just definitional manipulation. Good warmup module!

## Difficulty: ⭐☆☆☆☆ (Easiest)

-/

import Mathlib.Data.Finset.Basic

/-! ## The Definitions -/

-- Simplified version of edge adjacency
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

-- Version 1: Edges adjacent if they share a vertex
def edgeAdj₁ (incident : V → Finset E) (e e' : E) : Prop :=
  e ≠ e' ∧ ∃ v, e ∈ incident v ∧ e' ∈ incident v

-- Version 2: Using explicit shared edge predicate
def hasSharedVertex (incident : V → Finset E) (e e' : E) : Prop :=
  ∃ v, e ∈ incident v ∧ e' ∈ incident v

def edgeAdj₂ (incident : V → Finset E) (e e' : E) : Prop :=
  e ≠ e' ∧ hasSharedVertex incident e e'

/-! ## Exercise 1: Definitional Equivalence -/

/-
**Exercise 1a**: The two definitions are equivalent (just unfolding!)
-/
example (incident : V → Finset E) (e e' : E) :
    edgeAdj₁ incident e e' ↔ edgeAdj₂ incident e e' := by
  -- Just unfold both definitions - they're syntactically identical
  unfold edgeAdj₁ edgeAdj₂ hasSharedVertex
  -- Now they're exactly the same
  rfl

/-! ## Exercise 2: Symmetry -/

/-
**Exercise 2a**: Edge adjacency is symmetric.

This is `adj_symm` from Tait.lean:278
-/
example (incident : V → Finset E) (e e' : E) :
    edgeAdj₁ incident e e' → edgeAdj₁ incident e' e := by
  intro ⟨hne, v, he, he'⟩
  constructor
  · -- Show e' ≠ e
    exact fun h => hne h.symm
  · -- Show ∃ v with both edges incident
    exact ⟨v, he', he⟩

/-
**Exercise 2b**: Prove it's symmetric using Iff instead
-/
example (incident : V → Finset E) (e e' : E) :
    edgeAdj₁ incident e e' ↔ edgeAdj₁ incident e' e := by
  constructor
  · intro ⟨hne, v, he, he'⟩
    exact ⟨fun h => hne h.symm, v, he', he⟩
  · intro ⟨hne, v, he, he'⟩
    exact ⟨fun h => hne h.symm, v, he', he⟩

/-! ## Exercise 3: Connection to Irreflexivity -/

/-
**Exercise 3a**: No edge is adjacent to itself
-/
example (incident : V → Finset E) (e : E) :
    ¬ edgeAdj₁ incident e e := by
  intro ⟨hne, _⟩
  exact hne rfl

/-! ## Exercise 4: Properties of Shared Vertices -/

/-
**Exercise 4a**: Sharing a vertex is symmetric (obviously!)
-/
example (incident : V → Finset E) (e e' : E) :
    hasSharedVertex incident e e' ↔ hasSharedVertex incident e' e := by
  constructor
  · intro ⟨v, h1, h2⟩
    exact ⟨v, h2, h1⟩
  · intro ⟨v, h1, h2⟩
    exact ⟨v, h2, h1⟩

/-
**Exercise 4b**: An edge shares a vertex with itself at any incident vertex
-/
example (incident : V → Finset E) (e : E) (v : V) (h : e ∈ incident v) :
    hasSharedVertex incident e e := by
  exact ⟨v, h, h⟩

/-! ## Application to Tait.lean -/

/-
The actual axioms to eliminate:

```lean
-- From Tait.lean:269
theorem adj_iff_shared_edge (e e' : E) :
  adj e e' ↔ e ≠ e' ∧ ∃ v, e ∈ graph.incident v ∧ e' ∈ graph.incident v

-- From Tait.lean:278
theorem adj_symm : Symmetric adj
```

These should be PROVABLE from the definition of `adj` in Tait.lean!

**Action**: Check the actual definition of `adj` in Tait.lean and prove these
            as lemmas instead of axioms.

**Estimated time**: 15-30 minutes once you see the definition.
-/

/-! ## Mathlib Resources -/

#check Ne.symm          -- h : a ≠ b → b ≠ a
#check Iff.rfl          -- a ↔ a
#check Iff.intro        -- (a → b) → (b → a) → (a ↔ b)
#check Symmetric        -- Symmetric r means r a b → r b a

-- For finding the definition:
-- In Tait.lean, search for "def adj" or "abbrev adj"
-- Then these axioms should just be definitional lemmas

/-! ## Success Criteria -/

/-
✅ Module complete when:
1. All exercises solved
2. `adj_iff_shared_edge` eliminated from Tait.lean (proved as lemma)
3. `adj_symm` eliminated from Tait.lean (proved as lemma)

This removes 2 axioms with minimal effort!
-/
