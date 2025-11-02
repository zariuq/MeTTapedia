/-
# Module 3: Path XOR Calculus

## The Pattern

**Given**: Paths in a graph with edge weights
**Prove**: XOR sums compose correctly (concatenation, single edge, etc.)

## Why This Matters

Blocks:
- `pathXORSum` (Tait.lean:481)
- `pathXORSum_single_edge` (Tait.lean:491)
- `pathXORSum_concat` (Tait.lean:508)

These are about PATH COMPOSITION - a fundamental graph theory pattern.

## Difficulty: ⭐⭐⭐☆☆ (Medium - needs induction)

## Prerequisites

- Basic graph theory (paths, edges)
- XOR properties (associativity, commutativity, x ⊕ x = 0)
- Module 2 helpful but not required

-/

import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Basic

/-! ## Exercise 1: XOR Basics -/

-- In ZMod 2, + is XOR
def zxor (a b : ZMod 2) := a + b

-- Key properties we'll need
example (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

example (a b c : ZMod 2) : (a + b) + c = a + (b + c) := by
  exact add_assoc a b c

example (a b : ZMod 2) : a + b = b + a := by
  exact add_comm a b

/-! ## Exercise 2: List XOR -/

/-
**Exercise 2a**: XOR of empty list is 0
-/
example : ([] : List (ZMod 2)).sum = 0 := by
  rfl

/-
**Exercise 2b**: XOR of singleton list is the element
-/
example (x : ZMod 2) : [x].sum = x := by
  simp [List.sum_cons, List.sum_nil]

/-
**Exercise 2c**: XOR distributes over concatenation
-/
example (xs ys : List (ZMod 2)) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  exact List.sum_append

/-! ## Exercise 3: Path Representation -/

-- A path is a list of edges
def Path (E : Type*) := List E

-- Weight function: edge → color (in our case, ZMod 2)
variable {E : Type*}

def pathSum (w : E → ZMod 2) (p : Path E) : ZMod 2 :=
  (p.map w).sum

/-
**Exercise 3a**: Empty path has sum 0
-/
example (w : E → ZMod 2) : pathSum w [] = 0 := by
  rfl

/-
**Exercise 3b**: Single edge path has sum = weight of that edge
-/
example (w : E → ZMod 2) (e : E) : pathSum w [e] = w e := by
  unfold pathSum
  simp [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

/-
**Exercise 3c**: Concatenated paths have sum = sum of sums
-/
example (w : E → ZMod 2) (p q : List E) :
    pathSum w (p ++ q) = pathSum w p + pathSum w q := by
  unfold pathSum
  rw [List.map_append, List.sum_append]

/-! ## Exercise 4: Cycle Property -/

/-
**Exercise 4a**: If you traverse an edge then back, sum is 0
-/
example (w : E → ZMod 2) (e : E) :
    pathSum w [e, e] = 0 := by
  unfold pathSum
  simp [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  --  In ZMod 2, any element + itself = 0
  sorry  -- Exercise for later: prove x + x = 0 for ZMod 2

/-
**Exercise 4b**: A path followed by its reverse has sum 0

This is KEY for cycles!
-/
example (w : E → ZMod 2) (p : List E) :
    pathSum w (p ++ p.reverse) = 0 := by
  unfold pathSum
  rw [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse]
  -- In ZMod 2, any element + itself = 0
  sorry  -- Exercise for later: prove x + x = 0 for ZMod 2

/-! ## Exercise 5: Application to Tait.lean -/

/-
The actual axioms to eliminate:

```lean
-- From Tait.lean:481
theorem pathXORSum (p : Path) :
  pathXORSum p = ∑ e ∈ p.edges, edgeColor e

-- From Tait.lean:491
theorem pathXORSum_single_edge (e : E) :
  pathXORSum (singleEdgePath e) = edgeColor e

-- From Tait.lean:508
theorem pathXORSum_concat (p q : Path) :
  pathXORSum (p ++ q) = pathXORSum p ⊕ pathXORSum q
```

These should be PROVABLE from the definition of `pathXORSum`!

**Strategy**:
1. Find the definition of `pathXORSum` in Tait.lean
2. It's probably defined as the XOR sum over edges
3. Then these axioms are just Exercise 3b and 3c above!
-/

/-! ## Advanced: Cycle Lemma -/

/-
**Exercise 6 (Challenge)**: Any cycle has even XOR sum in 2-colored graphs

This connects to Module 2 (Cycle Parity).
-/

-- A cycle is a path that starts and ends at the same vertex
-- (Commented out to avoid redeclaration issues)
-- structure Cycle (V E : Type*) where
--   path : List E
--   is_closed : sorry  -- start vertex = end vertex (details omitted)

/-
If edges are 2-colored (taking values in ZMod 2), then:
- Cycles alternate colors if properly 2-colored
- XOR sum around cycle = number of edges mod 2
- For proper 2-coloring: this should be 0!
-/

/-! ## Mathlib Resources -/

#check List.sum_nil
#check List.sum_cons
#check List.sum_append
#check List.map_append
#check List.sum_reverse
#check add_assoc
#check add_comm
-- In ZMod 2: x + x = 0 (see examples above)

-- For paths in graphs:
-- Check Mathlib.Combinatorics.SimpleGraph.Path
-- or Mathlib.Combinatorics.SimpleGraph.Walk

/-! ## Success Criteria -/

/-
✅ Module complete when:
1. Exercises 1-5 solved
2. `pathXORSum_single_edge` eliminated from Tait.lean
3. `pathXORSum_concat` eliminated from Tait.lean
4. `pathXORSum` axiom eliminated (replaced with def + lemma)

This removes 3 axioms by understanding path composition!

**Estimated time**: 2-3 hours for exercises, 1 hour for application
-/
