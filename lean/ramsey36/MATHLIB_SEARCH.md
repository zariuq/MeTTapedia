# Partition and Inequality Arguments for Ramsey(3,6) Proof

## Summary

This document catalogs the standard combinatorial arguments used in the Ramsey(3,6) proof and identifies which are available in Mathlib vs. which need to be proven locally.

## Mathlib Modules Currently Used

The proof currently imports from these Mathlib modules:
- `Mathlib.Combinatorics.SimpleGraph.Basic` - Core graph definitions
- `Mathlib.Combinatorics.SimpleGraph.Clique` - Clique predicates
- `Mathlib.Combinatorics.SimpleGraph.Finite` - Finite graph theory
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum` - **Degree sum lemmas (handshaking!)**
- `Mathlib.Data.Fintype.Card` - Finite type cardinality
- `Mathlib.Data.Fin.Basic` - Finite natural numbers
- `Mathlib.Data.Finset.Card` - Finite set cardinality
- `Mathlib.Data.Finset.Image` - Set image operations
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic` - **Sum operations**
- `Mathlib.Tactic` - All tactics (including `omega`, `decide`)

## Key Arguments Used

### 1. **Finset Cardinality & Partition Arguments**

#### Already in Mathlib ✓
- `Finset.card_le_card` - subset cardinality inequality
- `Finset.exists_subset_card_eq` - extract subset of given size
- `Finset.card_union_of_disjoint` - partition cardinality
- `Finset.card_insert_of_notMem` - insert cardinality
- `Finset.card_map` - map preserves cardinality
- `Finset.card_eq_two` - characterize 2-element sets
- `Finset.card_le_univ` - bound by universe size
- `Finset.card_sdiff` - difference cardinality
- `Finset.card_erase_of_mem` - erase cardinality

#### Need to Prove Locally
- Partition arguments for vertex neighborhoods (domain-specific)
- Disjointness of P and Q in the final contradiction
- Specific cardinality constraints from regularity

### 2. **Double-Counting Arguments**

#### Core Pattern (used multiple times)
The proof uses double-counting extensively:

```lean
-- Example from Basic.lean:692-693
-- "Each of v's 5 neighbors has degree 5, uses 1 edge to v"
-- ∑ deg(neighbor) counts edges from both sides
```

**Key instances:**
1. **Edge counting** (line 1066): Count edges between neighbor sets
2. **P-Q edge counting** (line 2624): `P.sum(Q-neighbors) = Q.sum(P-neighbors)`
3. **Matching argument** (line 3272): Find p₁, p₂ with common Q-non-neighbors
4. **Handshaking lemma variants** (line 2417)

#### In Mathlib ✓
- `SimpleGraph.sum_degrees_eq_twice_card_edges` - basic handshaking lemma
- `Finset.sum_bij` - bijection principle for sums

#### Need to Prove Locally
- **Application to bipartite edge counting** (between P, Q, N(v))
- **Specific double-counting for matching construction** (Case 2 of final_contradiction)
- Edge constraints from triangle-free + regularity

### 3. **Degree Arguments**

#### Already in Mathlib ✓
- `SimpleGraph.degree` - degree of a vertex
- `SimpleGraph.card_neighborFinset_eq_degree` - degree = |neighbors|

#### Defined Locally (SHOULD BE IN MATHLIB!)
- **`neighborSet_indep_of_triangleFree`** (RamseyDef.lean:47-75)
  - **Statement:** In triangle-free graph, neighborhood of any vertex is independent
  - **Importance:** FUNDAMENTAL graph theory fact, used 20+ times
  - **Action:** Submit to Mathlib.Combinatorics.SimpleGraph.Triangle or similar

#### Need to Prove Locally
- `IsKRegular` - k-regular graph predicate (defined in RamseyDef.lean)
- `r35_critical_is_4_regular` - R(3,5) critical graphs are 4-regular
- `claim1_five_regular` - R(3,6) critical graphs are 5-regular
- Degree bounds from independence number

### 4. **Pigeonhole Principle**

#### Used For:
- Minimum degree argument (FiveCycleLemma.lean:41-165)
- Extracting 3 non-neighbors when degree ≤ 1
- Finding non-edges in triangle-free neighborhoods

#### In Mathlib ✓
- `Finset.exists_le_card_fiber_of_mul_le_card` - general pigeonhole
- Various `omega` tactic applications for arithmetic

#### Need to Prove Locally
- Domain-specific applications to graph neighborhoods

### 5. **Matching & Independent Set Arguments**

#### Pattern:
- Triangle-free ⟹ neighborhoods are independent
- Use to construct larger independent sets
- Combine with pigeonhole to find structures

#### In Mathlib ✓
- `SimpleGraph.IsIndepSet` - independence predicate
- `SimpleGraph.IsClique` - clique predicate
- `SimpleGraph.TriangleFree` - triangle-free predicate

#### Need to Prove Locally
- `NoKIndepSet` - no k-independent set predicate (defined locally)
- Five-cycle structural lemma (FiveCycleLemma.lean)
- Matching construction in Case 2 (Basic.lean:3243-3749)

## Critical Missing Pieces

## Locally-Defined Lemmas That Should Be in Mathlib

### CONFIRMED - Already Defined Locally

1. **`neighborSet_indep_of_triangleFree`** (RamseyDef.lean:47-75) ⭐ TOP PRIORITY
   - In triangle-free graph, neighborhood of any vertex is independent
   - Used extensively throughout the proof
   - **Submit to:** `Mathlib.Combinatorics.SimpleGraph.Triangle`

2. **`degree_le_of_triangleFree_no_indep`** (RamseyDef.lean:78-103)
   - Triangle-free + no k-IS ⟹ degree ≤ k-1
   - Combines triangle-free with independence constraints
   - **Submit to:** `Mathlib.Combinatorics.SimpleGraph.Basic`

3. **`IsNIndepSet`** (RamseyDef.lean:32-33)
   - Independence set with specified cardinality
   - Compare with existing `IsNClique` in Mathlib
   - **Check if similar exists, otherwise submit**

### High Priority (blocking progress)

2. **Edge counting between partition classes**
   - Count edges between P, Q, N(v) using regularity
   - Uses double-counting + disjoint partition

3. **Matching existence via double-counting** (Case 2)
   - Find pair p₁, p₂ ∈ P with many common Q-non-neighbors
   - Clever pigeonhole argument on sum of non-neighbors

### Medium Priority (marked sorry)

4. **Unique element from card = 1** (line 2851)
   - Extract witness from `S.card = 1`
   - **Check Mathlib for** `Finset.card_eq_one`

5. **Disjointness lemmas for P ∩ Q = ∅**
   - Many `sorry`s for proving x ∈ P ⟹ x ∉ Q
   - Should follow from partition construction

6. **Vertex distinctness** (lines 3611-3684)
   - Many `sorry`s proving v ≠ q₁, p₁ ≠ q₂, etc.
   - Should follow from partition membership + disjointness

### Low Priority (deferred proofs)

7. **5-cycle structural lemma** (SmallRamsey.lean:1165)
   - R(3,4) = 9 constructive proof
   - Can use `sorry` + computational verification

8. **Connectedness argument** (Basic.lean:5208)
   - Bipartite graph connectivity
   - Deferred to later

## Recommended Search Strategy

### Phase 1: Core Mathlib Lemmas (search these)
```lean
-- Finset operations
Finset.card_eq_one
Finset.sum_partition
Finset.disjoint_iff_inter_eq_empty

-- Graph theory
SimpleGraph.neighborSet_indep_of_triangleFree  -- VERIFY THIS
SimpleGraph.Adj.ne  -- x ~ y ⟹ x ≠ y
SimpleGraph.degree_sum

-- Arithmetic
Nat.div_le_of_le_mul  -- for pigeonhole
```

### Phase 2: Standard Graph Theory (likely need to add)
```lean
-- Regular graphs
IsKRegular_iff_all_degrees_eq_k
degree_sum_eq_card_mul_k  -- for k-regular

-- Triangle-free implications
triangle_free_neighborSet_indep
triangle_free_degree_bound

-- Independence
indep_subset  -- subset of independent set is independent
```

### Phase 3: Double-Counting Utilities (definitely need to add)
```lean
-- Bipartite edge counting
bipartite_edge_count_eq_sum_degrees
bipartite_double_count

-- Matching arguments
exists_pair_with_common_neighbors_via_pigeonhole
```

## Edge Cases to Handle

1. **Empty set edge cases** - most handled by `omega` tactic
2. **Distinctness from membership** - P ∩ Q = ∅ ⟹ x ∈ P ⟹ x ∉ Q
3. **Vertex count arithmetic** - 18 = 1 + 5 + 5 + 7 (v + N(v) + P + Q)
4. **Degree constraints** - 5-regular with 18 vertices ⟹ total degree = 90

## Next Steps

1. **Search Mathlib for:**
   - `SimpleGraph.neighborSet` operations
   - `IsIndepSet` lemmas
   - `Finset.card_eq_one` and extraction
   - Degree sum formulas

2. **Create local utilities:**
   - `partition_vertex_neighborhoods.lean` - helper lemmas for P/Q partition
   - `double_counting.lean` - bipartite edge counting
   - `triangle_free_helpers.lean` - implications of triangle-free property

3. **Fill in edge case `sorry`s:**
   - Distinctness lemmas (automated with `simp` + partition facts)
   - Cardinality arithmetic (use `omega`)
   - Disjointness consequences

## File Structure Recommendation

```
Ramsey36/
├── Helpers/
│   ├── FinsetPartition.lean      -- Partition cardinality lemmas
│   ├── DoubleCounting.lean       -- Bipartite edge counting
│   ├── TriangleFree.lean         -- Triangle-free implications
│   └── RegularGraphs.lean        -- k-regular graph lemmas
├── Basic.lean                     -- Main proof (use helpers)
├── FiveCycleLemma.lean           -- Structural lemma
└── ...
```

This organization separates "should be in Mathlib" (Helpers/) from "specific to Ramsey" (Basic.lean).

## ACTION ITEMS SUMMARY

### Immediate (Do Now)
1. ✅ **DONE:** Cataloged all partition/inequality arguments
2. ✅ **DONE:** Identified locally-defined lemmas vs Mathlib
3. 🔧 **TODO:** Verify if `IsNIndepSet` already exists in Mathlib (search for similar)
4. 🔧 **TODO:** Check if `Finset.card_eq_one` exists (likely yes, verify syntax)
5. 🔧 **TODO:** Search Mathlib for bipartite edge-counting lemmas

### Short-term (This Week)
1. Extract `neighborSet_indep_of_triangleFree` + tests → submit to Mathlib
2. Create `Helpers/` directory structure
3. Fill in distinctness/disjointness `sorry`s (mostly mechanical)
4. Add cardinality extraction lemmas (e.g., from `card = 1`)

### Medium-term (This Month)
1. Complete double-counting utilities
2. Prove or axiomatize R(3,4)=9, R(3,5)=14
3. Complete Case 2 matching construction
4. Review all `sorry`s and prioritize

### Long-term (Mathlib Submission)
1. Package triangle-free lemmas for Mathlib PR
2. Package degree/regularity lemmas
3. Package Ramsey-specific definitions (if general enough)

## Quick Reference: Key Mathlib Searches

```bash
# Search for these in Mathlib documentation/source:
- SimpleGraph.IsNIndepSet vs IsIndepSet
- Finset.card_eq_one / card_eq_succ
- SimpleGraph.sum_degrees_eq_twice_card_edges (handshaking)
- Finset.sum_bij / sum_partition (double counting)
- neighborSet properties in Triangle.lean (if exists)
```

---

**Last Updated:** 2025-11-27
**Status:** Initial survey complete, ready for detailed Mathlib search
**Edge Cases Identified:** ~40 `sorry`s, mostly mechanical distinctness proofs
