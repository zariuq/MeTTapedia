# Formalization Analysis: R(3,6) = 18

## Paper Summary

**Title**: On the Ramsey number R(3,6)  
**Author**: David Cariolaro (Academia Sinica, Taiwan)  
**Source**: Australian Journal of Combinatorics, Vol 37 (2007), p. 301-305

### Main Result

**Theorem 1**: R(3,6) = 18

**Meaning**: In any graph with 18 vertices, either:
- There exist 3 mutually adjacent vertices (a triangle/K₃), OR  
- There exist 6 mutually non-adjacent vertices (an independent set of size 6)

And 17 vertices is insufficient (there exists a counterexample).

## Proof Structure

### Part 1: Lower Bound (R(3,6) ≥ 18)
Exhibit a triangle-free graph on 17 vertices with no 6-IS (shown in Figure 1).

**Formalization**: Need to construct the graph and verify properties (decidable/computable).

### Part 2: Upper Bound (R(3,6) ≤ 18)
Prove that any triangle-free graph on 18 vertices contains a 6-IS.

**Proof by contradiction**: Assume G is triangle-free, has 18 vertices, but no 6-IS.

#### Claim 1: G is 5-regular
- Every vertex has degree exactly 5
- Key insight: Triangle-free ⟹ N(v) is independent ⟹ deg(v) ≤ 5
- If deg(v) = 4, derive contradiction using R(3,5) = 14

#### Claim 2: Structure of Non-Neighbors
For any vertex v, among its 12 non-neighbors:
- Exactly 4 vertices (p₁, p₂, p₃, p₄) share 1 neighbor with v
- Exactly 8 vertices (q₁, ..., q₈) share 2 neighbors with v
- The pᵢ's connect to 4 distinct neighbors of v
- The qᵢ's connect to 8 distinct pairs of neighbors

**Technique**: Edge counting between induced subgraphs

#### Claim 3: The p-vertices form a 4-cycle
The 4 vertices {p₁, p₂, p₃, p₄} induce a 4-cycle in G.

**Method**: Detailed case analysis on adjacency structure

#### Final Step: Contradiction
Through careful labeling and exhaustive case analysis, derive that some pair of vertices shares 3 common neighbors, contradicting Claim 2.

## Formalization Feasibility Assessment

### ✅ HIGHLY FORMALIZABLE

**Difficulty**: ⭐⭐⭐ (Medium - similar to Four Color infrastructure)

### Why This is Great for Formalization

1. **Finite and Elementary**
   - Only 18 vertices (finite case analysis)
   - No deep theorems required
   - Self-contained proof

2. **Clean Graph Theory**
   - Uses only: vertices, edges, adjacency, independence, regularity
   - No spectral theory, no probability, no advanced algebra

3. **Structured Proof**
   - Clear claims with explicit dependencies
   - Combinatorial counting arguments (very formalizable)
   - Case analysis (Lean's pattern matching shines here)

4. **Similar to Existing Work**
   - Four Color formalization has graph theory infrastructure
   - Ramsey numbers are studied in mathlib
   - Regular graphs, independent sets well-understood

### Required Infrastructure

#### From Mathlib (Likely Available)
- [ ] Fintype graphs
- [ ] Graph.adjacency, Graph.degree
- [ ] Independent sets
- [ ] Regular graphs
- [ ] Finite graph constructions

#### To Be Developed (Estimated LOC)
- [ ] Ramsey number definition (~20 lines)
- [ ] R(3,5) = 14 (prerequisite, or axiom) (~50-200 lines)
- [ ] The 17-vertex counterexample graph (~100 lines)
- [ ] Triangle-free graphs and properties (~50 lines)
- [ ] Neighborhood intersection counting (~100 lines)
- [ ] Main proof (~500-800 lines)

**Total Estimate**: 800-1200 lines of Lean

### Proof Complexity Breakdown

| Component | Difficulty | LOC Estimate | Notes |
|-----------|-----------|--------------|-------|
| Definitions | ⭐ Easy | 50 | Standard graph theory |
| Counterexample graph | ⭐⭐ Medium | 100 | Decidable verification |
| Claim 1 (5-regular) | ⭐⭐ Medium | 150 | Uses R(3,5), counting |
| Claim 2 (structure) | ⭐⭐⭐ Hard | 300 | Edge counting, careful bookkeeping |
| Claim 3 (4-cycle) | ⭐⭐⭐ Hard | 200 | Complex case analysis |
| Final contradiction | ⭐⭐⭐⭐ Very Hard | 300 | Exhaustive labeling, many cases |

### Potential Challenges

1. **Case Explosion in Final Step**
   - The final contradiction involves labeling 18 vertices
   - Many subcases to track
   - **Mitigation**: Use tactic automation (`fin_cases`, `decide`)

2. **R(3,5) = 14 Dependency**
   - Could formalize separately (another interesting result!)
   - Or axiomatize temporarily
   - **Recommendation**: Formalize R(3,5) first (similar techniques)

3. **Bookkeeping Vertex Sets**
   - Need to track p₁, p₂, p₃, p₄, q₁, ..., q₈, s₁, ..., s₄, t₁, ..., t₄, w₁, ..., w₄
   - **Solution**: Use Lean's dependent types and subtypes

4. **Neighborhood Intersection Counting**
   - Claims involve |N(u) ∩ N(v)| = k
   - Need clean Finset cardinality lemmas
   - **Good news**: Similar to what we just did in NoDigons!

### Recommended Approach

**Phase 1: Infrastructure (2-3 weeks)**
- Set up basic Ramsey number definitions
- Prove or axiomatize R(3,5) = 14
- Develop counting lemmas for neighborhood intersections
- Build the 17-vertex counterexample graph

**Phase 2: Main Proof Structure (2-3 weeks)**
- Formalize Claim 1 (5-regular)
- Formalize Claim 2 (structural decomposition)
- Set up the vertex labeling system

**Phase 3: Case Analysis (3-4 weeks)**
- Formalize Claim 3 (4-cycle)
- Final contradiction with extensive case analysis
- Polish and optimize

**Total Time Estimate**: 7-10 weeks for experienced Lean developer

### Comparison to Four Color

**Similarities**:
- Finite graph theory
- Heavy case analysis
- Needs careful vertex/edge bookkeeping
- Combinatorial counting arguments

**Differences**:
- R(3,6) is MUCH shorter (5 pages vs 200+ pages)
- No planarity, no coloring theory
- More self-contained
- Cleaner mathematical structure

**Verdict**: If you can formalize Four Color, you can DEFINITELY formalize R(3,6)!

## Strategic Value

### Why This is Worth Doing

1. **Accessibility**: Much shorter than Four Color
2. **Educational**: Great teaching example for graph theory formalization
3. **Impact**: First elementary Ramsey number proof in a theorem prover?
4. **Foundation**: Opens door to formalizing other Ramsey numbers (R(3,7), R(4,4))
5. **Beauty**: Elegant proof, satisfying to formalize

### Publication Potential

- Conference: ITP (Interactive Theorem Proving)
- Impact: Demonstrates viability of formalizing classical combinatorics
- Novelty: Computer-free Ramsey proofs are rare; formal verification adds value

## Recommendation

**GO FOR IT!** ✅

This is an excellent formalization target:
- Achievable scope (unlike R(4,5) or R(5,5) which are unknown!)
- Beautiful mathematics
- Builds on existing graph theory
- Natural follow-up to Four Color work
- Great learning project for Lean graph theory

**Suggested First Step**: Formalize R(3,5) = 14 as a warmup (similar techniques, smaller scale).
