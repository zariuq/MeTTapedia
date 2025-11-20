# Four Color Theorem - Proof Pattern Curriculum

## Purpose

This curriculum teaches **recurring proof patterns** that block progress in the formalization. Each module starts with a **minimal prototypical example** and builds to the actual application.

## Identified Blocking Patterns

### 🔴 Critical (Blocks multiple proofs)

1. **[Module 1: F₂ Parity Arguments](./01_F2_Parity.lean)**
   - **Pattern**: From `∑ x_i = 0` in `(ZMod 2) × (ZMod 2)`, prove even cardinality of subset
   - **Blockers**: `even_alphaBeta_incident` (KempeAPI:320)
   - **Skills**: ZMod 2 arithmetic, sum partitioning, coordinate decomposition
   - **Prerequisites**: None

2. **[Module 2: Graph Cycle Parity](./02_Cycle_Parity.lean)**
   - **Pattern**: Cycles have even length, XOR sums around cycles are zero
   - **Blockers**: `twoColorUnion_is_even_cycles` (Tait:240), `parity_sum_cycle_zero` (Tait:254)
   - **Skills**: Cycle induction, alternating sums, path composition
   - **Prerequisites**: Module 1

3. **[Module 3: Path XOR Calculus](./03_Path_XOR.lean)**
   - **Pattern**: XOR sums along paths compose correctly
   - **Blockers**: `pathXORSum` (Tait:481), `pathXORSum_concat` (Tait:508)
   - **Skills**: Path concatenation, associativity of XOR, base cases
   - **Prerequisites**: Module 2

### 🟡 Important (Single blockers, high value)

4. **[Module 4: Graph Connectivity](./04_Connectivity.lean)**
   - **Pattern**: Bridge-free graphs are connected
   - **Blockers**: `bridgeless_connected` (Tait:290)
   - **Skills**: Graph connectivity, bridge characterization
   - **Prerequisites**: None

5. **[Module 5: Line Graph Adjacency](./05_Line_Graph.lean)**
   - **Pattern**: Edge adjacency via shared vertex
   - **Blockers**: `adj_iff_shared_edge` (Tait:269), `adj_symm` (Tait:278)
   - **Skills**: Definitional equivalence, symmetry proofs
   - **Prerequisites**: None

### 🟢 Foundation (Geometry axioms - review needed)

6. **[Module 6: Disk Geometry](./06_Disk_Geometry.lean)**
   - **Pattern**: Planar graph properties (faces, spanning trees)
   - **Blockers**: 12 axioms in Disk.lean
   - **Skills**: Planar graph theory, Euler's formula
   - **Prerequisites**: Graph theory background

7. **[Module 7: Rotation Systems](./07_Rotation_Systems.lean)**
   - **Pattern**: Embedding properties, boundary compatibility
   - **Blockers**: 5 axioms in RotationSystem.lean
   - **Skills**: Planar embeddings, rotation orders
   - **Prerequisites**: Module 6

## Learning Path

### Fast Track (Unblock KempeAPI)
1. Module 1 (F₂ Parity) → Completes KempeAPI

### Tait Infrastructure Track
1. Module 5 (Line Graph) - Easy warmup
2. Module 4 (Connectivity) - Medium difficulty
3. Module 2 (Cycle Parity) - Uses Module 1 skills
4. Module 3 (Path XOR) - Builds on Module 2

### Complete Track
Follow numerical order (Modules 1-7)

## How to Use Each Module

Each module contains:
1. **Minimal Example**: Toy problem illustrating the pattern
2. **Mathlib Resources**: Relevant lemmas and tactics
3. **Worked Solution**: Step-by-step proof of minimal example
4. **Exercises**: Progressive difficulty leading to actual blocker
5. **Application**: Complete the actual proof in the formalization

## Success Criteria

- ✅ Module complete: All exercises solved, actual blocker eliminated
- 🔄 Module in progress: Minimal example solved, working on exercises
- 📚 Module started: Reading and understanding pattern

## Current Status

| Module | Pattern | Blockers | Status |
|--------|---------|----------|--------|
| 1 | F₂ Parity | 1 (KempeAPI) | 📚 Ready to start |
| 2 | Cycle Parity | 2 (Tait) | 📚 Ready to start |
| 3 | Path XOR | 2 (Tait) | 📚 Ready to start |
| 4 | Connectivity | 1 (Tait) | 📚 Ready to start |
| 5 | Line Graph | 2 (Tait) | 📚 Ready to start |
| 6 | Disk Geometry | 12 (Disk) | 📚 Needs review |
| 7 | Rotation Systems | 5 (RotationSystem) | 📚 Needs review |

**Total blockers identified**: ~25 axioms/sorries across 7 patterns

---

**Created**: 2025-11-09
**Purpose**: Systematic skill-building to eliminate all unproven statements
**Philosophy**: Learn once, apply many times
