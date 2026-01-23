# K&S Representation Theorem Core Machinery

This directory contains the core induction machinery for the Knuth-Skilling
representation theorem. The key result is the **B-empty extension step**:
given a k-atom representation, extend it to k+1 atoms.

## Overview

The extension process requires:
1. **δ-choice**: Find the correct value for the new atom
2. **Consistency**: Ensure δ satisfies bounds from all witnesses
3. **Uniqueness**: Prove δ is uniquely determined

## File Structure

```
Core/
├── README.md                      # This file
├── All.lean                       # Aggregates all exports
├── Prelude.lean                   # Basic setup, imports
├── MultiGrid.lean                 # k-dimensional grids, μ function
├── SeparationImpliesCommutative.lean  # Global commutativity from KSSeparation
└── Induction/                     # The extension step
    ├── Construction.lean          # Witness types, DeltaSpec
    ├── DeltaShift.lean            # δ-shift consistency
    ├── ThetaPrime.lean            # chooseδ procedure, base admissibility
    ├── Goertzel.lean              # Separation-driven simplifications + main extension theorem
    ├── KSSeparationBridge.lean    # Bridge: KSSeparation supplies commutativity
    └── HypercubeGap.lean          # Hypercube gap analysis
```

## Key Concepts

### Multi-Index Grids (MultiGrid.lean)

```lean
-- A k-atom family: k distinct atoms above identity
structure AtomFamily (α : Type*) [KnuthSkillingAlgebra α] (k : ℕ) where
  atoms : Fin k → α
  atoms_pos : ∀ i, ident < atoms i
  atoms_distinct : ∀ i j, i ≠ j → atoms i ≠ atoms j

-- Multi-index: how many of each atom
abbrev Multi (k : ℕ) := Fin k → ℕ

-- The grid point: a₀^r₀ ⊕ a₁^r₁ ⊕ ... ⊕ aₖ₋₁^rₖ₋₁
def mu (F : AtomFamily α k) (r : Multi k) : α := ...

-- The k-grid: all reachable points
def kGrid (F : AtomFamily α k) : Set α := { x | ∃ r : Multi k, mu F r = x }
```

### A/B/C Partition (MultiGrid.lean)

For a target `d^u`, partition old grid values:
```lean
-- A: values strictly below target
def extensionSetA (d : α) (u : ℕ) : Set (Multi k) :=
  {r | mu F r < iterate_op d u}

-- B: values exactly equal to target
def extensionSetB (d : α) (u : ℕ) : Set (Multi k) :=
  {r | mu F r = iterate_op d u}

-- C: values strictly above target
def extensionSetC (d : α) (u : ℕ) : Set (Multi k) :=
  {r | iterate_op d u < mu F r}
```

### The δ-Choice Procedure (ThetaPrime.lean)

```lean
-- Separation statistic: Θ(r)/u when r witnesses A/B/C for u
def separationStatistic (R : MultiGridRep F) (r : Multi k) (u : ℕ) : ℝ :=
  R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u

-- Choose δ as the supremum of A-statistics
noncomputable def chooseδ (hk : k ≥ 1) (R : MultiGridRep F)
    (d : α) (hd : ident < d) : ℝ :=
  sSup {separationStatistic R r u | (r, u) ∈ extensionSetA F d u ∧ 0 < u}
```

### DeltaSpec (Construction.lean)

The specification that δ must satisfy:
```lean
structure DeltaSpec (δ : ℝ) where
  hA : ∀ r u, 0 < u → r ∈ extensionSetA F d u → separationStatistic R r u ≤ δ
  hB : ∀ r u, 0 < u → r ∈ extensionSetB F d u → separationStatistic R r u = δ
  hC : ∀ r u, 0 < u → r ∈ extensionSetC F d u → δ ≤ separationStatistic R r u
```

**Key theorem**: `DeltaSpec_unique` - any two values satisfying `DeltaSpec` are equal.

### The Extension Step (Goertzel.lean)

The main extension theorem:
```lean
theorem extend_grid_rep_with_atom_of_KSSeparationStrict
    [KSSeparationStrict α]
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F)
    {d : α} (hd : ident < d) :
    ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        ∀ r : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r t), ...⟩ =
          R.Θ_grid ⟨mu F r, ...⟩ + t * chooseδ hk R d hd
```

## Key Theorems

| Theorem | File | Description |
|---------|------|-------------|
| `DeltaSpec_unique` | Construction.lean | δ is uniquely determined |
| `chooseδ_spec` | ThetaPrime.lean | `chooseδ` satisfies `DeltaSpec` |
| `chooseδBaseAdmissible_of_KSSeparationStrict` | Goertzel.lean | Base admissibility from KSSeparationStrict |
| `newAtomCommutes_of_KSSeparation` | Goertzel.lean | Global commutativity gives NewAtomCommutes |
| `bEmptyExtensionExtra_of_KSSeparationStrict` | Goertzel.lean | Full extra hypotheses auto-constructible |
| `extend_grid_rep_with_atom_of_KSSeparationStrict` | Goertzel.lean | **Main extension lemma** |

## Proof Strategy

### 1. Establishing δ Bounds
- **A-bound**: Statistics from A are ≤ δ (by definition of sSup)
- **C-bound**: Statistics from C are ≥ δ (by contrapositive + Archimedean)
- **B-consistency**: If B is non-empty, statistics are exactly δ

### 2. Base Admissibility
The hardest part: showing `chooseδ` works at ALL base points, not just the
trivial base. This requires:
- `NewAtomCommutes`: The new atom commutes with all old grid points
- `C_strict0`: For small enough u, C is non-empty (strict gap above δ)

These are packaged in `BEmptyExtensionExtra` and derived from `KSSeparationStrict`.

### 3. Grid Extension
Once we have `chooseδBaseAdmissible`, we can:
1. Define `Θ'(joinMulti r t) = Θ(r) + t * δ`
2. Prove `Θ'` is strictly monotone on the extended grid
3. Prove `Θ'` satisfies additivity

## The Hypercube Connection

The A/B/C partition corresponds to modal types in the Stay-Wells hypercube:

| Set | Modal Interpretation |
|-----|---------------------|
| A (below) | `⟨C_<⟩ Below` - reachable below target |
| B (equal) | `⟨C_=⟩ Equal` - exactly at target |
| C (above) | `⟨C_>⟩ Above` - reachable above target |

The δ-choice procedure finds the **equational center** between A and C:
the unique value where the A-bound meets the C-bound.

See `HypercubeGap.lean` for detailed analysis.

## Usage

```lean
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core

-- Use the extension theorem
example [KSSeparationStrict α] {F : AtomFamily α 2} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) {d : α} (hd : ident < d) :
    ∃ F' R', ... := extend_grid_rep_with_atom_of_KSSeparationStrict
      (α := α) (hk := by omega) (R := R) (IH := IH) (H := H) (hd := hd)
```

## Status

**Complete** (2026-01-11):
- ✅ All key theorems proven
- ✅ Builds as part of `Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem` with 0 sorries and 0 warnings
