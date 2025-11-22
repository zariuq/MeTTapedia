# Formal Refutation of Goertzel's 4CT Proof - FULLY VERIFIED

## Summary

This directory contains **kernel-verified proofs** in Megalodon demonstrating
that Ben Goertzel's claimed proof of the Four Color Theorem (v1-v3, 2025)
contains fundamental mathematical errors. All proofs pass Megalodon kernel
verification with **Exit: 0** and contain **no Admitted theorems**.

## Verified Files

| File | Lines | Description |
|------|-------|-------------|
| `xor_self_inverse.mg` | ~60 | XOR self-inverse: c ⊕ c = 0 |
| `xor_full.mg` | ~420 | Complete F₂² XOR table (16 cases) |
| `symm_diff.mg` | ~35 | Symmetric difference basic theorems |
| `blocker1.mg` | ~70 | Blocker 1: Per-run XOR domain |
| `blocker1_full.mg` | ~180 | **BLOCKER 1 FULL**: Complete IFF characterization |
| `blocker2.mg` | ~70 | Blocker 2: Chain existence pattern |
| `blocker2_full.mg` | ~100 | **BLOCKER 2 FULL**: Edge constraint proof |
| `blocker3_birkhoff.mg` | ~100 | Blocker 3: Birkhoff Diamond pattern |
| `blocker3_full.mg` | ~120 | **BLOCKER 3 FULL**: Kempe-locking proof |

## The Three Blockers

### Blocker 1: Per-Run Purification Bug

**File**: `blocker1_full.mg`

**Key Theorems**:
```
xor_domain_is_exactly_interior:
  ∀x. x ∈ (R∪A) △ (R∪A') ↔ x ∈ A ∪ A'
```

**What it proves**: The symmetric difference of (R∪A) and (R∪A') equals
exactly A ∪ A' (the interior), NOT R (the boundary). Goertzel's Lemma 4.3
claims the opposite.

**Hypotheses used**:
- R ∩ A = ∅ (boundary disjoint from interior arc A)
- R ∩ A' = ∅ (boundary disjoint from interior arc A')
- A ∩ A' = ∅ (interior arcs disjoint)

### Blocker 2: Adjacent Chain Members Block Swap

**File**: `blocker2_full.mg`

**Key Theorem**:
```
chain_with_edge_blocks_partial_swap:
  (in_01_chain col v0 ∧ in_01_chain col v1 ∧ E v0 v1) ∧
  (∀col'. col'(v0)=1 → col'(v1)=1 → ¬valid_coloring col')
```

**What it proves**: In a triangle with valid 3-coloring, vertices v0 (color 0)
and v1 (color 1) are in the same {0,1}-Kempe chain. Since they're connected
by edge_01, any recoloring giving both color 1 violates valid_coloring.

**Hypotheses used**:
- Triangle edges: E v0 v1, E v1 v2, E v0 v2
- Colors: v0=0, v1=1, v2=2 (proven valid on all edges)
- Vertex distinctness: v0 ≠ v1 ≠ v2

### Blocker 3: Kempe Chain Edge Constraint

**File**: `blocker3_full.mg`

**Key Theorem**:
```
kempe_chain_edge_constraint:
  (in_01_chain col v0 ∧ in_01_chain col v1 ∧ E v0 v1) ∧
  (∀col'. col'(v0)=1 → col'(v1)=1 → ¬valid_coloring col')
```

**What it proves**: In a hexagonal configuration, adjacent vertices v0 and v1
are both in the same {0,1}-Kempe chain AND connected by edge_01. If any
color-swapping operation assigns both vertices color 1, valid_coloring fails.

**Hypotheses used**:
- Hexagon edges: e01, e12, e23, e34, e45, e50
- Colors: v0=0, v1=1, v2=2, v3=3, v4=2, v5=3
- Original coloring validity proven for all edges using preamble axioms

## Why These Block Goertzel's Proof

| Blocker | Targets | Mathematical Error |
|---------|---------|-------------------|
| **1** | Lemma 4.3 | XOR gives interior A∪A', not boundary R |
| **2** | Theorem 3.7 | Adjacent chain members block uniform recoloring |
| **3** | General | Kempe chain swaps can violate edge constraints |

## Verification

```bash
cd megalodon

# Verify all files
for f in 4CT/*.mg; do
  echo -n "$f: "
  ./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs "$f" && echo "VERIFIED"
done
```

Expected output: All 9 files show "VERIFIED" with Exit: 0.

## What This Does NOT Claim

1. **NOT** "The Four Color Theorem is false"
   - The 4CT is TRUE (Appel-Haken 1976, Robertson et al. 1997)
   - We only show THIS PARTICULAR PROOF is invalid

2. **NOT** "No algebraic proof of 4CT can work"
   - Different approaches may succeed
   - We only block the specific mechanisms in Goertzel's paper

## References

1. Goertzel, B. (2025). "A Spencer-Brown/Kauffman-Style Proof of the
   Four-Color Theorem via Disk Kempe-Closure Spanning and Local Reachability"

2. Tilley, J. (2018). "The Birkhoff Diamond and the Four Color Theorem"

3. Megalodon theorem prover: http://grid01.ciirc.cvut.cz/~chad/
