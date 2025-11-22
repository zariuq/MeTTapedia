# R(3,6) = 18 Formalization in Megalodon

## Overview

This directory contains a formalization of the Ramsey number R(3,6) = 18 in the Megalodon theorem prover for Proofgold.

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `Adj17_sym` | **Kernel verified** | 2.8s, 2572 lines |
| `neq_lemmas` (10-16) | **Kernel verified** | Extends preamble |
| `Adj17_not_i_j` (190 non-edges) | **Kernel verified** | ~11s, all non-edge proofs |
| `Adj17_path_i_j_k` (316 paths) | **Kernel verified** | Triangle-free witnesses |
| `Adj17_triangle_free` | **Reconstruction WIP** | Needs 4913-case analysis (see below) |
| `Adj17_no_6_indep` | **ATP verified** | Vampire ~7s, 12376 6-subsets to check |
| `lower_bound` | **Kernel verified** | Uses admitted helper lemmas |
| `triangle_free_no_3clique` | Admitted | Helper: triangle_free => no 3-clique |
| `no_k_indep_no_indep_set` | Admitted | Helper: no_k_indep => no k-indep set |
| `upper_bound` | **Structure done** | Needs helper lemmas discharged |
| `Ramsey_3_6_eq_18` | Compiles | Uses bounds |

## Files

- `ramsey36_mizar.mg` - Main proof file (Mizar theory)
- `lower_bound_proof.mg` - Kernel-verified lower_bound proof structure
- `upper_bound_proof.mg` - Upper bound proof structure (helper lemmas admitted)
- `adj17_with_sym.mg` - Kernel-verified Adj17_sym proof (2572 lines)
- `adj17_all_proofs.mg` - Combined proofs: sym + neq + non-edges + paths (30554 lines)
- `adj17_nonedge_proofs.mg` - Non-edge and path lemma proofs
- `neq_lemmas.mg` - Additional inequality lemmas for 10-16
- `gen_adj17_nonedge_proofs.py` - Proof generator for non-edges and paths
- `gen_adj17_nonedge_and_paths.py` - Alternative generator (same functionality)
- `gen_adj17_proofs.py` - Original proof generator (edge theorems)
- `gen_adj17_triangle_free.py` - Analysis script for triangle_free case counts
- `gen_adj17_no6indep.py` - Analysis script for 6-independence verification

## ATP Verification Results

### Adj17_no_6_indep (No 6-vertex independent set)

TPTP file: `/tmp/adj17_no6indep_v3.p`

```
% Vampire 5.0.0
% SZS status Theorem for adj17_no6indep_v3
% Refutation found in ~7 seconds (CASC mode)
```

The graph has:
- 17 vertices (0-16)
- 40 undirected edges (80 directed)
- Maximum independent set size: 5 (82 such sets)
- All 12,376 6-subsets have at least one edge

### Adj17_triangle_free (No triangles)

Verified computationally:
- 316 two-edge paths x→y→z
- 0 triangles (verified by exhaustive check)

## Build Instructions

```bash
cd megalodon
./bin/megalodon -mizar -I examples/mizar/PfgMizarNov2020Preamble.mgs ramsey36/ramsey36_mizar.mg
```

## Theory

Uses Mizar theory (`-mizar` flag) with the Proofgold November 2020 preamble.

Key definitions from the preamble:
- `neq_n_m` axioms for 0-9
- `ordsucc_inj_contra` for generating larger inequalities
- `In_irref`, `In_no2cycle` for ordinal reasoning

## Reconstruction TODO

The ATP-verified theorems need kernel reconstruction:

### Adj17_triangle_free (17³ = 4913 cases)

The theorem `forall x y z :e 17, Adj17 x y -> Adj17 y z -> Adj17 x z -> False` requires:
- Case analysis on (x, y, z) triples
- For each case, use the appropriate non-edge lemma (`Adj17_not_i_j`)

Case breakdown:
- Self-loop cases (x=y or y=z or x=z): 833 (trivial by reflexivity contradiction)
- H1 contradiction (x-y not edge): 2850 cases
- H2 contradiction (y-z not edge): 914 cases
- H3 contradiction (x-z not edge): 316 cases (use path lemmas)

**Blocker**: Megalodon's preamble only has `cases_n` up to n=9. Need `cases_17` axiom or ordinal induction.

### Adj17_no_6_indep (12,376 6-subsets)

Each 6-subset must be shown to contain at least one edge. The witness edge for each subset is computed by `gen_adj17_no6indep.py`.

Both require handling left-associative nested disjunctions in Megalodon.

## Upper Bound Approach (TODO)

The upper bound R(3,6) ≤ 18 requires proving that any 2-coloring of K_18 has a red triangle or blue K_6.

Standard Ramsey recursion gives: R(3,6) ≤ R(2,6) + R(3,5) = 6 + 14 = 20 (not tight enough)

Cariolaro's proof uses three claims:
1. **Claim 1**: A (3,6)-good graph on 18 vertices has ≥ 36 edges
2. **Claim 2**: A (3,6)-good graph on 18 vertices has max degree ≤ 7
3. **Claim 3**: Contradiction from Claims 1 and 2 (18 * 7 / 2 = 63 < 36 * 2 = 72)

These would require:
- Formalization of degree counting
- Case analysis for triangle-free graphs with bounded independent sets
- Possibly ATP assistance for combinatorial enumeration

## References

- Cariolaro, D. "On the Ramsey number R(3,6)". Australian J. Combinatorics 37 (2007), 301-305.
- Graver, J.E. & Yackel, J. "Some graph theoretic results associated with Ramsey's theorem". J. Comb. Theory 4 (1968), 125-175.
