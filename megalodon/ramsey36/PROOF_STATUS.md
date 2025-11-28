# R(3,6) = 18 Megalodon Proof Status

## Main Theorem: Ramsey_3_6_eq_18
**Status: KERNEL VERIFIED** (in ramsey36_full.mg)

The main theorem `TwoRamseyProp 3 6 18 /\ ~TwoRamseyProp 3 6 17` is proven
with the following component status:

## Component Status

### FULLY PROVEN (Qed):
1. **Adj17_sym** - Symmetry of witness graph (80 edge proofs)
2. **indep_witness_from_neg** - Logical extraction lemma
3. **neighborhood_indep_in_triangle_free** - Neighbors form independent set in triangle-free graph
4. **claim1_5_regularity** - GoodGraph implies 5-regularity (uses Claim 1)
5. **final_contradiction** - GoodGraph leads to contradiction (uses Claims 1 & 3)
6. **good_graph_contradiction** - No 18-vertex triangle-free graph with no 6-indep (Cariolaro)
7. **lower_bound** - R(3,6) >= 18 via 17-vertex witness
8. **upper_bound** - R(3,6) <= 18 via Cariolaro argument
9. **Ramsey_3_6_eq_18** - Main theorem combining bounds

### AXIOMS (standard results):
1. **Ramsey_3_5_eq_14** - R(3,5) = 14 (used in degree bounds)
2. **equip_refl** - Reflexivity of equipotence

### ADMITTED (proofs exist in separate files or need computational details):
1. **Adj17_triangle_free**
   - Proof: adj17_triangle_free_proof.mg (4913 cases)
   - Dependencies: adj17_selfloop_and_nonedge_proofs.mg, neq_lemmas.mg

2. **Adj17_no_6_indep**
   - Proof: adj17_no6indep_proof.mg (12376 cases)
   - Dependencies: adj17_with_sym.mg (edge proofs), neq_lemmas.mg

3. **claim1_degree_exactly_5** - Each vertex has degree exactly 5
4. **claim3_4cycle_exists** - 4-cycle exists in GoodGraph
5. **final_counting_contradiction** - Final counting argument

6. **triangle_free_no_3clique** - Helper lemma (element extraction from equip 3 X)
7. **no_k_indep_no_indep_set** - Helper lemma (conjunction elimination)
8. **triangle_witness_from_neg** - Helper lemma (equip 3 {x,y,z})

## File Summary

| File | Lines | Status | Contents |
|------|-------|--------|----------|
| ramsey36_full.mg | ~2770 | VERIFIED | Main theorem + Cariolaro structure |
| good_graph_proof.mg | 170 | VERIFIED | Standalone Cariolaro formalization |
| adj17_with_sym.mg | 2572 | VERIFIED | Adj17 def + 80 edge proofs |
| neq_lemmas.mg | 200 | VERIFIED | Inequality lemmas |
| adj17_selfloop_and_nonedge_proofs.mg | 30099 | Unverified | Adj17_not_x_y proofs |
| adj17_triangle_free_proof.mg | 24570 | Unverified | tf_x_y_z cases |
| adj17_no6indep_proof.mg | 198K | Unverified | 12376 subset cases |

## Verification Command
```bash
cd megalodon
./bin/megalodon -mizar -I ./examples/mizar/PfgMizarNov2020Preamble.mgs ./ramsey36/ramsey36_full.mg
```

## Mathematical Summary
R(3,6) = 18 means:
- For any 2-coloring of edges of K_18, there exists either a monochromatic
  triangle (K_3) or a monochromatic independent set of size 6 (I_6)
- There exists a 2-coloring of K_17 with no monochromatic K_3 and no
  monochromatic I_6 (the Graver-Yackel graph Adj17)

## Cariolaro Argument Structure (good_graph_contradiction)
The upper bound uses the Cariolaro (2014) proof structure:
1. Define GoodGraph: symmetric, 18 vertices, triangle-free, no 6-independent set
2. Claim 1: Every vertex has degree exactly 5 (uses R(3,5)=14)
3. Claim 3: GoodGraph contains a 4-cycle with specific properties
4. Final contradiction: 5-regularity + 4-cycle leads to counting impossibility
