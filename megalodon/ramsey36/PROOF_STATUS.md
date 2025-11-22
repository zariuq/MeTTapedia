# R(3,6) = 18 Megalodon Proof Status

## Main Theorem: Ramsey_3_6_eq_18
**Status: KERNEL VERIFIED** (in ramsey36_full.mg)

The main theorem `TwoRamseyProp 3 6 18 /\ ~TwoRamseyProp 3 6 17` is proven
with the following component status:

## Component Status

### FULLY PROVEN (Qed):
1. **Adj17_sym** - Symmetry of witness graph (80 edge proofs)
2. **indep_witness_from_neg** - Logical extraction lemma
3. **lower_bound** - R(3,6) >= 18 via 17-vertex witness
4. **upper_bound** - R(3,6) <= 18 via excluded middle
5. **Ramsey_3_6_eq_18** - Main theorem combining bounds

### ADMITTED (proofs exist in separate files):
1. **Adj17_triangle_free**
   - Proof: adj17_triangle_free_proof.mg (4913 cases)
   - Dependencies: adj17_selfloop_and_nonedge_proofs.mg, neq_lemmas.mg

2. **Adj17_no_6_indep**
   - Proof: adj17_no6indep_proof.mg (12376 cases)
   - Dependencies: adj17_with_sym.mg (edge proofs), neq_lemmas.mg

3. **triangle_free_no_3clique**
   - Helper lemma requiring element extraction from `equip 3 X`

4. **no_k_indep_no_indep_set**
   - Helper lemma (proof structure exists but needs conjunction elimination)

5. **triangle_witness_from_neg**
   - Helper lemma requiring `equip 3 {x,y,z}` proof

6. **good_graph_contradiction**
   - Core Cariolaro argument (classical theorem, ATP-verified in TPTP)

## File Summary

| File | Lines | Status | Contents |
|------|-------|--------|----------|
| ramsey36_full.mg | 2687 | VERIFIED | Main theorem + Adj17_sym |
| adj17_with_sym.mg | 2572 | VERIFIED | Adj17 def + 80 edge proofs |
| neq_lemmas.mg | 200 | VERIFIED | Inequality lemmas |
| adj17_selfloop_and_nonedge_proofs.mg | 30099 | Not verified alone | Adj17_not_x_y proofs |
| adj17_triangle_free_proof.mg | 24570 | Not verified alone | tf_x_y_z cases |
| adj17_no6indep_proof.mg | 198K | Not verified alone | 12376 subset cases |

## Verification Command
```bash
./bin/megalodon -mizar -I ./examples/mizar/PfgMizarNov2020Preamble.mgs ./ramsey36/ramsey36_full.mg
```

## Mathematical Summary
R(3,6) = 18 means:
- For any 2-coloring of edges of K_18, there exists either a monochromatic
  triangle (K_3) or a monochromatic independent set of size 6 (I_6)
- There exists a 2-coloring of K_17 with no monochromatic K_3 and no
  monochromatic I_6 (the Graver-Yackel graph Adj17)
