# Formal Refutation of Goertzel's 4CT Proof - KERNEL VERIFIED

## Summary

This directory contains **kernel-verified proofs** in Megalodon demonstrating
that a claimed proof of the Four Color Theorem using face generators and
Kempe chain operations contains a fundamental mathematical error. All proofs
pass Megalodon kernel verification with **Exit: 0**.

## Core Result

**Lemma 4.3 is false**: The claimed equality

```
X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R  (boundary)
```

is wrong. The correct result is:

```
X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_{A∪A'}  (interior)
```

This is because R is common to both (R∪A) and (R∪A'), so it **cancels** in
the symmetric difference. The error is the **exact opposite** of the claim.

## Verified Files

| File | Status | Description |
|------|--------|-------------|
| `lemma43_refutation.mg` | ✓ VERIFIED | **CORE**: Symmetric diff gives interior, not boundary |
| `cascade_analysis.mg` | ✓ VERIFIED | **CORE**: Cascade failure and impossibility theorem |
| `blocker1_full.mg` | ✓ VERIFIED | Complete IFF characterization |
| `blocker2_full.mg` | ✓ VERIFIED | Edge constraint proof |
| `blocker3_full.mg` | ✓ VERIFIED | Kempe chain constraint proof |
| `xor_full.mg` | ✓ VERIFIED | Complete F₂² XOR table (16 cases) |
| `symm_diff.mg` | ✓ VERIFIED | Symmetric difference theorems |
| `blocker1.mg` | ✓ VERIFIED | Per-run XOR domain |
| `blocker2.mg` | ✓ VERIFIED | Chain existence pattern |
| `blocker3_birkhoff.mg` | ✓ VERIFIED | Birkhoff Diamond pattern |
| `xor_self_inverse.mg` | ✓ VERIFIED | XOR self-inverse: c ⊕ c = 0 |

## Key Theorems

### From `lemma43_refutation.mg`:

```megalodon
Theorem symm_diff_RA_RAp_forward :
  forall x:set, x :e (RA :\: RAp) :\/: (RAp :\: RA) -> x :e interior.

Theorem symm_diff_RA_RAp_backward :
  forall x:set, x :e interior -> x :e (RA :\: RAp) :\/: (RAp :\: RA).

Theorem boundary_not_in_symm_diff :
  forall x:set, x :e R -> ~(x :e (RA :\: RAp) :\/: (RAp :\: RA)).
```

### From `cascade_analysis.mg`:

```megalodon
Theorem goertzel_claim_false :
  ~(symm_diff_result = R).

Theorem lemma44_instantiation_impossible :
  ~(forall x:set, x :e symm_diff_result <-> x :e R).
```

## Why This Error Is Fatal

1. **Lemma 4.3 is wrong**: XOR gives interior, not boundary
2. **Lemma 4.4 cannot be instantiated**: The SwitchData requirement fails
3. **Span argument collapses**: Without 4.3/4.4, theorems 4.8-4.10 don't follow
4. **Entire proof avenue blocked**: The purification mechanism cannot work

## Verification

```bash
cd megalodon

# Verify core theorems
./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs 4CT/lemma43_refutation.mg
./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs 4CT/cascade_analysis.mg

# Verify all files
for f in 4CT/*.mg; do
  ./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs "$f" && echo "$f: VERIFIED"
done
```

## Paper

The LaTeX paper `paper.tex` provides a complete mathematical exposition:

```bash
cd 4CT
pdflatex paper.tex
```

## What This Does NOT Claim

1. **NOT** "The Four Color Theorem is false" - The 4CT is TRUE
2. **NOT** "No algebraic proof can work" - Different approaches may succeed
3. **NOT** "The abstract lemmas are wrong" - They're valid, just not instantiable

We **only** claim: This specific purification mechanism with these specific
face generator definitions cannot work due to the symmetric difference error.

## References

1. Appel, K. and Haken, W. (1976). "Every planar map is four colorable."
2. Gonthier, G. (2008). "Formal proof—the four-color theorem."
3. Heawood, P.J. (1890). "Map colour theorem." (Identified Kempe's error)
