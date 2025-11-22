# Formal Refutation of Goertzel's 4CT Proof - VERIFIED

## Summary

This directory contains **kernel-verified proofs** in Megalodon demonstrating
that Ben Goertzel's claimed proof of the Four Color Theorem (v1-v3, 2025)
contains a fundamental mathematical error in Lemma 4.3.

## Verified Files (Exit: 0)

All proofs pass Megalodon kernel verification.

| File | Description | Lines |
|------|-------------|-------|
| `xor_self_inverse.mg` | XOR self-inverse: c XOR c = 0 for all colors | ~40 |
| `xor_full.mg` | Complete F2^2 XOR operation table (16 cases) | ~420 |
| `symm_diff.mg` | Symmetric difference theorems | ~35 |
| `blocker1.mg` | **BLOCKER 1 PROOF** | ~70 |

## The Bug (Blocker 1)

### What Goertzel Claims (Lemma 4.3)

For face generator X^f_{αβ}(C) and Kempe cycle D = R ∪ A ∪ A':
```
X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R    (CLAIMED)
```
This claims the XOR isolates the **boundary run R**.

### What Is Actually True (Proven in blocker1.mg)

```
X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_{A∪A'}    (ACTUAL)
```
The XOR gives the **interior arcs A ∪ A'**, NOT the boundary run R.

### Key Theorems Proven

From `blocker1.mg`:

1. **per_run_xor_domain**: For any x in the symmetric difference (R∪A) △ (R∪A'),
   x must be in A ∪ A' (interior only).

2. **boundary_not_in_xor**: If x is in R (boundary), then x is NOT in the
   symmetric difference (R∪A) △ (R∪A').

**The paper has it exactly backwards.**

## Why This Happens

For run R with Kempe cycle D = R ∪ A ∪ A':
- In coloring C: contribution is on R∪A
- In coloring C^R (after swap): contribution is on R∪A'
- XOR = symmetric difference: (R∪A) △ (R∪A')

Computing the symmetric difference:
- **On R**: Both sets contain R, so R **cancels** (contributes 0)
- **On A**: Only (R∪A) contains A, so A **survives**
- **On A'**: Only (R∪A') contains A', so A' **survives**

Result: (R∪A) △ (R∪A') = A ∪ A' = D \ R

## Verification Commands

```bash
cd /home/user/ai-agents/megalodon

# Verify XOR self-inverse
./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs 4CT/xor_self_inverse.mg

# Verify full XOR table
./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs 4CT/xor_full.mg

# Verify symmetric difference
./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs 4CT/symm_diff.mg

# Verify BLOCKER 1
./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs 4CT/blocker1.mg
```

Exit code 0 = kernel verified.

## Old/Unverified Files

Files with `.old` extension are previous attempts that did not verify.
They should be ignored - only `.mg` files pass the kernel.

## What This Does NOT Claim

1. **NOT** "The Four Color Theorem is false"
   - The 4CT is TRUE (Appel-Haken 1976, computer-verified)
   - We only show THIS PARTICULAR PROOF is invalid

2. **NOT** "No algebraic proof of 4CT can work"
   - Different approaches may succeed
   - We only block the specific per-run purification mechanism

## References

1. **Goertzel, B.** (2025). "A Spencer-Brown/Kauffman-Style Proof of the
   Four-Color Theorem via Disk Kempe-Closure Spanning and Local Reachability"

2. **Megalodon theorem prover**: http://grid01.ciirc.cvut.cz/~chad/
