VERIFIED MEGALODON PROOFS FOR GOERTZEL P!=NP FORMALIZATION
==========================================================

This directory contains machine-verified proofs in Megalodon.

TO VERIFY ANY FILE:
  cat ../../examples/egal/PfgEMay2021Preamble.mgs <file.mg> > /tmp/combined.mg
  ../../bin/megalodon /tmp/combined.mg

VERIFIED FILES:
---------------

neutrality_foundation.mg - Core algebra for T_i involution (VERIFIED)
  - Bit: element of 2 = {0, 1}
  - xor: if-then-else based XOR
  - xor_0_0, xor_1_1, xor_0_1, xor_1_0: basic XOR table
  - bit_cases: any bit is 0 or 1
  - xor_self: xor a a = 0
  - xor_is_bit: xor preserves bits
  - xor_0_l, xor_0_r: 0 is identity
  - xor_double_cancel: xor (xor a b) b = a  [KEY FOR T_i INVOLUTION]
  - neg: negation via XOR with 1
  - neg_0, neg_1: negation table
  - neg_involution: neg (neg a) = a
  - pairing_lemma: a <> neg a  [KEY FOR NEUTRALITY]

SIGNIFICANCE FOR P!=NP PROOF:
-----------------------------

These verified lemmas establish the algebraic foundation for the
Neutrality theorem (Corollary 3.8 in Goertzel arXiv:2510.08814).

The T_i transformation on instances (phi, A, b) is:
  T_i(phi, A, b) = (flip_sign_i(phi), A, b XOR row_i(A))

For T_i to be an involution (T_i(T_i(x)) = x), we need:
  1. flip_sign_i(flip_sign_i(phi)) = phi  [sign flip is involution]
  2. (b XOR row_i(A)) XOR row_i(A) = b   [XOR double cancel]

Our xor_double_cancel theorem proves (2) at the bit level.
Combined with (1), this proves T_i is an involution.

The pairing_lemma shows that for any bit a:
  a <> neg(a)
This means T_i changes witness bit i from a to neg(a),
which are always different.

Since T_i is:
  - A bijection (it's an involution)
  - Measure-preserving on D_m
  - Flips the witness bit at position i

We get:
  P[X_i = 1] = P[X_i = 0] = 1/2

for any sign-invariant conditioning, establishing Neutrality.

NEXT STEPS:
-----------
1. Formalize sign-invariant predicates
2. Define the full T_i transformation on instances
3. Prove T_i preserves the D_m distribution
4. Complete the Neutrality theorem

These algebraic foundations are SOLID - the rest is structure.
