(* P != NP Formalization: Critical Analysis of Switching *)
(* Deep dive into potential failure modes *)

(* ============================================================ *)
(* THE CORE QUESTION: DOES SWITCHING ACTUALLY WORK?             *)
(* ============================================================ *)

(*
The switching theorem claims:
  Any short decoder P becomes per-bit local after wrapping.

This relies on a CIRCULAR argument:
  1. If P is "inherently local", then H captures P's behavior
  2. If P is "inherently non-local", then P fails due to neutrality

The gap: What if P is "semi-local" - uses some global structure
but not enough to be captured by neutrality?
*)

(* ============================================================ *)
(* ATTEMPT 1: CONSTRUCT A COUNTEREXAMPLE DECODER                *)
(* ============================================================ *)

(*
Consider a decoder P that:
  - Looks at the XOR of ALL solution bits: parity = X_1 XOR X_2 XOR ... XOR X_m
  - If parity = 0, output X_1 (guess first bit correctly)
  - If parity = 1, output random

This decoder uses GLOBAL information (parity of all bits).
But parity is sign-invariant under individual T_i!

Wait - is parity sign-invariant?
  T_i flips X_i, so parity -> 1 - parity.
  No, parity is NOT sign-invariant.

So the neutrality argument applies: P cannot compute parity
better than 1/2 when conditioned on sign-invariant features.

Actually, can P compute parity at all from Phi?
The decoder sees Phi = F^h, not X directly.
To compute parity(X), P would need to solve the instance!

So this counterexample doesn't work because P can't compute parity.
*)

(* ============================================================ *)
(* ATTEMPT 2: A DECODER THAT USES FORMULA STRUCTURE             *)
(* ============================================================ *)

(*
Consider a decoder P that:
  - Analyzes the masked formula Phi's clause structure
  - Looks for "special" clauses that reveal information
  - Uses this to guess some bits

Example: If variable i appears in very few clauses,
maybe P can infer something about X_i.

But: The masking (pi, sigma) is random and independent of F.
So the "special structure" of Phi is uniformly distributed.

And: The sparsification theorem says local structure is tree-like.
So any structure P detects is either:
  (a) Truly local, and captured by H
  (b) Global, and has sign-invariant distribution

This suggests switching DOES work, but the argument is subtle.
*)

(* ============================================================ *)
(* ATTEMPT 3: A DECODER THAT MEMORIZES                          *)
(* ============================================================ *)

(*
Consider a decoder P that:
  - Has a lookup table for "special" formulas
  - If Phi matches a known formula, output the stored witness
  - Otherwise, output random

This decoder has description length |P| = O(table_size * m).
For the table to be useful, we need table_size * m <= delta * t = O(m).
So table_size = O(1).

With only O(1) formulas memorized, the probability of a random
D_m instance matching is 2^{-Omega(m)} (negligible).

So this decoder fails on almost all instances.
Not a counterexample.
*)

(* ============================================================ *)
(* ATTEMPT 4: A DECODER USING INTER-BLOCK CORRELATIONS          *)
(* ============================================================ *)

(*
Consider a decoder P that:
  - Looks at correlations BETWEEN blocks (Phi_1, ..., Phi_t)
  - Uses block j's structure to help decode block j'

But: Blocks are i.i.d. by construction.
There are no correlations to exploit.

The only "correlation" is that all blocks share the same decoder P.
This is what the switching argument exploits!

Switching says: If P uses the same logic across blocks,
we can distill that logic into a hypothesis h.
*)

(* ============================================================ *)
(* THE KEY INSIGHT: WHY SWITCHING WORKS                         *)
(* ============================================================ *)

(*
The switching argument works because of a TENSION:

1. P is SHORT (|P| <= delta * t bits)

2. P operates on MANY BLOCKS (t blocks)

3. Each block is COMPLEX (m bits of witness, exp(m) possible instances)

Implication:
  P cannot "hardcode" different behavior for each block.
  P must use SHARED LOGIC across blocks.

  The bits in P's description must be "reused" across many blocks.
  With |P| = O(t) bits and t blocks, each bit is used O(1) times per block.

  This means P's computation on each block is essentially the same,
  with only O(1) bits of "customization" per block.

The ERM distillation captures this shared logic.
The hypotheses h_i represent the "core" of P's computation,
which is reused across all test blocks.

THIS IS THE QUANTALE WEAKNESS PRINCIPLE:
  Short programs must be "weak" in the sense that they
  reuse computation across their inputs.
  This reuse can be extracted and analyzed.
*)

(* ============================================================ *)
(* FORMALIZING THE REUSE ARGUMENT                               *)
(* ============================================================ *)

(* A program P of length L can be viewed as a Boolean circuit
   with L + O(input_size) gates.

   When applied to t independent blocks, P "reuses" its gates.
   The internal state of P while processing block j
   depends on:
   - The L bits of P's description
   - The O(m) bits of block j's input
   - The O(m * j) bits of previous blocks (if any)

   Key: If P processes blocks independently (which it must for
   the K_poly complexity bound), then the processing of block j
   depends only on O(L + m) bits.

   With L = O(t) and t = O(m), this is O(m) bits per block.
   This is exactly what "local" means in the hypothesis class H!
*)

Theorem reuse_implies_local :
  forall p, Program p -> strlen p c= nat_mult delta t ->
    (* P's behavior on block j depends on O(m) bits *)
    forall j :e t, exists local_bits :e omega,
      local_bits c= nat_mult 2 m /\
      (* P's output on block j is a function of these bits *)
      True.
Admitted.

(* ============================================================ *)
(* THE REMAINING GAP: SYMMETRIZATION                            *)
(* ============================================================ *)

(*
Even if P's behavior is "local" in the sense above,
it might depend on SIGN-SENSITIVE features.

Example: P might output X_i if some formula property Q(Phi) holds,
where Q is NOT sign-invariant.

The symmetrization step addresses this:
  By averaging P over sign-flip involutions,
  we get a decoder P' that only depends on sign-invariant features.

Formally: P'(Phi) = majority_vote_{I in family} P(T_I(Phi))

where T_I is a composition of T_i involutions.

Claim: P' depends only on sign-invariant features of Phi.

Proof sketch:
  For any sign-sensitive feature f(Phi),
  the symmetrization family "averages out" f.
  P' sees only the sign-invariant projection of Phi.

But: Does this actually work with a FINITE symmetrization family?

If the family has size |F| = polylog(m), and there are exp(m) possible
sign configurations, then most configurations are NOT in the family.

The argument must be that:
  With polylog(m) random involutions, the average of P
  APPROXIMATES the expectation over ALL involutions.

This is a CONCENTRATION argument.
It should work if P has bounded sensitivity to each involution.
*)

(* ============================================================ *)
(* ANALYZING SYMMETRIZATION CONCENTRATION                       *)
(* ============================================================ *)

(*
Let f(Phi) = P(Phi) be the decoder's output (a bit).
Let E[f] be the expectation over all sign configurations.

Symmetrization computes:
  f'(Phi) = (1/|F|) * sum_{I in F} f(T_I(Phi))

We want: |f'(Phi) - E[f]| is small with high probability.

By Hoeffding's inequality:
  P[|f' - E[f]| > epsilon] <= 2 * exp(-2 * epsilon^2 * |F|)

With |F| = (log m)^2 and epsilon = m^{-0.1}:
  RHS <= 2 * exp(-2 * m^{-0.2} * (log m)^2)
       = 2 * exp(-2 * (log m)^2 / m^{0.2})

For large m, (log m)^2 / m^{0.2} -> 0, so RHS -> 2.
This bound is USELESS!

PROBLEM: Hoeffding requires |F| = Omega(1/epsilon^2) samples.
For epsilon = m^{-c}, we need |F| = Omega(m^{2c}) samples.
But we only have polylog(m) samples!

CRITICAL ISSUE: Symmetrization might not concentrate with polylog samples.
*)

(* ============================================================ *)
(* ALTERNATIVE: STRUCTURED SYMMETRIZATION                       *)
(* ============================================================ *)

(*
The paper might use a more structured approach:
  Instead of random involutions, use a COVERING family.

A covering family F is one where:
  For any sign-sensitive feature f with "low complexity",
  there exists I in F such that f and f . T_I are "different".

With such a family, the majority vote over F
removes all low-complexity sign-sensitive features.

The size of such a covering family depends on what "low complexity" means.
For complexity = poly(log m), we might need |F| = poly(m) or more.

This would change the description length analysis!
*)

(* ============================================================ *)
(* CHECKING THE PAPER'S CLAIM                                   *)
(* ============================================================ *)

(*
The paper claims symmetrization works with polylog(m) samples.
This requires one of:
  1. A non-standard concentration argument
  2. Structured covering families
  3. A different notion of "symmetrization"

Let me re-read the paper's approach...

From the paper:
  "Symmetrization wrapper applies a polylogarithmic multiset of
   promise-preserving block automorphisms"

  "takes majority vote over the resulting surrogate labels"

The key might be that we're not approximating E[f] for arbitrary f.
We're specifically interested in the SURROGATE LABELS Y~_{j,i}.

If Y~_{j,i} is close to X_{j,i} (the true label),
then ERM on Y~ generalizes to X.

The paper claims (Lemma 4.8, Lemma A.16):
  "Optimal predictor for surrogate Y~ equals optimal predictor for truth X"

This is a CALIBRATION claim.
Even if Y~ != X, if the optimal predictor of Y~ is the same as
the optimal predictor of X, then learning Y~ suffices.

This is a clever way to avoid concentration issues!
We don't need Y~ = X; we just need them to have the same optimal predictor.
*)

Theorem calibration_key :
  (* The optimal predictor for symmetrized surrogate equals
     the optimal predictor for truth *)
  forall p family h,
    (* h optimal for predicting symmetrized P output *)
    True ->
    (* h is also optimal for predicting true witness bit *)
    True.
Admitted.

(* ============================================================ *)
(* FINAL ANALYSIS OF SWITCHING                                  *)
(* ============================================================ *)

(*
SWITCHING-BY-WEAKNESS: DETAILED VERDICT

COMPONENTS:
1. Short programs reuse logic (OK - follows from information theory)
2. ERM generalizes (OK - standard learning theory)
3. Symmetrization removes sign-sensitivity (SUBTLE - relies on calibration)
4. Description length is O(log m + log t) (OK - wrapper encodes algorithm)

THE SUBTLE PART:
  Symmetrization doesn't need concentration.
  It relies on CALIBRATION: the optimal predictor is preserved.

  This is plausible because:
  - T_i is measure-preserving
  - T_i toggles exactly one bit
  - The optimal predictor for X_i must be sign-invariant

  If the optimal predictor is sign-invariant, then:
  - Symmetrization doesn't change it
  - ERM finds the same predictor from surrogate labels as from true labels

REMAINING QUESTIONS:
  1. Is the calibration lemma (Lemma A.16) correct?
  2. Does polylog(m) symmetrization suffice for the calibration?
  3. Are there edge cases where calibration fails?

RISK ASSESSMENT:
  The switching argument is CLEVER and PLAUSIBLE.
  The main risk is in the calibration lemma.
  Without full proof of calibration, we can't be certain.

  Risk level: MEDIUM
  (Lower than I initially thought, but still non-trivial)
*)

(* ============================================================ *)
(* WHAT COULD STILL GO WRONG                                    *)
(* ============================================================ *)

(*
POTENTIAL FAILURE 1: Calibration might fail

  The calibration claim assumes the optimal predictor is sign-invariant.
  But what if there are MULTIPLE optimal predictors,
  and some are sign-invariant while others are not?

  In that case, ERM might find a sign-sensitive predictor
  that works on training data but fails on test data
  (where symmetrization has changed the signs).

POTENTIAL FAILURE 2: Non-uniform behavior

  The switching argument assumes P behaves "uniformly" across blocks.
  What if P has special behavior for a SMALL subset of blocks?

  Example: P succeeds on blocks 1, 2, ..., log(t) by memorization,
  and fails on the rest.
  ERM would find a predictor that works on "most" blocks,
  but P's actual success rate is only log(t)/t.

  This might not break the argument, but it requires careful handling.

POTENTIAL FAILURE 3: The hypothesis class might be wrong

  The paper assumes H contains poly(log m)-size circuits.
  But what if the "right" predictor needs slightly larger circuits?

  Example: If the best predictor has size (log m)^{10},
  and H only contains size (log m)^{2} circuits,
  then ERM finds a suboptimal predictor.

  This could degrade the success rate significantly.
*)

Theorem potential_failures :
  (* Identified potential failure modes for switching *)
  True.
exact TrueI.
Qed.

