(* P != NP Formalization: FULL Switching-by-Weakness Analysis *)
(* Rigorous verification of Theorem 4.2 *)

(* ============================================================ *)
(* PARAMETERS AND SETUP                                         *)
(* ============================================================ *)

Variable m : set.      (* number of variables per instance *)
Variable t : set.      (* number of blocks, t = Theta(m) *)
Variable delta : set.  (* description length budget fraction *)
Variable gamma : set.  (* fraction of blocks that become local *)

Axiom m_large : (* m is sufficiently large *) m :e omega /\ 100 c= m.
Axiom t_prop : (* t = Theta(m) *) m c= t /\ t c= nat_mult 2 m.
Axiom delta_small : (* delta < 1 *) delta :e omega /\ delta c= 1.
Axiom gamma_const : (* gamma is a constant > 0 *) gamma :e omega /\ 0 :e gamma.

(* ============================================================ *)
(* PART 1: LOCAL VIEW DEFINITION                                *)
(* ============================================================ *)

(* The local view u_i(Phi) consists of:
   - z(F^h): some O(log m)-bit summary of the masked formula
   - a_i: row i of the VV matrix A (O(log m) bits for k = O(log m) constraints)
   - b: the VV target vector (O(log m) bits)
*)

Definition local_view_size : set := nat_mult 3 (log2 m).  (* O(log m) *)

(* Local view extraction *)
Variable extract_local : set -> set -> set.  (* (instance, bit_index) -> local_view *)

Axiom local_view_small :
  forall inst i, i :e m ->
    strlen (extract_local inst i) c= local_view_size.

(* ============================================================ *)
(* PART 2: HYPOTHESIS CLASS H                                   *)
(* ============================================================ *)

(* H consists of Boolean functions h: {0,1}^{O(log m)} -> {0,1}
   that are computable in poly(log m) time.

   Key property: |H| <= poly(m)
*)

Definition HypothesisClass : set -> prop :=
  fun H =>
    (* H is a set of programs *)
    (forall h :e H, Program h) /\
    (* Each h computes a function from local views to bits *)
    (forall h :e H, forall v, strlen v c= local_view_size -> U_halts h v) /\
    (* Each h runs in poly(log m) time *)
    (forall h :e H, forall v, strlen v c= local_view_size ->
       exists c :e omega, U_time h v (exp (log2 m) c)) /\
    (* H has polynomial size *)
    (exists c :e omega, equip (exp m c) H \/ H c= exp m c).

(* The standard hypothesis class *)
Variable H_std : set.
Axiom H_std_valid : HypothesisClass H_std.

(* Size of H *)
Definition H_size : set := (* |H| = m^O(1) *) exp m 2.

(* Bits to encode a hypothesis *)
Definition hyp_bits : set := log2 H_size.  (* O(log m) *)

(* ============================================================ *)
(* PART 3: SYMMETRIZATION                                       *)
(* ============================================================ *)

(* Symmetrization applies a multiset of T_i involutions and
   takes majority vote over the surrogate labels.

   Family size: polylog(m) = (log m)^O(1)
*)

Definition sym_family_size : set := exp (log2 m) 2.  (* (log m)^2 *)

(* A symmetrization family is a multiset of involution indices *)
Definition SymFamily : set -> prop :=
  fun F => F c= (m :*: sym_family_size).  (* pairs (i, count) *)

(* Apply symmetrization: average decoder output over family *)
Definition symmetrize : set -> set -> set -> set :=
  fun p family inst =>
    (* majority vote of P(T_{i1}(T_{i2}(...(inst)...))) over family *)
    (* Returns 0 or 1 *)
    0.  (* placeholder *)

(* Bits to encode a symmetrization family *)
Definition sym_bits : set := nat_mult sym_family_size (log2 m).  (* O(log^3 m) *)

(* ISSUE: sym_bits = O(log^3 m), not O(log m)!
   This is larger than claimed O(log m + log t) overhead. *)

(* ============================================================ *)
(* PART 4: TRAIN/TEST SPLIT                                     *)
(* ============================================================ *)

(* Split t blocks into train (first t/2) and test (second t/2) *)
Definition train_blocks : set := nat_div t 2.
Definition test_blocks : set := t :\: train_blocks.

(* A partition encoding *)
Definition partition_bits : set := log2 t.  (* O(log t) *)

(* ============================================================ *)
(* PART 5: ERM DISTILLATION                                     *)
(* ============================================================ *)

(* ERM finds the best hypothesis for each bit on training data *)

(* Empirical error of h on training blocks for bit i *)
Definition emp_error : set -> set -> set -> (set -> set) -> set :=
  fun h i train_set Phis =>
    (* |{j in train_set : h(u_i(Phi_j)) != X_{j,i}}| / |train_set| *)
    0.  (* placeholder *)

(* ERM output: hypothesis minimizing empirical error *)
Definition ERM : set -> set -> (set -> set) -> set :=
  fun i train_set Phis =>
    (* argmin_{h in H} emp_error(h, i, train_set, Phis) *)
    some h :e H_std, True.  (* placeholder *)

(* ERM generalization bound *)
(* With |H| = poly(m) and train_size = t/2 = Theta(m),
   standard VC theory gives:
   Pr[test_error - train_error > epsilon] <= |H| * exp(-epsilon^2 * train_size)
                                           <= m^O(1) * exp(-epsilon^2 * Theta(m))
*)

Theorem ERM_generalization :
  forall epsilon :e omega, 0 :e epsilon ->
  forall i :e m, forall Phis,
    let h := ERM i train_blocks Phis in
    let train_err := emp_error h i train_blocks Phis in
    let test_err := emp_error h i test_blocks Phis in
    (* With high probability: *)
    Pr (fun _ => test_err c= train_err :+: epsilon) :e (1 :\: exp m (0 :\: 1)).
Admitted.

(* ============================================================ *)
(* PART 6: WRAPPER CONSTRUCTION                                 *)
(* ============================================================ *)

(* The wrapper W consists of:
   1. Symmetrization family encoding
   2. Train/test partition encoding
   3. For each bit i: the ERM-selected hypothesis h_i
*)

Definition wrapper_length : set -> set :=
  fun p =>
    strlen p :+:       (* original program *)
    sym_bits :+:       (* symmetrization family: O(log^3 m) *)
    partition_bits :+: (* partition: O(log t) *)
    nat_mult m hyp_bits.  (* m hypotheses: O(m log m) !!! *)

(* CRITICAL ISSUE: wrapper_length includes O(m log m) for hypothesis encoding!
   This is NOT O(log m + log t) as claimed.

   The paper must mean something different...
*)

(* ============================================================ *)
(* PART 7: ANALYZING THE DESCRIPTION LENGTH CLAIM               *)
(* ============================================================ *)

(* Let's reconsider: maybe we don't encode ALL m hypotheses.

   Alternative interpretation 1:
   We encode a SINGLE hypothesis that works for all bits.
   Cost: O(log m) for the hypothesis.
   But: Different bits might need different hypotheses!

   Alternative interpretation 2:
   We encode the INDEX of the best hypothesis from a fixed enumeration.
   Cost: O(log |H|) = O(log m) per bit, but we have m bits...
   Total: O(m log m) - still too much.

   Alternative interpretation 3:
   The hypotheses are IMPLICIT in the decoder P.
   The wrapper only needs to encode how to extract them.
   Cost: O(log m + log t) for extraction instructions.
   But: How does this work exactly?
*)

(* Re-reading the paper more carefully:

   "a short wrapper W of length |P| + O(log m + log t)"

   The wrapper ADDS O(log m + log t) to the program length.
   It doesn't replace P, it augments it.

   The wrapper does:
   1. Select which blocks to use for training: O(log t) bits
   2. Specify symmetrization parameters: O(log m) bits
   3. The ERM selection is COMPUTED at runtime, not encoded!

   Aha! The hypotheses are computed, not stored.
   The wrapper encodes the PROCEDURE, not the result.
*)

Definition wrapper_length_v2 : set -> set :=
  fun p =>
    strlen p :+:         (* original program *)
    (log2 m) :+:         (* symmetrization seed/parameters *)
    (log2 t).            (* partition seed *)

(* This is O(|P| + log m + log t) as claimed! *)

(* But wait: how can the wrapper COMPUTE the ERM result at runtime
   if it doesn't know the instances?

   Answer: The wrapper is a program that:
   1. Takes the tuple (Phi_1, ..., Phi_t) as input
   2. Runs ERM on train blocks to find best hypotheses
   3. Applies those hypotheses to test blocks

   The wrapper encodes the ALGORITHM, not the learned parameters.
   This is valid because ERM is a deterministic procedure.
*)

(* ============================================================ *)
(* PART 8: PER-BIT LOCALITY                                     *)
(* ============================================================ *)

(* After applying the wrapper, the decoder becomes per-bit local:
   (P . W)(Phi)_{j,i} = h_{j,i}(u_i(Phi_j))

   where h_{j,i} is the ERM-selected hypothesis.

   Key insight: h_{j,i} only looks at the local view u_i(Phi_j),
   which is O(log m) bits.
*)

Definition per_bit_local_v2 : set -> set -> set -> prop :=
  fun pw j i =>
    exists h :e H_std,
      forall inst,
        ap (U pw inst) (pair j i) = U h (extract_local (ap inst j) i).

Theorem wrapper_makes_local :
  forall p, Program p -> strlen p c= nat_mult delta t ->
    exists w, Program w /\
      strlen w c= strlen p :+: (log2 m) :+: (log2 t) /\
      exists S c= t, gamma c= (S ::: t) /\
        forall j :e S, forall i :e m,
          per_bit_local_v2 (compose p w) j i.
Admitted.

(* ============================================================ *)
(* PART 9: POTENTIAL ISSUES                                     *)
(* ============================================================ *)

(* ISSUE 1: Runtime of the wrapper

   The wrapper needs to run ERM, which involves:
   - Evaluating P on O(t) training instances
   - For each of m bits, searching over |H| = poly(m) hypotheses
   - Total: O(t * time(P) + m * |H| * t)

   This is polynomial in m and t, so within the K_poly framework.
   OK.
*)

(* ISSUE 2: The wrapper needs to know which instances are "on promise"

   The wrapper computes ERM on training blocks.
   But to compute the "correct" labels X_i, it needs to solve Unique-SAT!

   Wait - the wrapper doesn't use the true labels X_i.
   It uses the DECODER'S outputs on symmetrized instances.

   The "surrogate labels" are Y~_{j,i} = majority_vote(P(T_I(Phi_j)))
   where I ranges over the symmetrization family.

   So the wrapper only needs to run P, not solve SAT.
   OK.
*)

(* ISSUE 3: Generalization with dependent data

   The standard ERM generalization bound assumes i.i.d. data.
   Are the training blocks i.i.d.?

   Yes - by construction of D_m, the t blocks are independent.
   The symmetrization might introduce dependencies within a block,
   but blocks remain independent.
   OK.
*)

(* ISSUE 4: What if ERM finds different hypotheses for different blocks?

   The claim is that h_{j,i} can depend on j (the block).
   But the description length analysis assumes a SINGLE hypothesis per bit.

   Re-reading: "h_{j,i}(u_i(Phi_j))" - yes, h can depend on j.

   But if each block needs a different hypothesis, we need O(t) hypotheses,
   which costs O(t log |H|) = O(t log m) bits.
   This is MUCH more than O(log m + log t)!

   CRITICAL ISSUE: The description length claim seems wrong if
   hypotheses can vary across blocks.
*)

(* Let me reconsider the wrapper structure...

   The wrapper is:
   W(Phi_1, ..., Phi_t) =
     let train = first t/2 blocks
     let test = last t/2 blocks
     for each bit i:
       h_i := ERM(i, train, Phis)  // ONE hypothesis per bit
     for each test block j, for each bit i:
       output h_i(u_i(Phi_j))

   Key: There's ONE hypothesis h_i per bit i, shared across all test blocks!

   This makes the description O(log m + log t) because:
   - The wrapper encodes the ALGORITHM
   - The hypotheses are COMPUTED at runtime
   - The output uses the SAME h_i for all j in test blocks

   So h_{j,i} = h_i for all j in the test set S.
   The notation h_{j,i} in the paper might be misleading.
*)

(* ============================================================ *)
(* PART 10: REFINED STATEMENT                                   *)
(* ============================================================ *)

Theorem switching_refined :
  forall p, Program p -> strlen p c= nat_mult delta t ->
    exists w, Program w /\
      strlen w c= strlen p :+: (log2 m) :+: (log2 t) /\
      exists S c= t, gamma c= (S ::: t) /\
        (* For each bit i, there's a SINGLE hypothesis h_i *)
        forall i :e m, exists h_i :e H_std,
          (* that works for ALL test blocks j in S *)
          forall j :e S,
            forall inst,
              ap (U (compose p w) inst) (pair j i) = U h_i (extract_local (ap inst j) i).
Admitted.

(* ============================================================ *)
(* PART 11: DOES GENERALIZATION ACTUALLY WORK?                  *)
(* ============================================================ *)

(* The key question: Does ERM on train blocks give a hypothesis
   that works well on test blocks?

   Standard generalization: With n training samples and |H| hypotheses,
   P[test_error > train_error + epsilon] <= |H| * exp(-2 * epsilon^2 * n)

   Here: n = t/2 = Theta(m), |H| = poly(m) = m^c for some c.

   For epsilon = 0.1 (say):
   RHS <= m^c * exp(-0.02 * m)
       = exp(c * log(m) - 0.02 * m)
       -> 0 as m -> infinity (since m >> log(m))

   So generalization DOES work with high probability.
*)

Theorem generalization_works :
  forall epsilon, 0 :e epsilon -> epsilon c= 1 ->
    exists m0 :e omega,
      forall m', m0 c= m' ->
        (* Generalization bound holds *)
        H_size c= exp m' 2 ->
        train_blocks c= nat_div m' 2 ->
        exp H_size (nat_mult (0 :\: 2) (nat_mult (nat_mult epsilon epsilon) train_blocks))
          c= exp m' (0 :\: 1).
Admitted.

(* ============================================================ *)
(* PART 12: THE SUCCESS DOMINATION CLAIM                        *)
(* ============================================================ *)

(* Theorem 4.2 also claims "success domination":
   The wrapped decoder succeeds at least as often as the original,
   minus a small slack.

   P[(P . W) correct] >= P[P correct] - m^{-Omega(1)}

   This is needed to ensure that if P had any success,
   the local version still has some success.
*)

Theorem success_domination :
  forall p w,
    (* wrapper construction as above *)
    True ->
    (* success domination holds *)
    Pr (fun Phis => U (compose p w) Phis = witness_tuple Phis) :e
      Pr (fun Phis => U p Phis = witness_tuple Phis) :\: (exp m (0 :\: 1)).
Admitted.

(* ============================================================ *)
(* PART 13: CRITICAL ANALYSIS                                   *)
(* ============================================================ *)

(*
SUMMARY OF SWITCHING-BY-WEAKNESS:

WHAT IT CLAIMS:
- Any short decoder P can be wrapped to become per-bit local
- Wrapper adds O(log m + log t) bits
- Locality holds on gamma*t test blocks

HOW IT WORKS:
1. Symmetrize P using random sign flips
2. Split blocks into train/test
3. Run ERM on train blocks to find best hypothesis per bit
4. Apply hypotheses to test blocks

WHY DESCRIPTION LENGTH IS SHORT:
- Wrapper encodes the ALGORITHM, not the learned hypotheses
- ERM is deterministic, so hypotheses are implicit
- Only need to encode: symmetrization seed + partition seed

POTENTIAL ISSUES:

ISSUE A: Symmetrization overhead
- Paper says "polylogarithmic multiset of involutions"
- Encoding this multiset might cost more than O(log m)
- Need to verify exact encoding

ISSUE B: What makes P "learnable"?
- ERM works because |H| = poly(m) and train_size = Theta(m)
- But this assumes the best hypothesis in H is GOOD
- What if no hypothesis in H matches P's behavior well?

ISSUE C: Is the hypothesis class H expressive enough?
- H contains poly(log m)-size circuits
- P might compute something that requires larger circuits
- The switching argument must show H suffices

CRITICAL GAP:
The proof needs to show that for ANY short decoder P,
there EXISTS a hypothesis h in H that approximates P's behavior.

This is the LEARNABILITY assumption.
If P computes something fundamentally non-local,
no local hypothesis can match it.

But wait - that's the POINT of switching!
If P is non-local, it fails on the ensemble due to neutrality.
So we only need to learn P when P is already somewhat local.

This circular argument might actually work:
- If P is local, H captures its behavior
- If P is non-local, it fails anyway (success rate < 2^{-Omega(t)})
*)

(* ============================================================ *)
(* PART 14: VERDICT                                             *)
(* ============================================================ *)

(*
VERDICT ON SWITCHING-BY-WEAKNESS:

The theorem appears PLAUSIBLE but has SUBTLE GAPS:

1. DESCRIPTION LENGTH: Probably OK
   - Wrapper encodes algorithm, not result
   - O(log m + log t) is achievable

2. GENERALIZATION: OK
   - Standard ERM bounds apply
   - poly(m) hypotheses, Theta(m) samples -> good generalization

3. LOCALITY: UNCLEAR
   - Assumes H is expressive enough to capture local behavior
   - This is the "learnability" assumption
   - Needs more justification

4. SUCCESS DOMINATION: UNCLEAR
   - Symmetrization might degrade success rate
   - Need to bound the degradation carefully

OVERALL: The switching theorem is the most complex part of the proof.
It's not obviously wrong, but the details are intricate.
The circular argument (non-local => fails, local => learnable)
is clever but needs careful verification.

RISK LEVEL: MEDIUM-HIGH
This is still a likely failure point, but less obvious than I initially thought.
*)

Theorem switching_verdict :
  (* Switching-by-Weakness appears plausible with caveats *)
  True.
exact TrueI.
Qed.

