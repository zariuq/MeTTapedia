(* P != NP Formalization: CRUX - Neutrality Lemma *)
(* Based on Goertzel arXiv:2510.08814, Corollary 3.8 *)

(* ============================================================ *)
(* CRUX LEMMA 1: SIGN-INVARIANT NEUTRALITY                      *)
(*                                                               *)
(* This is one of the most critical claims in the proof.        *)
(* If this fails, the entire lower bound argument collapses.    *)
(* ============================================================ *)

(* A predicate is sign-invariant if it's preserved by all T_i *)
Definition sign_invariant : (set -> prop) -> prop :=
  fun P => forall i :e m, forall inst,
    DmInstance inst -> P inst -> P (T_i i inst).

(* A sigma-algebra (event family) is sign-invariant if all events are *)
Definition sign_invariant_algebra : (set -> prop) -> prop :=
  fun I => sign_invariant I.

(* ============================================================ *)
(* THE NEUTRALITY CLAIM                                         *)
(* Corollary 3.8: For any sign-invariant view I,                *)
(*   Pr[X_i = 1 | I] = 1/2                                      *)
(*                                                               *)
(* INTUITION: If you can only see sign-invariant features,      *)
(* you have no information about any individual bit.            *)
(* ============================================================ *)

(* Probability abstraction *)
Variable Pr : (set -> prop) -> set.  (* probability measure *)

(* Conditional probability *)
Variable Pr_cond : (set -> prop) -> (set -> prop) -> set.

(* Bit value predicate *)
Definition bit_is_one : set -> (set -> prop) :=
  fun i => fun inst => ap (witness_X inst) i = 1.

(* ====== THE CRUX THEOREM ====== *)
Theorem neutrality_lemma :
  forall i :e m, forall I,
    sign_invariant_algebra I ->
    Pr_cond (bit_is_one i) I = half.
Admitted.

(* ============================================================ *)
(* WHY THIS MIGHT FAIL                                          *)
(* ============================================================ *)

(* POTENTIAL ISSUE 1: Does T_i really preserve the distribution?

   The claim relies on T_i being a measure-preserving involution.
   But:
   - The VV isolation might break this
   - The promise (unique satisfiability) conditioning might not be preserved
   - The distribution of masked formulas might not be symmetric
*)

(* Test case: Does T_i preserve the promise? *)
Theorem T_i_measure_preserving :
  forall i :e m,
    (* The distribution of T_i(inst) equals the distribution of inst *)
    (* This is required for the pairing argument *)
    forall P, (forall inst, DmInstance inst -> P inst \/ P (T_i i inst)).
Admitted.

(* POTENTIAL ISSUE 2: Is the pairing argument valid?

   The proof pairs each instance with its T_i image.
   But this requires:
   - T_i is an involution (T_i . T_i = id)
   - The pairing covers all instances exactly once
   - No instance is fixed by T_i
*)

Theorem T_i_involution :
  forall i :e m, forall inst,
    DmInstance inst ->
    T_i i (T_i i inst) = inst.
Admitted.

Theorem T_i_no_fixed_point :
  forall i :e m, forall inst,
    DmInstance inst ->
    T_i i inst <> inst.
Admitted.

(* POTENTIAL ISSUE 3: Sign-invariance of the decoder's view

   The proof assumes that any polytime decoder can only compute
   sign-invariant features of its local view. But:
   - What if the decoder exploits the VV structure?
   - What if template structure leaks sign information?
*)

(* A decoder's computed features *)
Definition decoder_features : set -> set -> set :=
  fun p inst => U p inst.

(* Claim: Polytime decoders compute sign-invariant features *)
(* THIS IS THE REAL CRUX - is this actually true? *)
Theorem polytime_sign_invariant :
  forall p, Program p -> strlen p c= m ->
    sign_invariant (fun inst => decoder_features p inst :e omega).
Admitted.

(* ============================================================ *)
(* CONSEQUENCE OF NEUTRALITY                                    *)
(* ============================================================ *)

(* If I is sign-invariant, conditioning on I gives no advantage *)
Theorem no_advantage_from_invariant :
  forall i :e m, forall I,
    sign_invariant_algebra I ->
    forall p, Program p ->
      Pr_cond (fun inst => U p inst = ap (witness_X inst) i) I = half.
Admitted.

(* This means success probability is at most 1/2 per bit *)
Theorem per_bit_half_success :
  forall p, Program p -> strlen p c= m ->
    forall i :e m,
      Pr (fun inst => U p inst = ap (witness_X inst) i) = half.
Admitted.

