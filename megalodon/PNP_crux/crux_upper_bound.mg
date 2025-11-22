(* P != NP Formalization: CRUX - Upper Bound under P=NP *)
(* Based on Goertzel arXiv:2510.08814, Proposition 7.2 *)

(* ============================================================ *)
(* CRUX LEMMA 4: P=NP IMPLIES O(1) WITNESS COMPLEXITY           *)
(*                                                               *)
(* This is the "easy" direction but still has subtle issues.    *)
(* ============================================================ *)

(* ============================================================ *)
(* THE UPPER BOUND CLAIM                                        *)
(* ============================================================ *)

(* If P=NP, there exists a uniform polytime SAT solver *)
Definition uniform_SAT_solver : set -> prop :=
  fun p => Program p /\
    (forall phi, SAT phi -> polytime_on p phi) /\
    (forall phi, SAT phi -> sat_formula (U p phi) phi).

(* P=NP implies existence of uniform solver *)
Theorem P_eq_NP_implies_solver :
  P_eq_NP -> exists p, uniform_SAT_solver p.
Admitted.

(* ============================================================ *)
(* SELF-REDUCTION FOR UNIQUE-SAT                                *)
(* ============================================================ *)

(* Key insight: Can use SAT oracle to find THE witness for Unique-SAT
   by binary search on variable assignments *)

Definition self_reduce_witness : set -> set -> set :=
  fun solver phi =>
    (* For i = 1 to n:
         If SAT(phi AND x_i = 0) then set x_i = 0
         Else set x_i = 1
       Return assignment *)
    U solver phi.  (* abstracted *)

Theorem self_reduction_correct :
  forall solver,
    uniform_SAT_solver solver ->
    forall phi, UniqueSAT phi ->
      self_reduce_witness solver phi = unique_witness phi.
Admitted.

(* ============================================================ *)
(* THE CONSTANT COMPLEXITY CLAIM                                *)
(* ============================================================ *)

(* ====== THE CRUX THEOREM ====== *)
Theorem P_eq_NP_implies_O1_complexity :
  P_eq_NP ->
  exists c :e omega,
    forall phi, UniqueSAT phi ->
      K_poly (unique_witness phi) phi c= c.
Admitted.

(* ============================================================ *)
(* WHY THIS MIGHT FAIL                                          *)
(* ============================================================ *)

(* POTENTIAL ISSUE 1: Is the solver really O(1) description length?

   The claim is that K_poly(X|Phi) <= O(1) because there's a
   uniform constant-length program mapping Phi to X.

   But:
   - The solver program itself has some length |solver|
   - Is |solver| truly O(1) independent of m?
   - The self-reduction adds O(log n) bits for the loop
*)

Theorem solver_is_O1 :
  P_eq_NP ->
  exists solver, uniform_SAT_solver solver /\
    strlen solver :e omega.  (* exists, but what's the constant? *)
Admitted.

(* The self-reduction overhead *)
Theorem self_reduction_overhead :
  forall solver phi,
    uniform_SAT_solver solver ->
    UniqueSAT phi ->
    (* description length of self-reduction program *)
    strlen (self_reduce_prog solver) c= strlen solver :+: log2 (cnf_vars phi).
Admitted.

(* WAIT: This is O(log n), not O(1)!!! *)
(* The self-reduction adds O(log n) bits for the binary search *)

(* CRITICAL QUESTION: Does K_poly(X|Phi) include the loop counter? *)

(* If so, we get O(log n), not O(1) *)
(* If not, how is the loop implemented without specifying its length? *)

Theorem self_reduction_is_actually_O_log_n :
  P_eq_NP ->
  exists c :e omega,
    forall phi, UniqueSAT phi ->
      K_poly (unique_witness phi) phi c= c :+: log2 (cnf_vars phi).
Admitted.

(* THIS IS A POTENTIAL BUG IN THE PROOF!
   If K_poly(X|Phi) = O(log n) under P=NP instead of O(1),
   and the lower bound is eta*t = Theta(m),
   we need t >> log(m) for the contradiction.

   Since t = Theta(m), this is satisfied.
   But the constants matter!
*)

(* POTENTIAL ISSUE 2: Uniformity

   The solver must work for ALL formulas of ALL sizes.
   A non-uniform solver (different program for each n) doesn't count.

   Question: Does P=NP give a SINGLE program, or a family?
*)

Theorem P_eq_NP_gives_single_program :
  P_eq_NP ->
  exists p, Program p /\
    forall n :e omega, forall phi,
      cnf_vars phi = n -> SAT phi -> polytime_on p phi /\ sat_formula (U p phi) phi.
Admitted.

(* POTENTIAL ISSUE 3: Polytime Bound in K_poly

   K_poly requires the decoder to run in time poly(|input|).
   For input Phi of size O(m), this is poly(m).
   The self-reduction runs SAT oracle m times.
   Each SAT call on a formula of size O(m) takes poly(m).
   Total: m * poly(m) = poly(m). OK.

   But: does the K_poly definition allow this?
*)

Theorem self_reduction_polytime :
  forall solver phi,
    uniform_SAT_solver solver ->
    UniqueSAT phi ->
    polytime_on (self_reduce_prog solver) phi.
Admitted.

(* ============================================================ *)
(* SUMMARY OF UPPER BOUND ANALYSIS                              *)
(* ============================================================ *)

(* The upper bound claim is:
   P=NP => K_poly((X_1,...,X_t) | (Phi_1,...,Phi_t)) <= O(1)

   By chain rule and uniformity:
   K_poly(X_1,...,X_t | Phi_1,...,Phi_t)
     <= K_poly(X_1 | Phi_1) + ... + K_poly(X_t | Phi_t) + O(log t)
     <= t * O(1) + O(log t)   [if each is O(1)]
     = O(t)

   WAIT: This is O(t), not O(1)!!!

   The paper claims the TUPLE complexity is O(1).
   But by additivity it should be O(t).

   CRITICAL: Re-read the paper. The contradiction is:
   - Lower bound: K_poly(...) >= eta*t
   - Upper bound: K_poly(...) <= O(1)  ???

   If upper bound is actually O(t), there's no contradiction!
*)

(* Need to check: Is the upper bound claim per-instance or tuple? *)
Theorem tuple_complexity_under_P_eq_NP :
  P_eq_NP ->
  (* The paper claims K_poly for the TUPLE is O(1) because
     a single program maps the entire tuple to its witnesses.
     The program doesn't depend on t.
     So |program| = O(1), not O(t). *)
  exists c :e omega,
    forall t :e omega, forall Phis Xs,
      Dm_tuple t Phis -> (forall j :e t, Xs j = unique_witness (Phis j)) ->
      K_poly (lam j :e t, Xs j) (lam j :e t, Phis j) c= c.
Admitted.

(* This is plausible: the program "for each j, solve Phis_j" has O(1) length
   because the loop structure is fixed and only the solver matters.
   The description length is |solver| + O(1) for the loop overhead.
*)

