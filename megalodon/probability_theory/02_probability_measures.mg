(* Probability Theory: Probability Measures
   Based on Billingsley "Probability and Measure" Chapter 1, Section 2
*)

(* ===== Reals Axiomatization (Simplified) ===== *)
(* We need R, 0, 1, +, <= to define probability measures.
   We declare them as parameters to avoid dependency on a specific construction. *)

Parameter R : set.
Parameter R_zero : set.
Parameter R_one : set.
Parameter R_plus : set -> set -> set.
Parameter R_mult : set -> set -> set.
Parameter R_leq : set -> set -> prop.
Parameter R_minus : set -> set -> set.

Infix + 360 right := R_plus.
Infix * 355 right := R_mult.
Infix <= 490 := R_leq.
Infix - 358 := R_minus.

(* Basic Real Axioms needed for Probability *)
Axiom R_zero_In : R_zero :e R.
Axiom R_one_In : R_one :e R.
Axiom R_plus_clos : forall x y :e R, x + y :e R.
Axiom R_mult_clos : forall x y :e R, x * y :e R.
Axiom R_minus_clos : forall x y :e R, x - y :e R.

Axiom R_leq_refl : forall x :e R, x <= x.
Axiom R_leq_trans : forall x y z :e R, x <= y -> y <= z -> x <= z.
Axiom R_leq_antisym : forall x y :e R, x <= y -> y <= x -> x = y.
Axiom R_zero_leq_one : R_zero <= R_one.
Axiom R_zero_leq_x_implies_plus_leq : forall x y :e R, R_zero <= y -> x <= x + y.

Axiom R_plus_comm : forall x y :e R, x + y = y + x.
Axiom R_plus_assoc : forall x y z :e R, x + (y + z) = (x + y) + z.
Axiom R_plus_zero : forall x :e R, x + R_zero = x.

Axiom R_minus_self : forall x :e R, x - x = R_zero.
Axiom R_plus_minus : forall x y :e R, (x + y) - y = x.
Axiom R_minus_plus_distr : forall x y z :e R, x - (y + z) = (x - y) - z.
(* x = 1 - y <-> x + y = 1 *)
Axiom R_minus_eq_iff : forall x y :e R, x = R_one - y <-> x + y = R_one.

Axiom R_leq_plus_r : forall x y z :e R, x <= y -> x + z <= y + z.
(* If x + z <= y + z then x <= y *)
Axiom R_leq_plus_cancel : forall x y z :e R, x + z <= y + z -> x <= y.

(* Countable Sum *)
Parameter sum_nat : (set -> set) -> set.

Axiom sum_nat_clos : forall f : set -> set, (forall n :e omega, f n :e R /\ R_zero <= f n) -> sum_nat f :e R.

(* Sum of zeros is zero *)
Axiom sum_nat_zero : sum_nat (fun n => R_zero) = R_zero.

(* Finite sum property: sum (a, b, 0, 0...) = a + b *)
Axiom sum_nat_pair : forall a b :e R,
  sum_nat (fun n => if n = 0 then a else if n = 1 then b else R_zero) = a + b.

(* ===== Probability Measure Definition ===== *)

Definition is_probability_measure : set -> set -> (set -> set) -> prop :=
  fun Omega F P =>
    is_sigma_field Omega F
    /\ (forall A :e F, P A :e R /\ R_zero <= P A)
    /\ P Omega = R_one
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e F) ->
         pairwise_disjoint f ->
         P (bigcup_nat f) = sum_nat (fun n => P (f n))).

(* ===== Theorems ===== *)

Theorem prob_measure_is_sigma_field :
  forall Omega F P,
    is_probability_measure Omega F P ->
    is_sigma_field Omega F.
let Omega. let F. let P.
assume H.
exact andEL (is_sigma_field Omega F)
            ((forall A :e F, P A :e R /\ R_zero <= P A) /\ P Omega = R_one /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))
            H.
Qed.

(* Lemma: P(Empty) = 0 *)
Theorem prob_empty_zero :
  forall Omega F P,
    is_probability_measure Omega F P ->
    P Empty = R_zero.
let Omega. let F. let P.
assume H.
(* Use countable additivity on Empty, Empty, ... *)
(* Disjointness: Empty /\ Empty = Empty. *)
(* Union Empty = Empty. *)
(* sum (P Empty, ...) = P Empty + P Empty + ... *)
(* This implies P Empty = 0 in Reals. *)
admit.
Qed.

(* Finite additivity for 2 sets *)
Theorem prob_finite_additivity :
  forall Omega F P A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    Disjoint A B ->
    P (A :\/: B) = P A + P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hd.
(* Construct sequence f: A, B, Empty, Empty... *)
(* Union is A U B *)
(* Sum is P A + P B *)
admit.
Qed.

Theorem prob_monotone :
  forall Omega F P A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    A c= B ->
    P A <= P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hab.
(* B = A U (B \ A) *)
(* A and B \ A are disjoint *)
(* P B = P A + P (B \ A) *)
(* P (B \ A) >= 0 *)
(* So P A <= P B *)
admit.
Qed.

Theorem prob_complement :
  forall Omega F P A,
    is_probability_measure Omega F P ->
    A :e F ->
    P (Omega :\: A) = R_one - P A.
let Omega. let F. let P. let A.
assume H. assume HA.
(* Omega = A U (Omega \ A) *)
(* Disjoint *)
(* P Omega = P A + P (Omega \ A) *)
(* 1 = P A + P (Omega \ A) *)
(* P (Omega \ A) = 1 - P A *)
admit.
Qed.

Theorem prob_union_bound :
  forall Omega F P A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    P (A :\/: B) <= P A + P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB.
(* P (A U B) = P A + P (B \ A) *)
(* B \ A c= B => P (B \ A) <= P B *)
(* P A + P (B \ A) <= P A + P B *)
admit.
Qed.
