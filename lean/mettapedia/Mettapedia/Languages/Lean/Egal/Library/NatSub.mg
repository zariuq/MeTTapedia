(** Subtraction of numerals.

   Lean's Nat.sub is the function read from its equation theorems: it
   subtracts by repeated predecessor.  On numerals it undoes Egal's own
   addition of ordinals: LeanNum (m + n) - LeanNum n = LeanNum m. **)

Theorem LeanNum_pred_S : forall m, nat_p m -> Lean_Nat_pred (LeanNum (ordsucc m)) = LeanNum m.
let m. assume Hm: nat_p m.
rewrite LeanNum_S m Hm.
exact Lean_Nat_pred_eq_2 (LeanNum m) (LeanNum_In m Hm).
Qed.

Theorem LeanNum_sub_add : forall n, nat_p n -> forall m, nat_p m ->
  Lean_Nat_sub (LeanNum (add_nat m n)) (LeanNum n) = LeanNum m.
apply nat_ind.
- let m. assume Hm: nat_p m.
  prove Lean_Nat_sub (LeanNum (add_nat m 0)) (LeanNum 0) = LeanNum m.
  rewrite add_nat_0R m.
  exact Lean_Nat_sub_eq_1 (LeanNum m) (LeanNum_In m Hm).
- let n. assume Hn: nat_p n.
  assume IH: forall m, nat_p m -> Lean_Nat_sub (LeanNum (add_nat m n)) (LeanNum n) = LeanNum m.
  let m. assume Hm: nat_p m.
  prove Lean_Nat_sub (LeanNum (add_nat m (ordsucc n))) (LeanNum (ordsucc n)) = LeanNum m.
  rewrite add_nat_SR m n Hn.
  rewrite LeanNum_S n Hn.
  rewrite Lean_Nat_sub_eq_2 (LeanNum (ordsucc (add_nat m n)))
    (LeanNum_In (ordsucc (add_nat m n)) (nat_ordsucc (add_nat m n) (add_nat_p m Hm n Hn))) (LeanNum n) (LeanNum_In n Hn).
  rewrite <- add_nat_SL m Hm n Hn.
  rewrite IH (ordsucc m) (nat_ordsucc m Hm).
  exact LeanNum_pred_S m Hm.
Qed.

(** The form used by computations: the difference m is given, with the
    ordinal sum that it undoes. **)
Theorem LeanNum_sub_eq : forall m, nat_p m -> forall n, nat_p n -> forall k,
  add_nat m n = k -> Lean_Nat_sub (LeanNum k) (LeanNum n) = LeanNum m.
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. let k. assume Hk: add_nat m n = k.
rewrite <- Hk.
exact LeanNum_sub_add n Hn m Hm.
Qed.

(** Positive and negative examples. **)
Theorem LeanNum_sub_ex : Lean_Nat_sub (LeanNum 5) (LeanNum 2) = LeanNum 3.
apply LeanNum_sub_eq 3 (nat_ordsucc 2 nat_2) 2 nat_2 5.
prove add_nat 3 2 = 5.
rewrite add_nat_SR 3 1 nat_1.
rewrite add_nat_SR 3 0 nat_0.
rewrite add_nat_0R 3.
reflexivity.
Qed.

Theorem LeanNum_sub_ex_not : Lean_Nat_sub (LeanNum 5) (LeanNum 2) <> LeanNum 2.
assume H: Lean_Nat_sub (LeanNum 5) (LeanNum 2) = LeanNum 2.
claim E: 3 = 2.
{ apply LeanNum_inj 3 (nat_ordsucc 2 nat_2) 2 nat_2.
  exact eq_i_tra (LeanNum 3) (Lean_Nat_sub (LeanNum 5) (LeanNum 2)) (LeanNum 2)
    (eq_sym_i (Lean_Nat_sub (LeanNum 5) (LeanNum 2)) (LeanNum 3) LeanNum_sub_ex) H. }
exact In_irref 2 (In_eq_r 2 3 2 E (ordsuccI2 2)).
Qed.
