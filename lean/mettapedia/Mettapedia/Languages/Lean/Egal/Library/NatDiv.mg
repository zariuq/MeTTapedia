(** Division of numerals.

   Lean's Nat.div runs its helper Nat.div.go on a fuel argument above the
   dividend.  On numerals the helper's value is the quotient: for a divisor
   y1 + 1 and a remainder r below it, Nat.div.go at the dividend
   q (y1 + 1) + r is q, for any fuel above the dividend.  The fuel is written
   as the dividend plus e plus one, so each step is an equation between
   ordinals. **)

Theorem Lean_Nat_div_go_num : forall y1, nat_p y1 -> forall r, nat_p r -> r :e ordsucc y1 ->
  forall q, nat_p q -> forall e, nat_p e ->
  Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) e)))
    (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0 = LeanNum q.
let y1. assume Hy1: nat_p y1. let r. assume Hr: nat_p r. assume Hry: r :e ordsucc y1.
claim HY: nat_p (ordsucc y1).
{ exact nat_ordsucc y1 Hy1. }
claim HYin: LeanNum (ordsucc y1) :e Lean_Nat.
{ exact LeanNum_In (ordsucc y1) HY. }
claim H1Y: 0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (LeanNum (ordsucc y1)).
{ rewrite <- LeanNum_S 0 nat_0.
  claim E1: add_nat 1 y1 = ordsucc y1.
  { rewrite add_nat_SL 0 nat_0 y1 Hy1. rewrite add_nat_0L y1 Hy1. reflexivity. }
  rewrite <- E1.
  exact Lean_Nat_le_add_num 1 nat_1 y1 Hy1. }
claim HF: forall X, nat_p X -> forall e, nat_p e ->
  0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum X)) (Lean_Nat_succ_node (LeanNum (add_nat X e))).
{ let X. assume HX: nat_p X. let e. assume He: nat_p e.
  rewrite <- LeanNum_S X HX.
  rewrite <- LeanNum_S (add_nat X e) (add_nat_p X HX e He).
  rewrite <- add_nat_SL X HX e He.
  exact Lean_Nat_le_add_num (ordsucc X) (nat_ordsucc X HX) e He. }
apply nat_ind.
- let e. assume He: nat_p e.
  prove Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat 0 (ordsucc y1)) r) e)))
    (LeanNum (add_nat (mul_nat 0 (ordsucc y1)) r)) 0 = LeanNum 0.
  rewrite mul_nat_0L (ordsucc y1) HY.
  rewrite add_nat_0L r Hr.
  rewrite LeanNum_S (add_nat r e) (add_nat_p r Hr e He).
  rewrite Lean_Nat_div_go_eq_1 (LeanNum (ordsucc y1)) HYin H1Y (LeanNum r) (LeanNum_In r Hr)
    (LeanNum (add_nat r e)) (LeanNum_In (add_nat r e) (add_nat_p r Hr e He)) (HF r Hr e He).
  rewrite Lean_Nat_decLe_num_false (ordsucc y1) HY r Hr Hry.
  rewrite Lean_dite_false_ap Lean_Nat (Lean_Nat_le_Prop (LeanNum (ordsucc y1)) (LeanNum r))
    (Lean_Nat_le_Prop_prop (LeanNum (ordsucc y1)) (LeanNum r)) (Lean_Nat_le_num_not (ordsucc y1) HY r Hr Hry).
  reflexivity.
- let q. assume Hq: nat_p q.
  assume IH: forall e, nat_p e ->
    Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) e)))
      (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0 = LeanNum q.
  let e. assume He: nat_p e.
  claim HqY: nat_p (mul_nat q (ordsucc y1)).
  { exact mul_nat_p q Hq (ordsucc y1) HY. }
  claim HA: nat_p (add_nat (mul_nat q (ordsucc y1)) r).
  { exact add_nat_p (mul_nat q (ordsucc y1)) HqY r Hr. }
  claim HX: nat_p (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)).
  { exact add_nat_p (add_nat (mul_nat q (ordsucc y1)) r) HA (ordsucc y1) HY. }
  claim EX: add_nat (mul_nat (ordsucc q) (ordsucc y1)) r = add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1).
  { rewrite mul_nat_SL q Hq (ordsucc y1) HY.
    rewrite add_nat_asso (mul_nat q (ordsucc y1)) HqY (ordsucc y1) HY r Hr.
    rewrite add_nat_asso (mul_nat q (ordsucc y1)) HqY r Hr (ordsucc y1) HY.
    rewrite add_nat_com (ordsucc y1) HY r Hr.
    reflexivity. }
  claim EF: add_nat (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) e
    = ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (add_nat y1 e)).
  { rewrite add_nat_SR (add_nat (mul_nat q (ordsucc y1)) r) y1 Hy1.
    rewrite add_nat_SL (add_nat (add_nat (mul_nat q (ordsucc y1)) r) y1) (add_nat_p (add_nat (mul_nat q (ordsucc y1)) r) HA y1 Hy1) e He.
    rewrite add_nat_asso (add_nat (mul_nat q (ordsucc y1)) r) HA y1 Hy1 e He.
    reflexivity. }
  prove Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat (ordsucc q) (ordsucc y1)) r) e)))
    (LeanNum (add_nat (mul_nat (ordsucc q) (ordsucc y1)) r)) 0 = LeanNum (ordsucc q).
  rewrite EX.
  rewrite LeanNum_S (add_nat (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) e)
    (add_nat_p (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) HX e He).
  rewrite Lean_Nat_div_go_eq_1 (LeanNum (ordsucc y1)) HYin H1Y
    (LeanNum (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1))) (LeanNum_In (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) HX)
    (LeanNum (add_nat (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) e))
    (LeanNum_In (add_nat (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) e) (add_nat_p (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) HX e He))
    (HF (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) HX e He).
  rewrite add_nat_com (add_nat (mul_nat q (ordsucc y1)) r) HA (ordsucc y1) HY.
  rewrite Lean_Nat_decLe_num_true (ordsucc y1) HY (add_nat (mul_nat q (ordsucc y1)) r) HA.
  rewrite Lean_dite_true_ap Lean_Nat (Lean_Nat_le_Prop (LeanNum (ordsucc y1)) (LeanNum (add_nat (ordsucc y1) (add_nat (mul_nat q (ordsucc y1)) r))))
    (Lean_Nat_le_add_num (ordsucc y1) HY (add_nat (mul_nat q (ordsucc y1)) r) HA).
  prove Lean_Nat_add (Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (add_nat (add_nat (ordsucc y1) (add_nat (mul_nat q (ordsucc y1)) r)) e))
      (Lean_Nat_sub (LeanNum (add_nat (ordsucc y1) (add_nat (mul_nat q (ordsucc y1)) r))) (LeanNum (ordsucc y1))) 0) (LeanNum 1)
    = LeanNum (ordsucc q).
  rewrite add_nat_com (ordsucc y1) HY (add_nat (mul_nat q (ordsucc y1)) r) HA.
  rewrite LeanNum_sub_add (ordsucc y1) HY (add_nat (mul_nat q (ordsucc y1)) r) HA.
  rewrite EF.
  rewrite IH (add_nat y1 e) (add_nat_p y1 Hy1 e He).
  rewrite LeanNum_add q Hq 1 nat_1.
  rewrite add_nat_SR q 0 nat_0.
  rewrite add_nat_0R q.
  reflexivity.
Qed.

(** Nat.div itself: the helper at fuel one above the dividend. **)
Theorem Lean_Nat_div_num : forall y1, nat_p y1 -> forall r, nat_p r -> r :e ordsucc y1 -> forall q, nat_p q ->
  Lean_Nat_div (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) (LeanNum (ordsucc y1)) = LeanNum q.
let y1. assume Hy1: nat_p y1. let r. assume Hr: nat_p r. assume Hry: r :e ordsucc y1. let q. assume Hq: nat_p q.
claim HY: nat_p (ordsucc y1).
{ exact nat_ordsucc y1 Hy1. }
claim HX: nat_p (add_nat (mul_nat q (ordsucc y1)) r).
{ exact add_nat_p (mul_nat q (ordsucc y1)) (mul_nat_p q Hq (ordsucc y1) HY) r Hr. }
claim H1Y: 0 :e Lean_Nat_le_Prop (LeanNum 1) (LeanNum (ordsucc y1)).
{ claim E1: add_nat 1 y1 = ordsucc y1.
  { rewrite add_nat_SL 0 nat_0 y1 Hy1. rewrite add_nat_0L y1 Hy1. reflexivity. }
  rewrite <- E1.
  exact Lean_Nat_le_add_num 1 nat_1 y1 Hy1. }
claim T0: Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) 0)))
  (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0 = LeanNum q.
{ exact Lean_Nat_div_go_num y1 Hy1 r Hr Hry q Hq 0 nat_0. }
rewrite Lean_Nat_div_unfold (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) (LeanNum (ordsucc y1)).
rewrite Lean_Nat_decLt_unfold (LeanNum 0) (LeanNum (ordsucc y1)).
rewrite <- LeanNum_S 0 nat_0.
rewrite Lean_Nat_decLe_num_le 1 nat_1 (ordsucc y1) HY H1Y.
rewrite Lean_dite_true_ap Lean_Nat (Lean_Nat_le_Prop (LeanNum 1) (LeanNum (ordsucc y1))) H1Y.
prove Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (Lean_Nat_succ_node (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)))
  (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0 = LeanNum q.
rewrite <- LeanNum_S (add_nat (mul_nat q (ordsucc y1)) r) HX.
exact eq_i_tra (Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (mul_nat q (ordsucc y1)) r)))
    (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0)
  (Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) 0)))
    (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0)
  (LeanNum q)
  (f_eq_i (fun z => Lean_Nat_div_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc z)) (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0)
    (add_nat (mul_nat q (ordsucc y1)) r) (add_nat (add_nat (mul_nat q (ordsucc y1)) r) 0)
    (eq_sym_i (add_nat (add_nat (mul_nat q (ordsucc y1)) r) 0) (add_nat (mul_nat q (ordsucc y1)) r) (add_nat_0R (add_nat (mul_nat q (ordsucc y1)) r))))
  T0.
Qed.

(** Positive and negative examples: 23 / 7 = 3, and not 2. **)
Theorem Lean_Nat_div_num_ex : Lean_Nat_div (LeanNum (add_nat (mul_nat 3 7) 2)) (LeanNum 7) = LeanNum 3.
exact Lean_Nat_div_num 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))) 2 nat_2
  (ordsuccI1 6 2 (ordsuccI1 5 2 (ordsuccI1 4 2 (ordsuccI1 3 2 (ordsuccI2 2)))))
  3 (nat_ordsucc 2 nat_2).
Qed.

Theorem Lean_Nat_div_num_ex_not : Lean_Nat_div (LeanNum (add_nat (mul_nat 3 7) 2)) (LeanNum 7) <> LeanNum 2.
assume H: Lean_Nat_div (LeanNum (add_nat (mul_nat 3 7) 2)) (LeanNum 7) = LeanNum 2.
claim E: 3 = 2.
{ apply LeanNum_inj 3 (nat_ordsucc 2 nat_2) 2 nat_2.
  exact eq_i_tra (LeanNum 3) (Lean_Nat_div (LeanNum (add_nat (mul_nat 3 7) 2)) (LeanNum 7)) (LeanNum 2)
    (eq_sym_i (Lean_Nat_div (LeanNum (add_nat (mul_nat 3 7) 2)) (LeanNum 7)) (LeanNum 3) Lean_Nat_div_num_ex) H. }
exact In_irref 2 (In_eq_r 2 3 2 E (ordsuccI2 2)).
Qed.

(** The remainder: the helper of Nat.modCore, then Nat.modCore. **)
Theorem Lean_Nat_modCore_go_num : forall y1, nat_p y1 -> forall r, nat_p r -> r :e ordsucc y1 ->
  forall q, nat_p q -> forall e, nat_p e ->
  Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) e)))
    (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0 = LeanNum r.
let y1. assume Hy1: nat_p y1. let r. assume Hr: nat_p r. assume Hry: r :e ordsucc y1.
claim HY: nat_p (ordsucc y1).
{ exact nat_ordsucc y1 Hy1. }
claim HYin: LeanNum (ordsucc y1) :e Lean_Nat.
{ exact LeanNum_In (ordsucc y1) HY. }
claim H1Y: 0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (LeanNum (ordsucc y1)).
{ rewrite <- LeanNum_S 0 nat_0.
  claim E1: add_nat 1 y1 = ordsucc y1.
  { rewrite add_nat_SL 0 nat_0 y1 Hy1. rewrite add_nat_0L y1 Hy1. reflexivity. }
  rewrite <- E1.
  exact Lean_Nat_le_add_num 1 nat_1 y1 Hy1. }
claim HF: forall X, nat_p X -> forall e, nat_p e ->
  0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum X)) (Lean_Nat_succ_node (LeanNum (add_nat X e))).
{ let X. assume HX: nat_p X. let e. assume He: nat_p e.
  rewrite <- LeanNum_S X HX.
  rewrite <- LeanNum_S (add_nat X e) (add_nat_p X HX e He).
  rewrite <- add_nat_SL X HX e He.
  exact Lean_Nat_le_add_num (ordsucc X) (nat_ordsucc X HX) e He. }
apply nat_ind.
- let e. assume He: nat_p e.
  prove Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat 0 (ordsucc y1)) r) e)))
    (LeanNum (add_nat (mul_nat 0 (ordsucc y1)) r)) 0 = LeanNum r.
  rewrite mul_nat_0L (ordsucc y1) HY.
  rewrite add_nat_0L r Hr.
  rewrite LeanNum_S (add_nat r e) (add_nat_p r Hr e He).
  rewrite Lean_Nat_modCore_go_eq_1 (LeanNum (ordsucc y1)) HYin H1Y (LeanNum r) (LeanNum_In r Hr)
    (LeanNum (add_nat r e)) (LeanNum_In (add_nat r e) (add_nat_p r Hr e He)) (HF r Hr e He).
  rewrite Lean_Nat_decLe_num_false (ordsucc y1) HY r Hr Hry.
  rewrite Lean_dite_false_ap Lean_Nat (Lean_Nat_le_Prop (LeanNum (ordsucc y1)) (LeanNum r))
    (Lean_Nat_le_Prop_prop (LeanNum (ordsucc y1)) (LeanNum r)) (Lean_Nat_le_num_not (ordsucc y1) HY r Hr Hry).
  reflexivity.
- let q. assume Hq: nat_p q.
  assume IH: forall e, nat_p e ->
    Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) e)))
      (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0 = LeanNum r.
  let e. assume He: nat_p e.
  claim HqY: nat_p (mul_nat q (ordsucc y1)).
  { exact mul_nat_p q Hq (ordsucc y1) HY. }
  claim HA: nat_p (add_nat (mul_nat q (ordsucc y1)) r).
  { exact add_nat_p (mul_nat q (ordsucc y1)) HqY r Hr. }
  claim HX: nat_p (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)).
  { exact add_nat_p (add_nat (mul_nat q (ordsucc y1)) r) HA (ordsucc y1) HY. }
  claim EX: add_nat (mul_nat (ordsucc q) (ordsucc y1)) r = add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1).
  { rewrite mul_nat_SL q Hq (ordsucc y1) HY.
    rewrite add_nat_asso (mul_nat q (ordsucc y1)) HqY (ordsucc y1) HY r Hr.
    rewrite add_nat_asso (mul_nat q (ordsucc y1)) HqY r Hr (ordsucc y1) HY.
    rewrite add_nat_com (ordsucc y1) HY r Hr.
    reflexivity. }
  claim EF: add_nat (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) e
    = ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (add_nat y1 e)).
  { rewrite add_nat_SR (add_nat (mul_nat q (ordsucc y1)) r) y1 Hy1.
    rewrite add_nat_SL (add_nat (add_nat (mul_nat q (ordsucc y1)) r) y1) (add_nat_p (add_nat (mul_nat q (ordsucc y1)) r) HA y1 Hy1) e He.
    rewrite add_nat_asso (add_nat (mul_nat q (ordsucc y1)) r) HA y1 Hy1 e He.
    reflexivity. }
  prove Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat (ordsucc q) (ordsucc y1)) r) e)))
    (LeanNum (add_nat (mul_nat (ordsucc q) (ordsucc y1)) r)) 0 = LeanNum r.
  rewrite EX.
  rewrite LeanNum_S (add_nat (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) e)
    (add_nat_p (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) HX e He).
  rewrite Lean_Nat_modCore_go_eq_1 (LeanNum (ordsucc y1)) HYin H1Y
    (LeanNum (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1))) (LeanNum_In (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) HX)
    (LeanNum (add_nat (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) e))
    (LeanNum_In (add_nat (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) e) (add_nat_p (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) HX e He))
    (HF (add_nat (add_nat (mul_nat q (ordsucc y1)) r) (ordsucc y1)) HX e He).
  rewrite add_nat_com (add_nat (mul_nat q (ordsucc y1)) r) HA (ordsucc y1) HY.
  rewrite Lean_Nat_decLe_num_true (ordsucc y1) HY (add_nat (mul_nat q (ordsucc y1)) r) HA.
  rewrite Lean_dite_true_ap Lean_Nat (Lean_Nat_le_Prop (LeanNum (ordsucc y1)) (LeanNum (add_nat (ordsucc y1) (add_nat (mul_nat q (ordsucc y1)) r))))
    (Lean_Nat_le_add_num (ordsucc y1) HY (add_nat (mul_nat q (ordsucc y1)) r) HA).
  prove Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (add_nat (add_nat (ordsucc y1) (add_nat (mul_nat q (ordsucc y1)) r)) e))
      (Lean_Nat_sub (LeanNum (add_nat (ordsucc y1) (add_nat (mul_nat q (ordsucc y1)) r))) (LeanNum (ordsucc y1))) 0
    = LeanNum r.
  rewrite add_nat_com (ordsucc y1) HY (add_nat (mul_nat q (ordsucc y1)) r) HA.
  rewrite LeanNum_sub_add (ordsucc y1) HY (add_nat (mul_nat q (ordsucc y1)) r) HA.
  rewrite EF.
  exact IH (add_nat y1 e) (add_nat_p y1 Hy1 e He).
Qed.

Theorem Lean_Nat_modCore_num : forall y1, nat_p y1 -> forall r, nat_p r -> r :e ordsucc y1 -> forall q, nat_p q ->
  Lean_Nat_modCore (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) (LeanNum (ordsucc y1)) = LeanNum r.
let y1. assume Hy1: nat_p y1. let r. assume Hr: nat_p r. assume Hry: r :e ordsucc y1. let q. assume Hq: nat_p q.
claim HY: nat_p (ordsucc y1).
{ exact nat_ordsucc y1 Hy1. }
claim HX: nat_p (add_nat (mul_nat q (ordsucc y1)) r).
{ exact add_nat_p (mul_nat q (ordsucc y1)) (mul_nat_p q Hq (ordsucc y1) HY) r Hr. }
claim H1Y: 0 :e Lean_Nat_le_Prop (LeanNum 1) (LeanNum (ordsucc y1)).
{ claim E1: add_nat 1 y1 = ordsucc y1.
  { rewrite add_nat_SL 0 nat_0 y1 Hy1. rewrite add_nat_0L y1 Hy1. reflexivity. }
  rewrite <- E1.
  exact Lean_Nat_le_add_num 1 nat_1 y1 Hy1. }
claim T0: Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) 0)))
  (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0 = LeanNum r.
{ exact Lean_Nat_modCore_go_num y1 Hy1 r Hr Hry q Hq 0 nat_0. }
rewrite Lean_Nat_modCore_unfold (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) (LeanNum (ordsucc y1)).
rewrite Lean_Nat_decLt_unfold (LeanNum 0) (LeanNum (ordsucc y1)).
rewrite <- LeanNum_S 0 nat_0.
rewrite Lean_Nat_decLe_num_le 1 nat_1 (ordsucc y1) HY H1Y.
rewrite Lean_dite_true_ap Lean_Nat (Lean_Nat_le_Prop (LeanNum 1) (LeanNum (ordsucc y1))) H1Y.
prove Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (Lean_Nat_succ_node (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)))
  (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0 = LeanNum r.
rewrite <- LeanNum_S (add_nat (mul_nat q (ordsucc y1)) r) HX.
exact eq_i_tra (Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (mul_nat q (ordsucc y1)) r)))
    (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0)
  (Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc (add_nat (add_nat (mul_nat q (ordsucc y1)) r) 0)))
    (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0)
  (LeanNum r)
  (f_eq_i (fun z => Lean_Nat_modCore_go (LeanNum (ordsucc y1)) 0 (LeanNum (ordsucc z)) (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) 0)
    (add_nat (mul_nat q (ordsucc y1)) r) (add_nat (add_nat (mul_nat q (ordsucc y1)) r) 0)
    (eq_sym_i (add_nat (add_nat (mul_nat q (ordsucc y1)) r) 0) (add_nat (mul_nat q (ordsucc y1)) r) (add_nat_0R (add_nat (mul_nat q (ordsucc y1)) r))))
  T0.
Qed.

(** Nat.mod itself: zero, or below the divisor, is its own remainder;
    otherwise Nat.modCore. **)
Theorem Lean_Nat_mod_num : forall y1, nat_p y1 -> forall r, nat_p r -> r :e ordsucc y1 -> forall q, nat_p q ->
  Lean_Nat_mod (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) (LeanNum (ordsucc y1)) = LeanNum r.
let y1. assume Hy1: nat_p y1. let r. assume Hr: nat_p r. assume Hry: r :e ordsucc y1. let q. assume Hq: nat_p q.
claim HY: nat_p (ordsucc y1).
{ exact nat_ordsucc y1 Hy1. }
claim HYin: LeanNum (ordsucc y1) :e Lean_Nat.
{ exact LeanNum_In (ordsucc y1) HY. }
apply nat_inv q Hq.
- assume Hq0: q = 0.
  rewrite Hq0.
  rewrite mul_nat_0L (ordsucc y1) HY.
  rewrite add_nat_0L r Hr.
  apply nat_inv r Hr.
  + assume Hr0: r = 0.
    rewrite Hr0.
    exact Lean_Nat_mod_eq_1 (LeanNum (ordsucc y1)) HYin.
  + assume Hr1: exists r1, nat_p r1 /\ r = ordsucc r1.
    apply Hr1.
    let r1. assume H: nat_p r1 /\ r = ordsucc r1.
    apply H.
    assume Hr1n: nat_p r1. assume Er: r = ordsucc r1.
    claim Hry1: ordsucc r1 :e ordsucc y1.
    { rewrite <- Er. exact Hry. }
    rewrite Er.
    rewrite LeanNum_S r1 Hr1n.
    rewrite Lean_Nat_mod_eq_2 (LeanNum (ordsucc y1)) HYin (LeanNum r1) (LeanNum_In r1 Hr1n).
    rewrite <- LeanNum_S r1 Hr1n.
    rewrite Lean_Nat_decLe_num_false (ordsucc y1) HY (ordsucc r1) (nat_ordsucc r1 Hr1n) Hry1.
    exact Lean_ite_false_ap Lean_Nat (Lean_Nat_le_Prop (LeanNum (ordsucc y1)) (LeanNum (ordsucc r1)))
      (Lean_Nat_le_Prop_prop (LeanNum (ordsucc y1)) (LeanNum (ordsucc r1)))
      (Lean_Nat_le_num_not (ordsucc y1) HY (ordsucc r1) (nat_ordsucc r1 Hr1n) Hry1)
      (Lean_Nat_modCore (LeanNum (ordsucc r1)) (LeanNum (ordsucc y1))) (LeanNum (ordsucc r1)).
- assume Hq1: exists q1, nat_p q1 /\ q = ordsucc q1.
  apply Hq1.
  let q1. assume H: nat_p q1 /\ q = ordsucc q1.
  apply H.
  assume Hq1n: nat_p q1. assume Eq: q = ordsucc q1.
  claim Hq1Y: nat_p (mul_nat q1 (ordsucc y1)).
  { exact mul_nat_p q1 Hq1n (ordsucc y1) HY. }
  claim HK: nat_p (add_nat (mul_nat q1 (ordsucc y1)) r).
  { exact add_nat_p (mul_nat q1 (ordsucc y1)) Hq1Y r Hr. }
  claim HN: nat_p (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r).
  { exact add_nat_p (add_nat (mul_nat q1 (ordsucc y1)) y1) (add_nat_p (mul_nat q1 (ordsucc y1)) Hq1Y y1 Hy1) r Hr. }
  claim EN: add_nat (mul_nat (ordsucc q1) (ordsucc y1)) r = ordsucc (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r).
  { rewrite mul_nat_SL q1 Hq1n (ordsucc y1) HY.
    rewrite add_nat_SR (mul_nat q1 (ordsucc y1)) y1 Hy1.
    exact add_nat_SL (add_nat (mul_nat q1 (ordsucc y1)) y1) (add_nat_p (mul_nat q1 (ordsucc y1)) Hq1Y y1 Hy1) r Hr. }
  claim EK: add_nat (ordsucc y1) (add_nat (mul_nat q1 (ordsucc y1)) r) = add_nat (mul_nat (ordsucc q1) (ordsucc y1)) r.
  { rewrite mul_nat_SL q1 Hq1n (ordsucc y1) HY.
    rewrite add_nat_com (ordsucc y1) HY (add_nat (mul_nat q1 (ordsucc y1)) r) HK.
    rewrite add_nat_asso (mul_nat q1 (ordsucc y1)) Hq1Y r Hr (ordsucc y1) HY.
    rewrite add_nat_asso (mul_nat q1 (ordsucc y1)) Hq1Y (ordsucc y1) HY r Hr.
    rewrite add_nat_com (ordsucc y1) HY r Hr.
    reflexivity. }
  claim HLe: 0 :e Lean_Nat_le_Prop (LeanNum (ordsucc y1)) (LeanNum (ordsucc (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r))).
  { rewrite <- EN. rewrite <- EK.
    exact Lean_Nat_le_add_num (ordsucc y1) HY (add_nat (mul_nat q1 (ordsucc y1)) r) HK. }
  claim MC: Lean_Nat_modCore (LeanNum (ordsucc (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r))) (LeanNum (ordsucc y1)) = LeanNum r.
  { rewrite <- EN. exact Lean_Nat_modCore_num y1 Hy1 r Hr Hry (ordsucc q1) (nat_ordsucc q1 Hq1n). }
  rewrite Eq.
  rewrite EN.
  rewrite LeanNum_S (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r) HN.
  rewrite Lean_Nat_mod_eq_2 (LeanNum (ordsucc y1)) HYin (LeanNum (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r))
    (LeanNum_In (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r) HN).
  rewrite <- LeanNum_S (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r) HN.
  rewrite Lean_Nat_decLe_num_le (ordsucc y1) HY (ordsucc (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r)) (nat_ordsucc (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r) HN) HLe.
  rewrite Lean_ite_true_ap Lean_Nat (Lean_Nat_le_Prop (LeanNum (ordsucc y1)) (LeanNum (ordsucc (add_nat (add_nat (mul_nat q1 (ordsucc y1)) y1) r)))) HLe.
  exact MC.
Qed.

(** Every natural of the reading is a numeral, and Egal's own division with
    remainder gives the numerals the theorems above need: on any naturals,
    the read remainder by a positive divisor is a numeral below it. **)
Theorem Lean_Nat_num : forall x :e Lean_Nat, exists k, nat_p k /\ x = LeanNum k.
apply Lean_Nat_ind.
- witness 0. apply andI.
  + exact nat_0.
  + exact eq_sym_i (LeanNum 0) Lean_Nat_zero_node LeanNum_0.
- let x. assume Hx: x :e Lean_Nat. assume IH: exists k, nat_p k /\ x = LeanNum k.
  apply IH. let k. assume Hk: nat_p k /\ x = LeanNum k.
  apply Hk. assume Hkn: nat_p k. assume Ex: x = LeanNum k.
  witness (ordsucc k). apply andI.
  + exact nat_ordsucc k Hkn.
  + rewrite LeanNum_S k Hkn. rewrite Ex. reflexivity.
Qed.

Theorem nat_euclid : forall a, nat_p a -> forall b, nat_p b ->
  exists q, nat_p q /\ (exists r, nat_p r /\ (r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r)).
let a. assume Ha: nat_p a.
claim HY: nat_p (ordsucc a).
{ exact nat_ordsucc a Ha. }
apply nat_ind.
- witness 0. apply andI.
  + exact nat_0.
  + witness 0. apply andI.
    * exact nat_0.
    * apply andI.
      { exact nat_0_in_ordsucc a Ha. }
      { rewrite mul_nat_0L (ordsucc a) HY. rewrite add_nat_0R 0. reflexivity. }
- let b. assume Hb: nat_p b.
  assume IH: exists q, nat_p q /\ (exists r, nat_p r /\ (r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r)).
  apply IH. let q. assume Hq: nat_p q /\ (exists r, nat_p r /\ (r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r)).
  apply Hq. assume Hqn: nat_p q. assume Hr: exists r, nat_p r /\ (r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r).
  apply Hr. let r. assume Hr2: nat_p r /\ (r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r).
  apply Hr2. assume Hrn: nat_p r. assume Hr3: r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r.
  apply Hr3. assume Hra: r :e ordsucc a. assume Eb: b = add_nat (mul_nat q (ordsucc a)) r.
  apply ordinal_ordsucc_In_eq (ordsucc a) r (nat_p_ordinal (ordsucc a) HY) Hra.
  + assume Hs: ordsucc r :e ordsucc a.
    witness q. apply andI.
    * exact Hqn.
    * witness (ordsucc r). apply andI.
      { exact nat_ordsucc r Hrn. }
      { apply andI.
        - exact Hs.
        - rewrite add_nat_SR (mul_nat q (ordsucc a)) r Hrn. rewrite Eb. reflexivity. }
  + assume EY: ordsucc a = ordsucc r.
    witness (ordsucc q). apply andI.
    * exact nat_ordsucc q Hqn.
    * witness 0. apply andI.
      { exact nat_0. }
      { apply andI.
        - exact nat_0_in_ordsucc a Ha.
        - rewrite add_nat_0R (mul_nat (ordsucc q) (ordsucc a)).
          rewrite mul_nat_SL q Hqn (ordsucc a) HY.
          rewrite Eb.
          rewrite EY.
          rewrite add_nat_SR (mul_nat q (ordsucc r)) r Hrn.
          reflexivity. }
Qed.

Theorem Lean_Nat_mod_lt : forall n :e Lean_Nat, forall a, nat_p a ->
  exists r, nat_p r /\ (r :e ordsucc a /\ Lean_Nat_mod n (LeanNum (ordsucc a)) = LeanNum r).
let n. assume Hn: n :e Lean_Nat. let a. assume Ha: nat_p a.
apply Lean_Nat_num n Hn. let b. assume Hb: nat_p b /\ n = LeanNum b.
apply Hb. assume Hbn: nat_p b. assume En: n = LeanNum b.
apply nat_euclid a Ha b Hbn. let q. assume Hq: nat_p q /\ (exists r, nat_p r /\ (r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r)).
apply Hq. assume Hqn: nat_p q. assume Hr: exists r, nat_p r /\ (r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r).
apply Hr. let r. assume Hr2: nat_p r /\ (r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r).
apply Hr2. assume Hrn: nat_p r. assume Hr3: r :e ordsucc a /\ b = add_nat (mul_nat q (ordsucc a)) r.
apply Hr3. assume Hra: r :e ordsucc a. assume Eb: b = add_nat (mul_nat q (ordsucc a)) r.
witness r. apply andI.
- exact Hrn.
- apply andI.
  + exact Hra.
  + rewrite En. rewrite Eb. exact Lean_Nat_mod_num a Ha r Hrn Hra q Hqn.
Qed.

(** The remainder's bound as an addition, which digits can certify:
    r + d = y1 puts r below y1 + 1. **)
Theorem In_ordsucc_add : forall r, nat_p r -> forall d, nat_p d -> r :e ordsucc (add_nat r d).
let r. assume Hr: nat_p r.
apply nat_ind.
- rewrite add_nat_0R r. exact ordsuccI2 r.
- let d. assume Hd: nat_p d. assume IH: r :e ordsucc (add_nat r d).
  rewrite add_nat_SR r d Hd.
  exact ordsuccI1 (ordsucc (add_nat r d)) r IH.
Qed.

Theorem Lean_Nat_div_num_add : forall y1, nat_p y1 -> forall r, nat_p r -> forall d, nat_p d -> add_nat r d = y1 ->
  forall q, nat_p q -> Lean_Nat_div (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) (LeanNum (ordsucc y1)) = LeanNum q.
let y1. assume Hy1: nat_p y1. let r. assume Hr: nat_p r. let d. assume Hd: nat_p d. assume E: add_nat r d = y1.
claim Hry: r :e ordsucc y1.
{ rewrite <- E. exact In_ordsucc_add r Hr d Hd. }
exact Lean_Nat_div_num y1 Hy1 r Hr Hry.
Qed.

Theorem Lean_Nat_mod_num_add : forall y1, nat_p y1 -> forall r, nat_p r -> forall d, nat_p d -> add_nat r d = y1 ->
  forall q, nat_p q -> Lean_Nat_mod (LeanNum (add_nat (mul_nat q (ordsucc y1)) r)) (LeanNum (ordsucc y1)) = LeanNum r.
let y1. assume Hy1: nat_p y1. let r. assume Hr: nat_p r. let d. assume Hd: nat_p d. assume E: add_nat r d = y1.
claim Hry: r :e ordsucc y1.
{ rewrite <- E. exact In_ordsucc_add r Hr d Hd. }
exact Lean_Nat_mod_num y1 Hy1 r Hr Hry.
Qed.
