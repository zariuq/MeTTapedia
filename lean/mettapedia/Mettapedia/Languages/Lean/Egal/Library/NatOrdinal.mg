(** The ordinal of a Lean natural number, and Lean's order on Nat between
    numerals as inclusion of ordinals.  A rank of a state that is, or is
    measured by, a Lean natural number is this ordinal. **)

Definition LeanNat_ord : set -> set := fun x => Eps_i (fun k => nat_p k /\ x = LeanNum k).

Theorem LeanNat_ord_num : forall k, nat_p k -> LeanNat_ord (LeanNum k) = k.
let k. assume Hk: nat_p k.
claim Lrefl: LeanNum k = LeanNum k.
{ reflexivity. }
claim L: nat_p (LeanNat_ord (LeanNum k)) /\ LeanNum k = LeanNum (LeanNat_ord (LeanNum k)).
{ exact Eps_i_ax (fun j => nat_p j /\ LeanNum k = LeanNum j) k (andI (nat_p k) (LeanNum k = LeanNum k) Hk Lrefl). }
apply L. assume L1: nat_p (LeanNat_ord (LeanNum k)). assume L2: LeanNum k = LeanNum (LeanNat_ord (LeanNum k)).
symmetry.
exact LeanNum_inj k Hk (LeanNat_ord (LeanNum k)) L1 L2.
Qed.

Theorem LeanNat_ord_nat : forall x :e Lean_Nat, nat_p (LeanNat_ord x).
let x. assume Hx: x :e Lean_Nat.
apply Lean_Nat_num x Hx. let k. assume Hk: nat_p k /\ x = LeanNum k.
apply Hk. assume Hk1: nat_p k. assume Hk2: x = LeanNum k.
rewrite Hk2. rewrite LeanNat_ord_num k Hk1. exact Hk1.
Qed.

Theorem Lean_Nat_le_num_Subq : forall m, nat_p m -> forall n, nat_p n ->
  0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum n) -> m c= n.
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n.
assume H: 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum n).
apply Lean_Nat_le_index m Hm (LeanNum n) H.
let k. assume Hk: nat_p k /\ m c= k /\ LeanNum n = LeanNum k.
apply and3E (nat_p k) (m c= k) (LeanNum n = LeanNum k) Hk.
assume Hk1: nat_p k. assume Hk2: m c= k. assume Hk3: LeanNum n = LeanNum k.
rewrite LeanNum_inj n Hn k Hk1 Hk3.
exact Hk2.
Qed.

Theorem Lean_Nat_le_num_of_Subq : forall m, nat_p m -> forall n, nat_p n -> m c= n ->
  0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum n).
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. assume H: m c= n.
apply NatFactor_Subq_add_ex m Hm n Hn H.
let j. assume Hj: nat_p j /\ n = add_nat m j.
apply Hj. assume Hj1: nat_p j. assume Hj2: n = add_nat m j.
rewrite Hj2.
exact Lean_Nat_le_add_num m Hm j Hj1.
Qed.

(** Where Lean's m <= n fails between numerals, n is below m. **)
Theorem Lean_Nat_le_num_In : forall m, nat_p m -> forall n, nat_p n ->
  0 /:e Lean_Nat_le_Prop (LeanNum m) (LeanNum n) -> n :e m.
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n.
assume H: 0 /:e Lean_Nat_le_Prop (LeanNum m) (LeanNum n).
apply ordinal_In_Or_Subq n m (nat_p_ordinal n Hn) (nat_p_ordinal m Hm).
- assume Hnm: n :e m. exact Hnm.
- assume Hmn: m c= n.
  exact FalseE (H (Lean_Nat_le_num_of_Subq m Hm n Hn Hmn)) (n :e m).
Qed.

(** An ordinal included in another is below its successor. **)
Theorem nat_Subq_In_ordsucc : forall m, nat_p m -> forall n, nat_p n -> m c= n -> m :e ordsucc n.
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. assume H: m c= n.
apply ordinal_In_Or_Subq m n (nat_p_ordinal m Hm) (nat_p_ordinal n Hn).
- assume Hmn: m :e n. exact ordsuccI1 n m Hmn.
- assume Hnm: n c= m.
  rewrite set_ext m n H Hnm.
  exact ordsuccI2 n.
Qed.

(** A Lean natural number is the numeral of its ordinal. **)
Theorem LeanNat_ord_eq : forall x :e Lean_Nat, x = LeanNum (LeanNat_ord x).
let x. assume Hx: x :e Lean_Nat.
apply Lean_Nat_num x Hx. let k. assume Hk: nat_p k /\ x = LeanNum k.
apply Hk. assume Hk1: nat_p k. assume Hk2: x = LeanNum k.
rewrite Hk2. rewrite LeanNat_ord_num k Hk1. reflexivity.
Qed.

(** A number is below its sum with a positive number. **)
Theorem nat_In_add_pos : forall p, nat_p p -> forall q, nat_p q -> 0 :e q -> p :e add_nat p q.
let p. assume Hp: nat_p p. let q. assume Hq: nat_p q. assume H0: 0 :e q.
claim Lgen: forall z, z = p -> z :e add_nat p q -> p :e add_nat p q.
{ let z. assume Ez: z = p. rewrite Ez.
  assume Hz: p :e add_nat p q. exact Hz. }
exact Lgen (add_nat p 0) (add_nat_0R p) (NatFactor_add_In p Hp q Hq 0 H0).
Qed.

(** Positive and negative examples. **)
Theorem LeanNat_ord_ex : LeanNat_ord (Lean_Nat_add (LeanNum 2) (LeanNum 1)) = 3.
claim L: add_nat 2 1 = 3.
{ prove add_nat 2 (ordsucc 0) = 3.
  rewrite add_nat_SR 2 0 nat_0. rewrite add_nat_0R 2. reflexivity. }
rewrite LeanNum_add_eq 2 nat_2 1 nat_1 3 L.
exact LeanNat_ord_num 3 nat_3.
Qed.

Theorem LeanNat_ord_ex_not : LeanNat_ord (LeanNum 3) <> 2.
rewrite LeanNat_ord_num 3 nat_3.
assume H: 3 = 2.
exact neq_2_1 (ordsucc_inj 2 1 H).
Qed.
