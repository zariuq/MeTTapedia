(** Divisibility reconstructed from the checked numeral division interface. **)

Theorem Lean_ite_same : forall T p value, forall decision :e Lean_Decidable p,
  Lean_ite T p decision value value = value.
let T p value.
claim Hfalse: forall h :e (Pi_ x :e p, Lean_False_Prop),
  Lean_ite T p (Lean_Decidable_isFalse_node p h) value value = value.
{ let h. assume Hh: h :e (Pi_ x :e p, Lean_False_Prop).
  rewrite Lean_ite_unfold T p (Lean_Decidable_isFalse_node p h) value value.
  rewrite Lean_Decidable_iota0 p (fun _ :e (Pi_ x :e p, Lean_False_Prop) => value)
    (fun _ :e p => value) h Hh.
  exact beta (Pi_ x :e p, Lean_False_Prop) (fun _ => value) h Hh. }
claim Htrue: forall h :e p, Lean_ite T p (Lean_Decidable_isTrue_node p h) value value = value.
{ let h. assume Hh: h :e p.
  rewrite Lean_ite_unfold T p (Lean_Decidable_isTrue_node p h) value value.
  rewrite Lean_Decidable_iota1 p (fun _ :e (Pi_ x :e p, Lean_False_Prop) => value)
    (fun _ :e p => value) h Hh.
  exact beta p (fun _ => value) h Hh. }
exact Lean_Decidable_ind p (fun d => Lean_ite T p d value value = value) Hfalse Htrue.
Qed.

Theorem Lean_modCore_zero : forall n :e Lean_Nat, Lean_Nat_modCore n (LeanNum 0) = n.
let n. assume Hn: n :e Lean_Nat.
claim Hnot: 0 /:e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (LeanNum 0).
{ rewrite <- LeanNum_S 0 nat_0. exact Lean_Nat_le_num_not 1 nat_1 0 nat_0 In_0_1. }
rewrite Lean_Nat_modCore_eq_1 n Hn (LeanNum 0) (LeanNum_In 0 nat_0).
rewrite Lean_Nat_decLt_unfold (LeanNum 0) (LeanNum 0).
rewrite Lean_Nat_decLe_canonical (Lean_Nat_succ_node (LeanNum 0))
  (Lean_Nat_succ_typed (LeanNum 0) (LeanNum_In 0 nat_0)) (LeanNum 0) (LeanNum_In 0 nat_0).
rewrite Lean_DecCanon_false (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (LeanNum 0)) Hnot.
exact Lean_dite_false_ap Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (LeanNum 0))
  (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node (LeanNum 0)) (LeanNum 0)) Hnot
  (fun _ => Lean_Nat_modCore_go (LeanNum 0) 0 (Lean_Nat_succ_node n) n 0) (fun _ => n).
Qed.

Theorem Lean_mod_zero : forall n :e Lean_Nat, Lean_Nat_mod n (LeanNum 0) = n.
apply Lean_Nat_ind.
- rewrite <- LeanNum_0. exact Lean_Nat_mod_eq_1 (LeanNum 0) (LeanNum_In 0 nat_0).
- let n. assume Hn: n :e Lean_Nat. assume IH: Lean_Nat_mod n (LeanNum 0) = n.
  rewrite Lean_Nat_mod_eq_2 (LeanNum 0) (LeanNum_In 0 nat_0) n Hn.
  rewrite Lean_modCore_zero (Lean_Nat_succ_node n) (Lean_Nat_succ_typed n Hn).
  exact Lean_ite_same Lean_Nat (Lean_Nat_le_Prop (LeanNum 0) (Lean_Nat_succ_node n))
    (Lean_Nat_succ_node n) (Lean_Nat_decLe (LeanNum 0) (Lean_Nat_succ_node n))
    (Lean_Nat_decLe_In (LeanNum 0) (LeanNum_In 0 nat_0) (Lean_Nat_succ_node n) (Lean_Nat_succ_typed n Hn)).
Qed.

Theorem Lean_mod_zero_witness_positive : forall d, nat_p d -> forall n, nat_p n ->
  Lean_Nat_mod (LeanNum n) (LeanNum (ordsucc d)) = LeanNum 0 ->
  exists q :e Lean_Nat, LeanNum n = Lean_Nat_mul (LeanNum (ordsucc d)) q.
let d. assume Hd: nat_p d. let n. assume Hn: nat_p n.
assume Hzero: Lean_Nat_mod (LeanNum n) (LeanNum (ordsucc d)) = LeanNum 0.
apply nat_euclid d Hd n Hn.
let q. assume Hq: nat_p q /\ (exists r, nat_p r /\ (r :e ordsucc d /\ n = add_nat (mul_nat q (ordsucc d)) r)).
apply Hq. assume Hqn: nat_p q.
assume Hex: exists r, nat_p r /\ (r :e ordsucc d /\ n = add_nat (mul_nat q (ordsucc d)) r).
apply Hex. let r. assume Hr: nat_p r /\ (r :e ordsucc d /\ n = add_nat (mul_nat q (ordsucc d)) r).
apply Hr. assume Hrn: nat_p r. assume Hrest: r :e ordsucc d /\ n = add_nat (mul_nat q (ordsucc d)) r.
apply Hrest. assume Hrd: r :e ordsucc d. assume En: n = add_nat (mul_nat q (ordsucc d)) r.
claim Hrem: Lean_Nat_mod (LeanNum n) (LeanNum (ordsucc d)) = LeanNum r.
{ rewrite En. exact Lean_Nat_mod_num d Hd r Hrn Hrd q Hqn. }
claim Er: r = 0.
{ apply LeanNum_inj r Hrn 0 nat_0.
  exact eq_i_tra (LeanNum r) (Lean_Nat_mod (LeanNum n) (LeanNum (ordsucc d))) (LeanNum 0)
    (eq_sym_i (Lean_Nat_mod (LeanNum n) (LeanNum (ordsucc d))) (LeanNum r) Hrem) Hzero. }
claim En0: n = mul_nat q (ordsucc d).
{ rewrite En. rewrite Er. exact add_nat_0R (mul_nat q (ordsucc d)). }
witness (LeanNum q). apply andI.
- exact LeanNum_In q Hqn.
- rewrite LeanNum_mul (ordsucc d) (nat_ordsucc d Hd) q Hqn.
  rewrite mul_nat_com (ordsucc d) (nat_ordsucc d Hd) q Hqn.
  exact f_eq_i LeanNum n (mul_nat q (ordsucc d)) En0.
Qed.

Theorem Lean_mod_zero_witness_divisor : forall d, nat_p d -> forall n :e Lean_Nat,
  Lean_Nat_mod n (LeanNum d) = LeanNum 0 -> exists q :e Lean_Nat, n = Lean_Nat_mul (LeanNum d) q.
let d. assume Hd: nat_p d.
apply nat_inv d Hd.
- assume Ed: d = 0. rewrite Ed. let n. assume Hn: n :e Lean_Nat.
  assume Hzero: Lean_Nat_mod n (LeanNum 0) = LeanNum 0.
  witness (LeanNum 0). apply andI.
  + exact LeanNum_In 0 nat_0.
  + rewrite Lean_Nat_mul_eq_1 (LeanNum 0) (LeanNum_In 0 nat_0).
    exact eq_i_tra n (Lean_Nat_mod n (LeanNum 0)) (LeanNum 0)
      (eq_sym_i (Lean_Nat_mod n (LeanNum 0)) n (Lean_mod_zero n Hn)) Hzero.
- assume Hex: exists predecessor, nat_p predecessor /\ d = ordsucc predecessor.
  apply Hex. let predecessor. assume Hpre: nat_p predecessor /\ d = ordsucc predecessor.
  apply Hpre. assume Hp: nat_p predecessor. assume Ed: d = ordsucc predecessor.
  rewrite Ed. let n. assume Hn: n :e Lean_Nat.
  apply Lean_Nat_num n Hn. let a. assume Ha: nat_p a /\ n = LeanNum a.
  apply Ha. assume Han: nat_p a. assume En: n = LeanNum a.
  rewrite En. exact Lean_mod_zero_witness_positive predecessor Hp a Han.
Qed.

Theorem Lean_mod_zero_witness : forall d n :e Lean_Nat,
  Lean_Nat_mod n d = LeanNum 0 -> exists q :e Lean_Nat, n = Lean_Nat_mul d q.
let d. assume Hd: d :e Lean_Nat.
apply Lean_Nat_num d Hd. let b. assume Hb: nat_p b /\ d = LeanNum b.
apply Hb. assume Hbn: nat_p b. assume Ed: d = LeanNum b.
rewrite Ed. exact Lean_mod_zero_witness_divisor b Hbn.
Qed.

Theorem Lean_mod_multiple_zero : forall d q :e Lean_Nat,
  Lean_Nat_mod (Lean_Nat_mul d q) d = LeanNum 0.
let d. assume Hd: d :e Lean_Nat.
apply Lean_Nat_num d Hd. let b. assume Hb: nat_p b /\ d = LeanNum b.
apply Hb. assume Hbn: nat_p b. assume Ed: d = LeanNum b.
rewrite Ed. let q. assume Hq: q :e Lean_Nat.
apply Lean_Nat_num q Hq. let a. assume Ha: nat_p a /\ q = LeanNum a.
apply Ha. assume Han: nat_p a. assume Eq: q = LeanNum a.
rewrite Eq. apply nat_inv b Hbn.
- assume Eb: b = 0. rewrite Eb.
  rewrite LeanNum_mul 0 nat_0 a Han. rewrite mul_nat_0L a Han.
  exact Lean_Nat_mod_eq_1 (LeanNum 0) (LeanNum_In 0 nat_0).
- assume Hex: exists predecessor, nat_p predecessor /\ b = ordsucc predecessor.
  apply Hex. let predecessor. assume Hpre: nat_p predecessor /\ b = ordsucc predecessor.
  apply Hpre. assume Hp: nat_p predecessor. assume Eb: b = ordsucc predecessor.
  rewrite Eb.
  rewrite LeanNum_mul (ordsucc predecessor) (nat_ordsucc predecessor Hp) a Han.
  rewrite mul_nat_com (ordsucc predecessor) (nat_ordsucc predecessor Hp) a Han.
  rewrite <- add_nat_0R (mul_nat a (ordsucc predecessor)).
  exact Lean_Nat_mod_num predecessor Hp 0 nat_0 (nat_0_in_ordsucc predecessor Hp) a Han.
Qed.

Definition LeanNatDivides : set -> set -> set := fun d n =>
  Lean_Exists_Prop Lean_Nat (fun q :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)).

Theorem LeanNatDivides_intro : forall d n q :e Lean_Nat,
  n = Lean_Nat_mul d q -> 0 :e LeanNatDivides d n.
let d. assume Hd: d :e Lean_Nat. let n. assume Hn: n :e Lean_Nat.
let q. assume Hq: q :e Lean_Nat. assume Heq: n = Lean_Nat_mul d q.
prove 0 :e Lean_Exists_Prop Lean_Nat (fun q :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)).
apply LeanExists_intro Lean_Nat (fun q :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)) q Hq.
rewrite beta Lean_Nat (fun q => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)) q Hq.
exact Lean_Eq_proof_of Lean_Nat n (Lean_Nat_mul d q) Heq.
Qed.

Theorem LeanNatDivides_num_intro : forall d, nat_p d -> forall n, nat_p n ->
  forall q, nat_p q -> mul_nat d q = n ->
  0 :e Lean_Exists_Prop Lean_Nat
    (fun witness :e Lean_Nat => Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum d) witness)).
let d. assume Hd: nat_p d. let n. assume Hn: nat_p n.
let q. assume Hq: nat_p q. assume Heq: mul_nat d q = n.
exact LeanNatDivides_intro (LeanNum d) (LeanNum_In d Hd) (LeanNum n) (LeanNum_In n Hn)
  (LeanNum q) (LeanNum_In q Hq)
  (eq_sym_i (Lean_Nat_mul (LeanNum d) (LeanNum q)) (LeanNum n) (LeanNum_mul_eq d Hd q Hq n Heq)).
Qed.

Theorem LeanNatDivides_elim : forall d n, forall Q:prop,
  (forall q :e Lean_Nat, n = Lean_Nat_mul d q -> Q) -> 0 :e LeanNatDivides d n -> Q.
let d n Q. assume H: forall q :e Lean_Nat, n = Lean_Nat_mul d q -> Q.
assume Hdiv: 0 :e LeanNatDivides d n.
apply LeanExists_elim Lean_Nat (fun q :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)) Q.
- let q. assume Hq: q :e Lean_Nat.
  assume Hp: 0 :e (fun q :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)) q.
  exact H q Hq (LeanEq_sound Lean_Nat n (Lean_Nat_mul d q) 0
    (In_eq_r 0 ((fun q :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)) q)
      (Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q))
      (beta Lean_Nat (fun q => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)) q Hq) Hp)).
- exact Hdiv.
Qed.

Theorem Lean_mod_zero_divides : forall d n :e Lean_Nat,
  Lean_Nat_mod n d = LeanNum 0 -> 0 :e LeanNatDivides d n.
let d. assume Hd: d :e Lean_Nat. let n. assume Hn: n :e Lean_Nat.
assume Hzero: Lean_Nat_mod n d = LeanNum 0.
apply Lean_mod_zero_witness d Hd n Hn Hzero.
let q. assume Hq: q :e Lean_Nat /\ n = Lean_Nat_mul d q.
apply Hq. assume Hqn: q :e Lean_Nat. assume Heq: n = Lean_Nat_mul d q.
exact LeanNatDivides_intro d Hd n Hn q Hqn Heq.
Qed.

Theorem Lean_divides_mod_zero : forall d n :e Lean_Nat,
  0 :e LeanNatDivides d n -> Lean_Nat_mod n d = LeanNum 0.
let d. assume Hd: d :e Lean_Nat. let n. assume Hn: n :e Lean_Nat.
assume Hdiv: 0 :e LeanNatDivides d n.
apply LeanNatDivides_elim d n (Lean_Nat_mod n d = LeanNum 0).
- let q. assume Hq: q :e Lean_Nat. assume Heq: n = Lean_Nat_mul d q.
  rewrite Heq. exact Lean_mod_multiple_zero d Hd q Hq.
- exact Hdiv.
Qed.

Theorem LeanNatDivides_num_refute : forall d, nat_p d -> forall n, nat_p n ->
  forall r, nat_p r -> r <> 0 ->
  Lean_Nat_mod (LeanNum n) (LeanNum d) = LeanNum r ->
  0 /:e Lean_Exists_Prop Lean_Nat
    (fun witness :e Lean_Nat => Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum d) witness)).
let d. assume Hd: nat_p d. let n. assume Hn: nat_p n.
let r. assume Hr: nat_p r. assume Hnonzero: r <> 0.
assume Hmod: Lean_Nat_mod (LeanNum n) (LeanNum d) = LeanNum r.
assume Hdiv: 0 :e LeanNatDivides (LeanNum d) (LeanNum n).
apply Hnonzero.
apply LeanNum_inj r Hr 0 nat_0.
rewrite <- Hmod.
exact Lean_divides_mod_zero (LeanNum d) (LeanNum_In d Hd) (LeanNum n) (LeanNum_In n Hn) Hdiv.
Qed.

Theorem Lean_mod_divisibility_iff : forall d n :e Lean_Nat,
  0 :e Lean_Iff_Prop (Lean_Eq_Prop Lean_Nat (Lean_Nat_mod n d) (LeanNum 0)) (LeanNatDivides d n).
let d. assume Hd: d :e Lean_Nat. let n. assume Hn: n :e Lean_Nat.
exact LeanIff_intro
  (Lean_Eq_Prop Lean_Nat (Lean_Nat_mod n d) (LeanNum 0))
  (Lean_Eq_Prop_prop Lean_Nat (Lean_Nat_mod n d) (LeanNum 0))
  (LeanNatDivides d n)
  (Lean_Exists_Prop_prop Lean_Nat (fun q :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul d q)))
  (fun H => Lean_mod_zero_divides d Hd n Hn (LeanEq_sound Lean_Nat (Lean_Nat_mod n d) (LeanNum 0) 0 H))
  (fun H => Lean_Eq_proof_of Lean_Nat (Lean_Nat_mod n d) (LeanNum 0) (Lean_divides_mod_zero d Hd n Hn H)).
Qed.
