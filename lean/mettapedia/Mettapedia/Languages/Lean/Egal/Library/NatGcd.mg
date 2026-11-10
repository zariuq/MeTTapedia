(** The remainder gives the decreasing rank used by Euclid's recursion. **)
Theorem LeanGcd_remainder : forall p, nat_p p -> forall n :e Lean_Nat,
  exists r, nat_p r /\ r :e ordsucc p /\ Lean_Nat_mod n (LeanNum (ordsucc p)) = LeanNum r.
let p. assume Hp: nat_p p. let n. assume Hn: n :e Lean_Nat.
apply Lean_Nat_num n Hn. let a. assume Ha: nat_p a /\ n = LeanNum a.
apply Ha. assume Han: nat_p a. assume En: n = LeanNum a.
apply nat_euclid p Hp a Han. let q.
assume Hq: nat_p q /\ (exists r, nat_p r /\ (r :e ordsucc p /\ a = add_nat (mul_nat q (ordsucc p)) r)).
apply Hq. assume Hqn: nat_p q.
assume Hex: exists r, nat_p r /\ (r :e ordsucc p /\ a = add_nat (mul_nat q (ordsucc p)) r).
apply Hex. let r. assume Hr: nat_p r /\ (r :e ordsucc p /\ a = add_nat (mul_nat q (ordsucc p)) r).
apply Hr. assume Hrn: nat_p r.
assume Hrest: r :e ordsucc p /\ a = add_nat (mul_nat q (ordsucc p)) r.
apply Hrest. assume Hrp: r :e ordsucc p. assume Ea: a = add_nat (mul_nat q (ordsucc p)) r.
witness r. apply and3I.
- exact Hrn.
- exact Hrp.
- rewrite En. rewrite Ea. exact Lean_Nat_mod_num p Hp r Hrn Hrp q Hqn.
Qed.

Theorem LeanGcdFuel_zero : forall k, nat_p k -> forall n :e Lean_Nat,
  Lean_Nat_gcdFuel (LeanNum (ordsucc k)) (LeanNum 0) n = n.
let k. assume Hk: nat_p k. let n. assume Hn: n :e Lean_Nat.
rewrite LeanNum_S k Hk.
rewrite Lean_Nat_gcdFuel_eq_2 (LeanNum 0) (LeanNum_In 0 nat_0) n Hn (LeanNum k) (LeanNum_In k Hk).
rewrite Lean_instDecidableEqNat_unfold (LeanNum 0) (LeanNum 0).
rewrite Lean_Nat_decEq_canonical (LeanNum 0) (LeanNum_In 0 nat_0) (LeanNum 0) (LeanNum_In 0 nat_0).
rewrite Lean_DecCanon_true (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) (Lean_Eq_num_refl 0).
exact Lean_ite_true_ap Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) (Lean_Eq_num_refl 0)
  n (Lean_Nat_gcdFuel (LeanNum k) (Lean_Nat_mod n (LeanNum 0)) (LeanNum 0)).
Qed.

Theorem LeanGcdFuel_positive : forall k, nat_p k -> forall p, nat_p p -> forall n :e Lean_Nat,
  Lean_Nat_gcdFuel (LeanNum (ordsucc k)) (LeanNum (ordsucc p)) n =
  Lean_Nat_gcdFuel (LeanNum k) (Lean_Nat_mod n (LeanNum (ordsucc p))) (LeanNum (ordsucc p)).
let k. assume Hk: nat_p k. let p. assume Hp: nat_p p. let n. assume Hn: n :e Lean_Nat.
claim Hm: (LeanNum (ordsucc p)) :e Lean_Nat.
{ exact LeanNum_In (ordsucc p) (nat_ordsucc p Hp). }
claim Hfalse: 0 /:e Lean_Eq_Prop Lean_Nat (LeanNum (ordsucc p)) (LeanNum 0).
{ exact Lean_Eq_num_not (ordsucc p) (nat_ordsucc p Hp) 0 nat_0 (neq_ordsucc_0 p). }
rewrite LeanNum_S k Hk.
rewrite Lean_Nat_gcdFuel_eq_2 (LeanNum (ordsucc p)) Hm n Hn (LeanNum k) (LeanNum_In k Hk).
rewrite Lean_instDecidableEqNat_unfold (LeanNum (ordsucc p)) (LeanNum 0).
rewrite Lean_Nat_decEq_canonical (LeanNum (ordsucc p)) Hm (LeanNum 0) (LeanNum_In 0 nat_0).
rewrite Lean_DecCanon_false (Lean_Eq_Prop Lean_Nat (LeanNum (ordsucc p)) (LeanNum 0)) Hfalse.
exact Lean_ite_false_ap Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum (ordsucc p)) (LeanNum 0))
  (Lean_Eq_Prop_prop Lean_Nat (LeanNum (ordsucc p)) (LeanNum 0)) Hfalse n
  (Lean_Nat_gcdFuel (LeanNum k) (Lean_Nat_mod n (LeanNum (ordsucc p))) (LeanNum (ordsucc p))).
Qed.

Theorem LeanGcdFuel_stable : forall k, nat_p k -> forall l, nat_p l ->
  forall m, nat_p m -> forall n :e Lean_Nat, m :e k -> m :e l ->
  Lean_Nat_gcdFuel (LeanNum k) (LeanNum m) n = Lean_Nat_gcdFuel (LeanNum l) (LeanNum m) n.
apply nat_ind.
- let l. assume Hl: nat_p l. let m. assume Hm: nat_p m. let n. assume Hn: n :e Lean_Nat.
  assume Hmk: m :e 0. assume Hml: m :e l.
  exact FalseE (EmptyE m Hmk)
    (Lean_Nat_gcdFuel (LeanNum 0) (LeanNum m) n = Lean_Nat_gcdFuel (LeanNum l) (LeanNum m) n).
- let k. assume Hk: nat_p k.
  assume IH: forall l, nat_p l -> forall m, nat_p m -> forall n :e Lean_Nat, m :e k -> m :e l ->
    Lean_Nat_gcdFuel (LeanNum k) (LeanNum m) n = Lean_Nat_gcdFuel (LeanNum l) (LeanNum m) n.
  let l. assume Hl: nat_p l. apply nat_inv l Hl.
  + assume El: l = 0. rewrite El. let m. assume Hm: nat_p m. let n. assume Hn: n :e Lean_Nat.
    assume Hmk: m :e ordsucc k. assume Hml: m :e 0.
    exact FalseE (EmptyE m Hml)
      (Lean_Nat_gcdFuel (LeanNum (ordsucc k)) (LeanNum m) n = Lean_Nat_gcdFuel (LeanNum 0) (LeanNum m) n).
  + assume Hex: exists j, nat_p j /\ l = ordsucc j.
    apply Hex. let j. assume Hj: nat_p j /\ l = ordsucc j.
    apply Hj. assume Hjn: nat_p j. assume El: l = ordsucc j. rewrite El.
    let m. assume Hm: nat_p m. apply nat_inv m Hm.
    * assume Em: m = 0. rewrite Em. let n. assume Hn: n :e Lean_Nat.
      assume Hmk: 0 :e ordsucc k. assume Hmj: 0 :e ordsucc j.
      rewrite LeanGcdFuel_zero k Hk n Hn. rewrite LeanGcdFuel_zero j Hjn n Hn. reflexivity.
    * assume Hpos: exists p, nat_p p /\ m = ordsucc p.
      apply Hpos. let p. assume Hp: nat_p p /\ m = ordsucc p.
      apply Hp. assume Hpn: nat_p p. assume Em: m = ordsucc p. rewrite Em.
      let n. assume Hn: n :e Lean_Nat.
      assume Hmk: ordsucc p :e ordsucc k. assume Hmj: ordsucc p :e ordsucc j.
      rewrite LeanGcdFuel_positive k Hk p Hpn n Hn.
      rewrite LeanGcdFuel_positive j Hjn p Hpn n Hn.
      apply LeanGcd_remainder p Hpn n Hn.
      let r. assume Hr: nat_p r /\ r :e ordsucc p /\ Lean_Nat_mod n (LeanNum (ordsucc p)) = LeanNum r.
      apply and3E (nat_p r) (r :e ordsucc p) (Lean_Nat_mod n (LeanNum (ordsucc p)) = LeanNum r) Hr.
      assume Hrn: nat_p r. assume Hrp: r :e ordsucc p.
      assume Er: Lean_Nat_mod n (LeanNum (ordsucc p)) = LeanNum r.
      rewrite Er.
      exact IH j Hjn r Hrn (LeanNum (ordsucc p)) (LeanNum_In (ordsucc p) (nat_ordsucc p Hpn))
        (nat_ordsucc_trans k Hk (ordsucc p) Hmk r Hrp) (nat_ordsucc_trans j Hjn (ordsucc p) Hmj r Hrp).
Qed.

Theorem LeanGcd_zero : forall n :e Lean_Nat, Lean_Nat_gcd (LeanNum 0) n = n.
let n. assume Hn: n :e Lean_Nat.
rewrite Lean_Nat_gcd_unfold (LeanNum 0) n.
rewrite <- LeanNum_S 0 nat_0.
exact LeanGcdFuel_zero 0 nat_0 n Hn.
Qed.

Theorem LeanGcd_positive : forall p, nat_p p -> forall n :e Lean_Nat,
  Lean_Nat_gcd (LeanNum (ordsucc p)) n =
    Lean_Nat_gcd (Lean_Nat_mod n (LeanNum (ordsucc p))) (LeanNum (ordsucc p)).
let p. assume Hp: nat_p p. let n. assume Hn: n :e Lean_Nat.
rewrite Lean_Nat_gcd_unfold (LeanNum (ordsucc p)) n.
rewrite <- LeanNum_S (ordsucc p) (nat_ordsucc p Hp).
rewrite LeanGcdFuel_positive (ordsucc p) (nat_ordsucc p Hp) p Hp n Hn.
apply LeanGcd_remainder p Hp n Hn. let r.
assume Hr: nat_p r /\ r :e ordsucc p /\ Lean_Nat_mod n (LeanNum (ordsucc p)) = LeanNum r.
apply and3E (nat_p r) (r :e ordsucc p) (Lean_Nat_mod n (LeanNum (ordsucc p)) = LeanNum r) Hr.
assume Hrn: nat_p r. assume Hrp: r :e ordsucc p.
assume Er: Lean_Nat_mod n (LeanNum (ordsucc p)) = LeanNum r.
rewrite Er. rewrite Lean_Nat_gcd_unfold (LeanNum r) (LeanNum (ordsucc p)).
rewrite <- LeanNum_S r Hrn.
exact LeanGcdFuel_stable (ordsucc p) (nat_ordsucc p Hp) (ordsucc r) (nat_ordsucc r Hrn)
  r Hrn (LeanNum (ordsucc p)) (LeanNum_In (ordsucc p) (nat_ordsucc p Hp)) Hrp (ordsuccI2 r).
Qed.

Theorem LeanGcd_equation : forall m n :e Lean_Nat,
  Lean_Nat_gcd m n = Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat m (LeanNum 0))
    (Lean_instDecidableEqNat m (LeanNum 0)) n (Lean_Nat_gcd (Lean_Nat_mod n m) m).
let m. assume Hm: m :e Lean_Nat. let n. assume Hn: n :e Lean_Nat.
apply Lean_Nat_num m Hm. let a. assume Ha: nat_p a /\ m = LeanNum a.
apply Ha. assume Han: nat_p a. assume Em: m = LeanNum a. rewrite Em.
apply nat_inv a Han.
- assume Ea: a = 0. rewrite Ea. rewrite LeanGcd_zero n Hn.
  rewrite Lean_instDecidableEqNat_unfold (LeanNum 0) (LeanNum 0).
  rewrite Lean_Nat_decEq_canonical (LeanNum 0) (LeanNum_In 0 nat_0) (LeanNum 0) (LeanNum_In 0 nat_0).
  rewrite Lean_DecCanon_true (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) (Lean_Eq_num_refl 0).
  rewrite Lean_ite_true_ap Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) (Lean_Eq_num_refl 0)
    n (Lean_Nat_gcd (Lean_Nat_mod n (LeanNum 0)) (LeanNum 0)).
  reflexivity.
- assume Hex: exists p, nat_p p /\ a = ordsucc p.
  apply Hex. let p. assume Hp: nat_p p /\ a = ordsucc p.
  apply Hp. assume Hpn: nat_p p. assume Ea: a = ordsucc p. rewrite Ea.
  claim Hfalse: 0 /:e Lean_Eq_Prop Lean_Nat (LeanNum (ordsucc p)) (LeanNum 0).
  { exact Lean_Eq_num_not (ordsucc p) (nat_ordsucc p Hpn) 0 nat_0 (neq_ordsucc_0 p). }
  rewrite LeanGcd_positive p Hpn n Hn.
  rewrite Lean_instDecidableEqNat_unfold (LeanNum (ordsucc p)) (LeanNum 0).
  rewrite Lean_Nat_decEq_canonical (LeanNum (ordsucc p)) (LeanNum_In (ordsucc p) (nat_ordsucc p Hpn))
    (LeanNum 0) (LeanNum_In 0 nat_0).
  rewrite Lean_DecCanon_false (Lean_Eq_Prop Lean_Nat (LeanNum (ordsucc p)) (LeanNum 0)) Hfalse.
  rewrite Lean_ite_false_ap Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum (ordsucc p)) (LeanNum 0))
    (Lean_Eq_Prop_prop Lean_Nat (LeanNum (ordsucc p)) (LeanNum 0)) Hfalse n
    (Lean_Nat_gcd (Lean_Nat_mod n (LeanNum (ordsucc p))) (LeanNum (ordsucc p))).
  reflexivity.
Qed.
