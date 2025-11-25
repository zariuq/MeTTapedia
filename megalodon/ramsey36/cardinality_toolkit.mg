Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 nat_p_12.
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13 nat_p_13))).
Qed.

Theorem equip_17_is_17 : equip 17 17.
exact equip_ref 17.
Qed.

Theorem ordsucc_setminus_singleton_base : forall n:set,
  ordinal n -> ordsucc n :\: {n} = n.
let n.
assume Hn: ordinal n.
prove ordsucc n :\: {n} = n.
apply set_ext.
- prove ordsucc n :\: {n} c= n.
  let x. assume Hx: x :e ordsucc n :\: {n}.
  apply setminusE (ordsucc n) {n} x Hx.
  assume Hx_succ: x :e ordsucc n.
  assume Hx_notn: x /:e {n}.
  apply ordsuccE n x Hx_succ.
  + assume Hx_n: x :e n.
    exact Hx_n.
  + assume Hx_eq: x = n.
    apply Hx_notn.
    prove x :e {n}.
    rewrite Hx_eq.
    exact SingI n.
- prove n c= ordsucc n :\: {n}.
  let x. assume Hx: x :e n.
  apply setminusI (ordsucc n) {n} x.
  + prove x :e ordsucc n.
    exact ordsuccI1 n x Hx.
  + prove x /:e {n}.
    assume Hxn: x :e {n}.
    claim Hxeqn: x = n.
      exact SingE n x Hxn.
    claim Hnn: n :e n.
      rewrite <- Hxeqn at 1.
      exact Hx.
    exact In_irref n Hnn.
Qed.

Theorem equip_17_without_17 : equip 17 (18 :\: {17}).
prove equip 17 (ordsucc 17 :\: {17}).
claim H17ord: ordinal 17.
  exact nat_p_ordinal 17 nat_p_17.
rewrite ordsucc_setminus_singleton_base 17 H17ord.
exact equip_17_is_17.
Qed.

Theorem nat_p_18 : nat_p 18.
exact nat_ordsucc 17 nat_p_17.
Qed.

Theorem In_17_18 : forall x :e 17, x :e 18.
let x. assume Hx: x :e 17.
prove x :e ordsucc 17.
exact ordsuccI1 17 x Hx.
Qed.


Theorem equip_17_without_one : forall v :e 18, equip 17 (18 :\: {v}).
Admitted.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)).
Qed.

Theorem nat_p_6 : nat_p 6.
exact nat_ordsucc 5 nat_p_5.
Qed.

Theorem in_5_13 : 5 :e 13.
prove 5 :e ordsucc 12.
apply ordsuccI1 12.
prove 5 :e 12.
apply ordsuccI1 11.
prove 5 :e 11.
apply ordsuccI1 10.
prove 5 :e 10.
apply ordsuccI1 9.
prove 5 :e 9.
apply ordsuccI1 8.
prove 5 :e 8.
apply ordsuccI1 7.
prove 5 :e 7.
apply ordsuccI1 6.
prove 5 :e 6.
exact ordsuccI2 5.
Qed.

Theorem Subq_5_13 : 5 c= 13.
let x. assume Hx: x :e 5.
exact nat_trans 13 nat_p_13 5 in_5_13 x Hx.
Qed.

Theorem equip_Subq_exists : forall k n V:set,
  k c= n ->
  equip n V ->
  exists U:set, U c= V /\ equip k U.
let k. let n. let V.
assume Hkn: k c= n.
assume Heq: equip n V.
apply Heq.
let f: set -> set.
assume Hbij: bij n V f.
set T := {f i | i :e k}.
witness T.
prove T c= V /\ equip k T.
apply and3E (forall u :e n, f u :e V) (forall u v :e n, f u = f v -> u = v) (forall w :e V, exists u :e n, f u = w) Hbij (T c= V /\ equip k T).
assume HfV: forall u :e n, f u :e V.
assume Hinj: forall u v :e n, f u = f v -> u = v.
assume Hsurj: forall w :e V, exists u :e n, f u = w.
apply andI (T c= V) (equip k T).
- prove T c= V.
  let y. assume Hy: y :e T.
  apply ReplE_impred k f y Hy (y :e V).
  let i. assume Hi: i :e k.
  assume Hyi: y = f i.
  prove y :e V.
  claim Hin: i :e n. exact Hkn i Hi.
  claim HfiV: f i :e V. exact HfV i Hin.
  exact Hyi (fun a b => b :e V) HfiV.
- prove equip k T.
  prove exists g : set -> set, bij k T g.
  witness f.
  prove bij k T f.
  apply and3I (forall u :e k, f u :e T) (forall u v :e k, f u = f v -> u = v) (forall w :e T, exists u :e k, f u = w).
  + prove forall u :e k, f u :e T.
    let u. assume Hu: u :e k.
    exact ReplI k f u Hu.
  + prove forall u v :e k, f u = f v -> u = v.
    let u. assume Hu: u :e k.
    let v. assume Hv: v :e k.
    assume Hfuv: f u = f v.
    exact Hinj u (Hkn u Hu) v (Hkn v Hv) Hfuv.
  + prove forall w :e T, exists u :e k, f u = w.
    let w. assume Hw: w :e T.
    apply ReplE_impred k f w Hw (exists u :e k, f u = w).
    let i. assume Hi: i :e k.
    assume Hwi: w = f i.
    witness i.
    prove i :e k /\ f i = w.
    claim Hfiw: f i = w.
      prove forall Q: set -> set -> prop, Q (f i) w -> Q w (f i).
      let Q: set -> set -> prop. assume HQ: Q (f i) w.
      exact Hwi (fun a b => Q b a) HQ.
    exact andI (i :e k) (f i = w) Hi Hfiw.
Qed.

Theorem in_6_17 : 6 :e 17.
prove 6 :e ordsucc 16.
apply ordsuccI1 16.
prove 6 :e 16.
apply ordsuccI1 15.
prove 6 :e 15.
apply ordsuccI1 14.
prove 6 :e 14.
apply ordsuccI1 13.
prove 6 :e 13.
apply ordsuccI1 12.
prove 6 :e 12.
apply ordsuccI1 11.
prove 6 :e 11.
apply ordsuccI1 10.
prove 6 :e 10.
apply ordsuccI1 9.
prove 6 :e 9.
apply ordsuccI1 8.
prove 6 :e 8.
apply ordsuccI1 7.
prove 6 :e 7.
exact ordsuccI2 6.
Qed.

Theorem six_subset_17 : 6 c= 17.
let x. assume Hx: x :e 6.
exact nat_trans 17 nat_p_17 6 in_6_17 x Hx.
Qed.

Theorem in_12_17 : 12 :e 17.
prove 12 :e ordsucc 16.
apply ordsuccI1 16.
prove 12 :e 16.
apply ordsuccI1 15.
prove 12 :e 15.
apply ordsuccI1 14.
prove 12 :e 14.
apply ordsuccI1 13.
prove 12 :e 13.
exact ordsuccI2 12.
Qed.

Theorem twelve_subset_17 : 12 c= 17.
let x. assume Hx: x :e 12.
exact nat_trans 17 nat_p_17 12 in_12_17 x Hx.
Qed.

Theorem no_6subset_implies_small : forall N:set, forall n:set,
  nat_p n ->
  equip n N ->
  ~(exists T:set, T c= N /\ equip 6 T) ->
  ~(6 c= n).
let N n.
assume Hn: nat_p n.
assume HeqN: equip n N.
assume Hno6: ~(exists T:set, T c= N /\ equip 6 T).
prove ~(6 c= n).
assume H6n: 6 c= n.
apply Hno6.
prove exists T:set, T c= N /\ equip 6 T.
exact equip_Subq_exists 6 n N H6n HeqN.
Qed.

Theorem has_subset_from_cardinality : forall N:set, forall n:set,
  nat_p n ->
  6 c= n ->
  equip n N ->
  exists T:set, T c= N /\ equip 6 T.
let N n.
assume Hn: nat_p n.
assume H6n: 6 c= n.
assume HeqN: equip n N.
exact equip_Subq_exists 6 n N H6n HeqN.
Qed.

Theorem nat_trichotomy_6 : forall n:set,
  nat_p n -> n :e 6 \/ n = 6 \/ 6 c= n.
Admitted.

Theorem no_6subset_bound_5 : forall N:set, forall n:set,
  nat_p n ->
  equip n N ->
  ~(exists T:set, T c= N /\ equip 6 T) ->
  n :e 6.
Admitted.

Theorem partition_17_5_implies_12 : forall V N Non:set,
  equip 17 V ->
  N c= V ->
  Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  ~(exists T, T c= N /\ equip 6 T) ->
  exists S, S c= Non /\ equip 12 S.
Admitted.
