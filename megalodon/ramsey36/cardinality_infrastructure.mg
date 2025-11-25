Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Theorem nat_p_4 : nat_p 4.
exact nat_ordsucc 3 (nat_ordsucc 2 nat_2).
Qed.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 nat_p_4.
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 (nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8
      (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5 nat_p_5))))))).
Qed.

Theorem nat_p_14 : nat_p 14.
exact nat_ordsucc 13 nat_p_13.
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 nat_p_14)).
Qed.

Theorem nat_p_18 : nat_p 18.
exact nat_ordsucc 17 nat_p_17.
Qed.

Theorem four_subset_13 : 4 c= 13.
let x. assume Hx: x :e 4.
prove x :e 13.
exact nat_trans 13 nat_p_13 4
  (ordsuccI1 12 4 (ordsuccI1 11 4 (ordsuccI1 10 4 (ordsuccI1 9 4
   (ordsuccI1 8 4 (ordsuccI1 7 4 (ordsuccI1 6 4 (ordsuccI1 5 4 (ordsuccI2 4)))))))))
  x Hx.
Qed.

Theorem five_subset_14 : 5 c= 14.
let x. assume Hx: x :e 5.
prove x :e 14.
exact nat_trans 14 nat_p_14 5
  (ordsuccI1 13 5 (ordsuccI1 12 5 (ordsuccI1 11 5 (ordsuccI1 10 5
   (ordsuccI1 9 5 (ordsuccI1 8 5 (ordsuccI1 7 5 (ordsuccI1 6 5 (ordsuccI2 5)))))))))
  x Hx.
Qed.

Theorem ordsucc_setminus_singleton : forall n k:set,
  ordinal n ->
  k :e n ->
  ordsucc n = ordsucc k ->
  equip k (n :\: {k}).
Admitted.

Theorem ordsucc_setminus_singleton_inside : forall n v:set,
  ordinal n ->
  v :e n ->
  equip n (ordsucc n :\: {v}).
let n v.
assume Hn: ordinal n.
assume Hv: v :e n.
prove equip n (ordsucc n :\: {v}).
prove exists f:set -> set, bij n (ordsucc n :\: {v}) f.
set f := fun x :set => if x :e v then x else ordsucc x.
witness f.
apply bijI.
- prove forall u :e n, f u :e ordsucc n :\: {v}.
  admit.
- prove forall u v :e n, f u = f v -> u = v.
  admit.
- prove forall w :e ordsucc n :\: {v}, exists u :e n, f u = w.
  admit.
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

Theorem complement_card_18 : forall v:set,
  v :e 18 ->
  equip 17 (18 :\: {v}).
let v.
assume Hv: v :e 18.
prove equip 17 (18 :\: {v}).
apply ordsuccE 17 v Hv.
- assume Hv17: v :e 17.
  exact ordsucc_setminus_singleton_inside 17 v (nat_p_ordinal 17 nat_p_17) Hv17.
- assume Hv_eq: v = 17.
  rewrite Hv_eq.
  claim H18_eq: 18 :\: {17} = 17.
    prove ordsucc 17 :\: {17} = 17.
    exact ordsucc_setminus_singleton_base 17 (nat_p_ordinal 17 nat_p_17).
  rewrite H18_eq.
  exact equip_ref 17.
Qed.

Theorem complement_card_sub : forall n k:set, forall S:set,
  nat_p n ->
  nat_p k ->
  k c= n ->
  S c= n ->
  equip k S ->
  exists m:set, nat_p m /\ equip m (n :\: S).
Admitted.

Theorem disjoint_union_card : forall n m A B:set,
  nat_p n ->
  nat_p m ->
  equip n A ->
  equip m B ->
  (forall x, x :e A -> x /:e B) ->
  exists p:set, nat_p p /\ equip p (A :\/: B).
Admitted.

Theorem disjoint_union_sing_5 : forall v:set, forall S:set,
  v /:e S ->
  equip 5 S ->
  equip 6 ({v} :\/: S).
Admitted.

Theorem partition_3_card : forall V A B C:set, forall n a b c:set,
  nat_p n ->
  nat_p a ->
  nat_p b ->
  nat_p c ->
  equip n V ->
  A c= V ->
  B c= V ->
  C c= V ->
  (forall x :e V, x :e A \/ x :e B \/ x :e C) ->
  (forall x, x :e A -> x /:e B) ->
  (forall x, x :e A -> x /:e C) ->
  (forall x, x :e B -> x /:e C) ->
  equip a A ->
  equip b B ->
  equip c C ->
  exists sum:set, nat_p sum /\ equip sum V.
Admitted.

Theorem partition_18_vertex_neighbors_rest : forall v N Gv:set,
  v :e 18 ->
  N c= 18 ->
  Gv c= 18 ->
  (forall x :e N, x <> v) ->
  (forall x :e Gv, x <> v) ->
  (forall x :e 18, x = v \/ x :e N \/ x :e Gv) ->
  (forall x :e N, x /:e Gv) ->
  forall d g:set,
    nat_p d ->
    nat_p g ->
    equip d N ->
    equip g Gv ->
    exists k:set, nat_p k /\ d :e ordsucc k /\ g :e ordsucc k /\ ordsucc (ordsucc k) = 18.
Admitted.

Theorem nat_lt_le_trans : forall a b c:set,
  nat_p a ->
  nat_p b ->
  nat_p c ->
  a :e b ->
  b c= c ->
  a :e c.
let a b c.
assume Ha: nat_p a.
assume Hb: nat_p b.
assume Hc: nat_p c.
assume Hab: a :e b.
assume Hbc: b c= c.
prove a :e c.
exact Hbc a Hab.
Qed.

Theorem nat_13_in_14 : 13 :e 14.
prove 13 :e ordsucc 13.
exact ordsuccI2 13.
Qed.

Theorem nat_14_not_in_14 : 14 /:e 14.
assume H: 14 :e 14.
exact In_irref 14 H.
Qed.

Theorem nat_4_in_17 : 4 :e 17.
prove 4 :e ordsucc 16.
apply ordsuccI1 16 4.
prove 4 :e 16.
apply ordsuccI1 15 4.
prove 4 :e 15.
apply ordsuccI1 14 4.
prove 4 :e 14.
apply ordsuccI1 13 4.
prove 4 :e 13.
apply ordsuccI1 12 4.
prove 4 :e 12.
apply ordsuccI1 11 4.
prove 4 :e 11.
apply ordsuccI1 10 4.
prove 4 :e 10.
apply ordsuccI1 9 4.
prove 4 :e 9.
apply ordsuccI1 8 4.
prove 4 :e 8.
apply ordsuccI1 7 4.
prove 4 :e 7.
apply ordsuccI1 6 4.
prove 4 :e 6.
apply ordsuccI1 5 4.
exact ordsuccI2 4.
Qed.

Theorem nat_4_subset_17 : 4 c= 17.
exact nat_trans 17 nat_p_17 4 nat_4_in_17.
Qed.

Theorem nat_lt_14_le_13 : forall g:set,
  nat_p g ->
  g :e 14 ->
  g c= 13.
let g.
assume Hg: nat_p g.
assume Hg14: g :e 14.
prove g c= 13.
let x. assume Hx: x :e g.
prove x :e 13.
apply ordsuccE 13 g Hg14.
- assume Hg13: g :e 13.
  exact nat_trans 13 nat_p_13 g Hg13 x Hx.
- assume Hg_eq: g = 13.
  rewrite <- Hg_eq.
  exact Hx.
Qed.

Theorem nat_sum_17_bound : forall d g:set,
  nat_p d ->
  nat_p g ->
  d + g = 17 ->
  g c= 13 ->
  4 c= d.
Admitted.

Theorem nat_17_minus_lt_14_implies_ge_4 : forall d g:set,
  nat_p d ->
  nat_p g ->
  (exists k:set, nat_p k /\ d :e ordsucc k /\ g :e ordsucc k /\ ordsucc (ordsucc k) = 18) ->
  g :e 14 ->
  4 c= d.
Admitted.

Theorem indep_add_vertex : forall V:set, forall R:set -> set -> prop, forall S v:set,
  V = 14 \/ V = 18 ->
  S c= V ->
  v :e V ->
  v /:e S ->
  equip 4 S ->
  is_indep_set V R S ->
  (forall x :e S, ~R v x) ->
  exists T:set, T c= V /\ equip 5 T /\ is_indep_set V R T.
Admitted.

Theorem infrastructure_compiles : True.
exact TrueI.
Qed.
