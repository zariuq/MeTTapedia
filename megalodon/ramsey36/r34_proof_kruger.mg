Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Definition TwoRamseyProp : set -> set -> set -> prop
 := fun M N V =>
      forall R:set -> set -> prop,
        (forall x y, R x y -> R y x)
       -> ((exists X c= V, equip M X /\ (forall x y :e X, x <> y -> R x y))
        \/ (exists Y c= V, equip N Y /\ (forall x y :e Y, x <> y -> ~R x y))).

Theorem nat_p_9 : nat_p 9.
exact nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5
      (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))).
Qed.

Theorem nat_p_8 : nat_p 8.
exact nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5
      (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))).
Qed.

Theorem TwoRamseyProp_3_3_6 : TwoRamseyProp 3 3 6.
Admitted.

Theorem degree_upper_from_triangle_free : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 9 R ->
  no_k_indep 9 R 4 ->
  forall v :e 9, forall N:set, N c= 9 ->
    (forall x :e N, R v x /\ x <> v) ->
    equip 4 N -> False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 9 R.
assume Hno4: no_k_indep 9 R 4.
let v. assume Hv: v :e 9.
let N. assume HN9: N c= 9.
assume HNadj: forall x :e N, R v x /\ x <> v.
assume HN4: equip 4 N.
prove False.
apply Hno4 N HN9 HN4.
prove is_indep_set 9 R N.
prove N c= 9 /\ (forall x :e N, forall y :e N, x <> y -> ~R x y).
apply andI.
- exact HN9.
- prove forall x :e N, forall y :e N, x <> y -> ~R x y.
  let x. assume Hx: x :e N.
  let y. assume Hy: y :e N.
  assume Hneq: x <> y.
  prove ~R x y.
  claim HRvx: R v x. exact andEL (R v x) (x <> v) (HNadj x Hx).
  claim HRvy: R v y. exact andEL (R v y) (y <> v) (HNadj y Hy).
  assume HRxy: R x y.
  apply Htf x (HN9 x Hx) y (HN9 y Hy) v Hv HRxy (Hsym v y HRvy) (Hsym v x HRvx).
Qed.

Theorem equip_adjoin_sing : forall n:set, forall X y:set,
  nat_p n ->
  equip n X ->
  y /:e X ->
  equip (ordsucc n) (X :\/: {y}).
let n X y.
assume Hn: nat_p n.
assume HX: equip n X.
assume Hy: y /:e X.
apply HX.
let f. assume Hf: bij n X f.
apply bijE n X f Hf.
assume Hf1: forall i :e n, f i :e X.
assume Hf2: forall i j :e n, f i = f j -> i = j.
assume Hf3: forall x :e X, exists i :e n, f i = x.
prove exists g:set -> set, bij (ordsucc n) (X :\/: {y}) g.
claim Lg: exists g:set -> set, (forall i :e n, g i = f i) /\ g n = y.
{ witness (fun i : set => if i :e n then f i else y).
  apply andI.
  - let i. assume Hi. exact If_i_1 (i :e n) (f i) y Hi.
  - exact If_i_0 (n :e n) (f n) y (In_irref n).
}
apply Lg.
let g. assume H. apply H.
assume Hg1 Hg2.
witness g.
apply bijI.
- let i. assume Hi. apply ordsuccE n i Hi.
  + assume H1: i :e n.
    apply binunionI1.
    rewrite Hg1 i H1.
    exact Hf1 i H1.
  + assume H1: i = n.
    apply binunionI2.
    rewrite H1.
    rewrite Hg2.
    exact SingI y.
- let i. assume Hi. let j. assume Hj.
  apply ordsuccE n i Hi.
  + assume H1: i :e n.
    rewrite Hg1 i H1.
    apply ordsuccE n j Hj.
    * assume H2: j :e n.
      rewrite Hg1 j H2.
      exact Hf2 i H1 j H2.
    * assume H2: j = n.
      rewrite H2.
      rewrite Hg2.
      assume H3: f i = y.
      apply Hy.
      rewrite <- H3.
      exact Hf1 i H1.
  + assume H1: i = n.
    rewrite H1.
    rewrite Hg2.
    apply ordsuccE n j Hj.
    * assume H2: j :e n.
      rewrite Hg1 j H2.
      assume H3: y = f j.
      apply Hy.
      rewrite H3.
      exact Hf1 j H2.
    * assume H2: j = n.
      rewrite H2.
      assume _.
      reflexivity.
- let x. assume Hx.
  apply binunionE X {y} x Hx.
  + assume H1: x :e X.
    apply Hf3 x H1.
    let i. assume H. apply H.
    assume Hi: i :e n.
    assume H2: f i = x.
    witness i.
    apply andI.
    * apply ordsuccI1. exact Hi.
    * rewrite Hg1 i Hi.
      exact H2.
  + assume H1: x :e {y}.
    witness n.
    apply andI.
    * apply ordsuccI2.
    * rewrite SingE y x H1.
      exact Hg2.
Qed.

Theorem disjoint_union_card : forall m:set, nat_p m -> forall n:set, forall A B:set,
  nat_p n ->
  equip m A ->
  equip n B ->
  (forall x, x :e A -> x /:e B) ->
  equip (m + n) (A :\/: B).
let m.
Admitted.
Theorem nat_p_3 : nat_p 3.
exact nat_ordsucc 2 nat_2.
Qed.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 (nat_ordsucc 3 nat_p_3).
Qed.

Axiom three_plus_five_eq_eight : 3 + 5 = 8.

Theorem vertex_degree_from_complement : forall v :e 9,
  forall N M: set,
    N c= 9 -> M c= 9 ->
    (forall x :e 9, x <> v -> (x :e N \/ x :e M)) ->
    (forall x :e N, x <> v) ->
    (forall x :e M, x <> v) ->
    (N :/\: M = Empty) ->
    equip 3 N -> equip 5 M ->
    equip 8 (N :\/: M).
let v. assume Hv: v :e 9.
let N M.
assume HN9: N c= 9.
assume HM9: M c= 9.
assume Hpartition: forall x :e 9, x <> v -> (x :e N \/ x :e M).
assume HNv: forall x :e N, x <> v.
assume HMv: forall x :e M, x <> v.
assume Hdisjoint: N :/\: M = Empty.
assume HN3: equip 3 N.
assume HM5: equip 5 M.
prove equip 8 (N :\/: M).
claim Hd: forall x, x :e N -> x /:e M.
  let x. assume Hx: x :e N.
  prove x /:e M.
  assume HxM: x :e M.
  claim H1: x :e N :/\: M.
    exact binintersectI N M x Hx HxM.
  claim H2: x :e Empty.
    rewrite <- Hdisjoint.
    exact H1.
  exact EmptyE x H2.
rewrite <- three_plus_five_eq_eight.
exact disjoint_union_card 3 nat_p_3 5 N M nat_p_5 HN3 HM5 Hd.
Qed.

Theorem degree_lower_from_r33_6 : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 9 R ->
  TwoRamseyProp 3 3 6 ->
  forall v :e 9, forall N M:set,
    N c= 9 -> M c= 9 ->
    (forall x :e N, R v x /\ x <> v) ->
    (forall x :e M, ~R v x /\ x <> v) ->
    equip 3 N -> equip 6 M -> False.
Admitted.

Definition is_3_regular : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    forall v :e V, exists N:set, N c= V /\ equip 3 N /\
      (forall x :e N, R v x /\ x <> v) /\
      (forall x :e V, x <> v -> R v x -> x :e N).

Theorem no_3_regular_9 : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  is_3_regular 9 R ->
  False.
Admitted.

Theorem force_3_regularity : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 9 R ->
  TwoRamseyProp 3 3 6 ->
  no_k_indep 9 R 4 ->
  is_3_regular 9 R.
Admitted.

Theorem ramsey_34_from_regularity : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 9 R ->
  TwoRamseyProp 3 3 6 ->
  no_k_indep 9 R 4 ->
  False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 9 R.
assume Hr33: TwoRamseyProp 3 3 6.
assume Hno4: no_k_indep 9 R 4.
prove False.
claim H3reg: is_3_regular 9 R.
  { exact force_3_regularity R Hsym Htf Hr33 Hno4. }
exact no_3_regular_9 R Hsym H3reg.
Qed.

Theorem TwoRamseyProp_3_4_9 : TwoRamseyProp 3 4 9.
Admitted.
