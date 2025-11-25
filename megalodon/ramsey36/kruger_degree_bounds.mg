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

Theorem TwoRamseyProp_3_5_14 : TwoRamseyProp 3 5 14.
Admitted.

Theorem nat_p_4 : nat_p 4.
exact nat_ordsucc 3 (nat_ordsucc 2 nat_2).
Qed.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 nat_p_4.
Qed.

Theorem nat_p_6 : nat_p 6.
exact nat_ordsucc 5 nat_p_5.
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 (nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8
      (nat_ordsucc 7 (nat_ordsucc 6 nat_p_6)))))).
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

Theorem degree_upper_bound_6 : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall N, N c= 18 -> equip 6 N ->
    (forall x :e N, R v x /\ x <> v) -> False.
prove forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall N, N c= 18 -> equip 6 N ->
    (forall x :e N, R v x /\ x <> v) -> False.
let R.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
let v. assume Hv: v :e 18.
let N. assume HN18: N c= 18. assume HN6: equip 6 N.
assume HNadj: forall x :e N, R v x /\ x <> v.
apply Hno6 N HN18 HN6.
prove is_indep_set 18 R N.
prove N c= 18 /\ (forall x :e N, forall y :e N, x <> y -> ~R x y).
apply andI.
- exact HN18.
- let x. assume Hx: x :e N.
  let y. assume Hy: y :e N.
  assume Hneq: x <> y.
  assume HRxy: R x y.
  claim HRvx: R v x. exact andEL (R v x) (x <> v) (HNadj x Hx).
  claim HRvy: R v y. exact andEL (R v y) (y <> v) (HNadj y Hy).
  apply Htf x (HN18 x Hx) y (HN18 y Hy) v Hv.
  + exact HRxy.
  + exact Hsym v y HRvy.
  + exact Hsym v x HRvx.
Qed.

Theorem four_in_five : 4 :e 5.
exact ordsuccI2 4.
Qed.

Theorem four_subset_five : 4 c= 5.
let x. assume Hx: x :e 4.
exact nat_trans 5 nat_p_5 4 four_in_five x Hx.
Qed.

Theorem degree_lower_bound_4_kruger : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18,
    exists N:set, N c= 18 /\
      (forall x :e N, R v x /\ x <> v) /\
      (forall x :e 18, x <> v -> R v x -> x :e N) /\
      (exists k:set, nat_p k /\ 4 c= k /\ equip k N).
prove forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18,
    exists N:set, N c= 18 /\
      (forall x :e N, R v x /\ x <> v) /\
      (forall x :e 18, x <> v -> R v x -> x :e N) /\
      (exists k:set, nat_p k /\ 4 c= k /\ equip k N).
Admitted.
