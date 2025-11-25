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

Theorem ramsey_3_5_le_14_kruger : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 14 R ->
  exists S:set, S c= 14 /\ equip 5 S /\ is_indep_set 14 R S.
Admitted.

Theorem four_subset_13 : 4 c= 13.
let x. assume Hx: x :e 4.
prove x :e 13.
exact nat_trans 13 nat_p_13 4
  (ordsuccI1 12 4 (ordsuccI1 11 4 (ordsuccI1 10 4 (ordsuccI1 9 4
   (ordsuccI1 8 4 (ordsuccI1 7 4 (ordsuccI1 6 4 (ordsuccI1 5 4 (ordsuccI2 4)))))))))
  x Hx.
Qed.

Theorem disjoint_union_sing_5 : forall v:set, forall S:set,
  v /:e S ->
  equip 5 S ->
  equip 6 ({v} :\/: S).
Admitted.

Theorem degree_lower_bound_4_kruger : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18,
    exists N:set, N c= 18 /\
      (forall x :e N, R v x /\ x <> v) /\
      (forall x :e 18, x <> v -> R v x -> x :e N) /\
      (exists k:set, nat_p k /\ 4 c= k /\ equip k N).
Admitted.

Theorem compiles_check : True.
exact TrueI.
Qed.
