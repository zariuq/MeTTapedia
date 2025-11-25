Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Theorem five_regularity : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, exists N:set, N c= 18 /\ equip 5 N /\
    (forall x :e N, R v x /\ x <> v) /\
    (forall x :e 18, x <> v -> R v x -> x :e N).
Admitted.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)).
Qed.

Theorem nat_p_10 : nat_p 10.
exact nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5 nat_p_5)))).
Qed.

Theorem neighborhood_intersection_lower : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall u v :e 18, u <> v -> ~R u v ->
  exists c :e 18, R u c /\ R v c /\ c <> u /\ c <> v.
prove forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall u v :e 18, u <> v -> ~R u v ->
  exists c :e 18, R u c /\ R v c /\ c <> u /\ c <> v.
let R.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
let u. assume Hu: u :e 18.
let v. assume Hv: v :e 18.
assume Huv: u <> v.
assume HnR: ~R u v.
prove exists c :e 18, R u c /\ R v c /\ c <> u /\ c <> v.
Admitted.
