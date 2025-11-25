Theorem set_eq_refl : forall x:set, x = x.
let x.
prove forall Q: set -> set -> prop, Q x x -> Q x x.
let Q. assume HQ: Q x x. exact HQ.
Qed.

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

Theorem TwoRamseyProp_3_4_9 : TwoRamseyProp 3 4 9.
Admitted.

Theorem neighborhood_intersection_upper : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall u v :e 18, u <> v -> ~R u v ->
  forall c1 c2 c3 :e 18,
    R u c1 /\ R v c1 /\ c1 <> u /\ c1 <> v ->
    R u c2 /\ R v c2 /\ c2 <> u /\ c2 <> v ->
    R u c3 /\ R v c3 /\ c3 <> u /\ c3 <> v ->
    c1 <> c2 -> c1 <> c3 -> c2 <> c3 ->
    False.
Admitted.
