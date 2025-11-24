Definition TwoRamseyProp : set -> set -> set -> prop
 := fun M N V =>
      forall R:set -> set -> prop,
        (forall x y, R x y -> R y x)
       -> ((exists X c= V, equip M X /\ (forall x y :e X, x <> y -> R x y))
        \/ (exists Y c= V, equip N Y /\ (forall x y :e Y, x <> y -> ~R x y))).

Definition is_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => (forall x y, R x y -> R y x) /\ (forall x :e V, ~R x x).

Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x y z :e V, R x y -> R y z -> R x z -> False.

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => ~exists S c= V, equip k S /\ (forall x y :e S, x <> y -> ~R x y).

Definition neighbors : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => {u :e V | R v u}.

Definition common_neighbors : set -> (set -> set -> prop) -> set -> set -> set :=
  fun V R u v => neighbors V R u :/\: neighbors V R v.

Definition degree : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R v d => equip d (neighbors V R v).

Definition k_regular : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall v :e V, degree V R v k.

Definition Adj17 : set -> set -> prop :=
  fun i j =>
    (i = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16)) \/
    (i = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16)) \/
    (i = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15)) \/
    (i = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16)) \/
    (i = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16)) \/
    (i = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13)) \/
    (i = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14)) \/
    (i = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15)) \/
    (i = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14)) \/
    (i = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12)) \/
    (i = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16)) \/
    (i = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15)) \/
    (i = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13)) \/
    (i = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14)) \/
    (i = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13)) \/
    (i = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11)) \/
    (i = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10)).

Theorem Adj17_sym : forall i j, Adj17 i j -> Adj17 j i.
Admitted.

Theorem Adj17_triangle_free : triangle_free 17 Adj17.
Admitted.

Theorem Adj17_no_6_indep : no_k_indep 17 Adj17 6.
Admitted.

Theorem lower_bound : ~TwoRamseyProp 3 6 17.
Admitted.

Theorem claim1_degree_le_5 :
  forall R:set->set->prop,
  is_graph 18 R ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall d, degree 18 R v d -> d c= 5.
Admitted.

Theorem claim1_degree_ge_5 :
  forall R:set->set->prop,
  is_graph 18 R ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall d, degree 18 R v d -> 5 c= d.
Admitted.

Theorem claim1 :
  forall R:set->set->prop,
  is_graph 18 R ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  k_regular 18 R 5.
Admitted.

Theorem claim2 :
  forall R:set->set->prop,
  is_graph 18 R ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  k_regular 18 R 5 ->
  forall v :e 18,
  exists P Q : set,
    P c= 18 /\ Q c= 18 /\
    equip 4 P /\ equip 8 Q /\
    P :/\: Q = Empty /\
    (forall p :e P, ~R v p /\ equip 1 (common_neighbors 18 R v p)) /\
    (forall q :e Q, ~R v q /\ equip 2 (common_neighbors 18 R v q)).
Admitted.

Theorem claim3 :
  forall R:set->set->prop,
  is_graph 18 R ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  k_regular 18 R 5 ->
  forall v :e 18, forall P : set,
    P c= 18 ->
    equip 4 P ->
    (forall p :e P, ~R v p /\ equip 1 (common_neighbors 18 R v p)) ->
    exists p1 p2 p3 p4 :e P,
      R p1 p2 /\ R p2 p3 /\ R p3 p4 /\ R p4 p1 /\
      ~R p1 p3 /\ ~R p2 p4.
Admitted.

Theorem final_contradiction :
  forall R:set->set->prop,
  is_graph 18 R ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  False.
Admitted.

Theorem upper_bound : TwoRamseyProp 3 6 18.
Admitted.

Theorem Ramsey_3_6_eq_18 :
  TwoRamseyProp 3 6 18 /\ ~TwoRamseyProp 3 6 17.
apply andI.
- exact upper_bound.
- exact lower_bound.
Qed.
