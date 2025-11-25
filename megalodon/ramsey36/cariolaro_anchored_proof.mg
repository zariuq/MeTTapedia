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

Theorem TwoRamseyProp_3_5_14 : TwoRamseyProp 3 5 14.
Admitted.

Theorem R35_critical_4regular :
  forall R:set -> set -> prop,
    (forall x y, R x y -> R y x) ->
    triangle_free 13 R ->
    no_k_indep 13 R 5 ->
    forall v :e 13,
      exists N:set,
        N c= 13 /\ equip 4 N /\
        (forall x :e N, R v x /\ x <> v) /\
        (forall x :e 13, x <> v -> R v x -> x :e N).
Admitted.

Theorem five_regularity_upper : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall N:set, N c= 18 ->
    (forall x :e N, R v x /\ x <> v) ->
    equip 6 N -> False.
prove forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall N:set, N c= 18 ->
    (forall x :e N, R v x /\ x <> v) ->
    equip 6 N -> False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
let v. assume Hv: v :e 18.
let N. assume HN18: N c= 18.
assume HNadj: forall x :e N, R v x /\ x <> v.
assume HN6: equip 6 N.
prove False.
apply Hno6 N HN18 HN6.
prove is_indep_set 18 R N.
prove N c= 18 /\ (forall x :e N, forall y :e N, x <> y -> ~R x y).
apply andI (N c= 18) (forall x :e N, forall y :e N, x <> y -> ~R x y).
- exact HN18.
- prove forall x :e N, forall y :e N, x <> y -> ~R x y.
  let x. assume Hx: x :e N.
  let y. assume Hy: y :e N.
  assume Hneq: x <> y.
  prove ~R x y.
  claim HRvx: R v x. exact andEL (R v x) (x <> v) (HNadj x Hx).
  claim HRvy: R v y. exact andEL (R v y) (y <> v) (HNadj y Hy).
  claim Hxv: x <> v. exact andER (R v x) (x <> v) (HNadj x Hx).
  claim Hyv: y <> v. exact andER (R v y) (y <> v) (HNadj y Hy).
  assume HRxy: R x y.
  apply Htf x (HN18 x Hx) y (HN18 y Hy) v Hv.
  - prove R x y. exact HRxy.
  - prove R y v. exact Hsym v y HRvy.
  - prove R x v. exact Hsym v x HRvx.
Qed.

Theorem five_regularity : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, exists N:set, N c= 18 /\ equip 5 N /\
    (forall x :e N, R v x /\ x <> v) /\
    (forall x :e 18, x <> v -> R v x -> x :e N).
prove forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, exists N:set, N c= 18 /\ equip 5 N /\
    (forall x :e N, R v x /\ x <> v) /\
    (forall x :e 18, x <> v -> R v x -> x :e N).
Admitted.

Definition neighborhood : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => {u :e V | R v u /\ u <> v}.

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
prove forall R:set -> set -> prop,
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

Theorem pq_decomposition_exists : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18,
  exists P Q:set,
    P c= 18 /\ Q c= 18 /\
    equip 4 P /\ equip 8 Q /\
    (forall p :e P, ~R v p) /\
    (forall q :e Q, ~R v q) /\
    (P :/\: Q = Empty) /\
    True.
prove forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18,
  exists P Q:set,
    P c= 18 /\ Q c= 18 /\
    equip 4 P /\ equip 8 Q /\
    (forall p :e P, ~R v p) /\
    (forall q :e Q, ~R v q) /\
    (P :/\: Q = Empty) /\
    True.
Admitted.

Theorem P_forms_4cycle : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall P:set,
    P c= 18 -> equip 4 P ->
    (forall p :e P, ~R v p) ->
    exists p1 p2 p3 p4,
      P = {p1} :\/:  {p2} :\/:  {p3} :\/:  {p4} /\
      R p1 p2 /\ R p2 p3 /\ R p3 p4 /\ R p4 p1 /\
      ~R p1 p3 /\ ~R p2 p4.
prove forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall P:set,
    P c= 18 -> equip 4 P ->
    (forall p :e P, ~R v p) ->
    exists p1 p2 p3 p4,
      P = {p1} :\/:  {p2} :\/:  {p3} :\/:  {p4} /\
      R p1 p2 /\ R p2 p3 /\ R p3 p4 /\ R p4 p1 /\
      ~R p1 p3 /\ ~R p2 p4.
Admitted.

Theorem good_graph_contradiction_anchored : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  False.
prove forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
prove False.
Admitted.

Theorem ramsey_3_6_upper_bound :
  forall R:set -> set -> prop,
    (forall x y, R x y -> R y x) ->
    triangle_free 18 R ->
    exists S:set, S c= 18 /\ equip 6 S /\ is_indep_set 18 R S.
prove forall R:set -> set -> prop,
    (forall x y, R x y -> R y x) ->
    triangle_free 18 R ->
    exists S:set, S c= 18 /\ equip 6 S /\ is_indep_set 18 R S.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
prove exists S:set, S c= 18 /\ equip 6 S /\ is_indep_set 18 R S.
Admitted.
