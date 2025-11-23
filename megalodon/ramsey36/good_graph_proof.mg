Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Theorem neighborhood_indep : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  forall v :e V, forall a b :e V, R v a -> R v b -> a <> b -> ~R a b.
let V. let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
let v. assume Hv: v :e V.
let a. assume Ha: a :e V.
let b. assume Hb: b :e V.
assume Hva: R v a.
assume Hvb: R v b.
assume Hab_neq: a <> b.
assume Hab: R a b.
prove False.
apply Htf v Hv a Ha b Hb.
- exact Hva.
- exact Hab.
- exact Hvb.
Qed.

Theorem degree_bound_6 : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  no_k_indep V R 6 ->
  forall v :e V, forall S, S c= V -> equip 6 S ->
    (forall x :e S, R v x) -> (forall x :e S, v <> x) -> False.
let V. let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
assume Hno6: no_k_indep V R 6.
let v. assume Hv: v :e V.
let S. assume HSV: S c= V. assume HS6: equip 6 S.
assume Hadj: forall x :e S, R v x.
assume Hneqv: forall x :e S, v <> x.
prove False.
apply Hno6 S HSV HS6.
prove is_indep_set V R S.
prove S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).
apply andI (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y).
- exact HSV.
- prove forall x :e S, forall y :e S, x <> y -> ~R x y.
  let x. assume HxS: x :e S.
  let y. assume HyS: y :e S.
  assume Hneq: x <> y.
  exact neighborhood_indep V R Hsym Htf v Hv x (HSV x HxS) y (HSV y HyS)
        (Hadj x HxS) (Hadj y HyS) Hneq.
Qed.

Theorem good_graph_contradiction : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) -> triangle_free 18 R -> no_k_indep 18 R 6 -> False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
prove False.
Admitted.
