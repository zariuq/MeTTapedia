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
aby.
Qed.

Axiom R34_upper : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  equip 9 V ->
  triangle_free V R ->
  exists S, S c= V /\ equip 4 S /\ is_indep_set V R S.

Axiom extension_5_to_6 : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  forall S, S c= 18 -> equip 5 S -> is_indep_set 18 R S ->
  exists x :e 18, x /:e S /\ (forall y :e S, ~R x y).

Axiom exists_5_indep : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  exists S, S c= 18 /\ equip 5 S /\ is_indep_set 18 R S.

Axiom good_graph_final_step : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall S5, S5 c= 18 -> equip 5 S5 -> is_indep_set 18 R S5 ->
  forall x6, x6 :e 18 -> x6 /:e S5 -> (forall y :e S5, ~R x6 y) -> False.

Theorem good_graph_contradiction : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) -> triangle_free 18 R -> no_k_indep 18 R 6 -> False.
aby.
Qed.
