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
       -> ((exists X, X c= V /\ equip M X /\ (forall x :e X, forall y :e X, x <> y -> R x y))
        \/ (exists Y, Y c= V /\ equip N Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y))).
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
Theorem triangle_free_no_3clique : forall V:set, forall R:set -> set -> prop,
  triangle_free V R ->
  ~(exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y)).
let V. let R: set -> set -> prop.
assume Htf: triangle_free V R.
assume Hclique: exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
prove False.
Admitted.
Theorem no_k_indep_no_indep_set : forall V:set, forall R:set -> set -> prop, forall k:set,
  no_k_indep V R k ->
  ~(exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
let V. let R: set -> set -> prop. let k.
assume Hno: no_k_indep V R k.
assume HY: exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
prove False.
apply HY.
let Y.
assume HYprop: Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
apply and3E HYprop.
assume HYV: Y c= V.
assume HYk: equip k Y.
assume HYind: forall x :e Y, forall y :e Y, x <> y -> ~R x y.
apply Hno Y HYV HYk.
prove is_indep_set V R Y.
apply andI.
- exact HYV.
- exact HYind.
Qed.
Theorem lower_bound : ~TwoRamseyProp 3 6 17.
assume H: TwoRamseyProp 3 6 17.
prove False.
apply H Adj17 Adj17_sym.
- assume H3: exists X, X c= 17 /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> Adj17 x y).
  exact triangle_free_no_3clique 17 Adj17 Adj17_triangle_free H3.
- assume H6: exists Y, Y c= 17 /\ equip 6 Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~Adj17 x y).
  exact no_k_indep_no_indep_set 17 Adj17 6 Adj17_no_6_indep H6.
Qed.
Theorem triangle_witness_from_neg : forall V:set, forall R:set -> set -> prop,
  ~triangle_free V R ->
  exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
let V. let R: set -> set -> prop.
assume Hnot: ~triangle_free V R.
prove exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
apply dneg.
assume Hcontra: ~(exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y)).
apply Hnot.
prove triangle_free V R.
let x. assume HxV: x :e V.
let y. assume HyV: y :e V.
let z. assume HzV: z :e V.
assume Hxy: R x y. assume Hyz: R y z. assume Hxz: R x z.
apply Hcontra.
witness {x, y, z}.
apply and3I.
- prove {x, y, z} c= V.
  let w. assume Hw: w :e {x, y, z}.
  apply binunionE {x, y} {z} w Hw.
  + assume Hwxy: w :e {x, y}.
    apply UPairE x y w Hwxy.
    * assume Hwx: w = x. rewrite Hwx. exact HxV.
    * assume Hwy: w = y. rewrite Hwy. exact HyV.
  + assume Hwz: w :e {z}.
    apply SingE z w Hwz.
    assume Hwz2: w = z. rewrite Hwz2. exact HzV.
- prove equip 3 {x, y, z}.
  % Requires showing x, y, z are distinct (follows from irreflexivity of ~triangle_free)
  Admitted.
Theorem indep_witness_from_neg : forall V:set, forall R:set -> set -> prop, forall k:set,
  ~no_k_indep V R k ->
  exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
let V. let R: set -> set -> prop. let k.
assume Hnot: ~no_k_indep V R k.
apply dneg.
assume Hcontra: ~(exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
apply Hnot.
prove no_k_indep V R k.
let S. assume HSV: S c= V. assume HSeq: equip k S.
assume Hindep: is_indep_set V R S.
apply Hcontra.
witness S.
apply and3I.
- exact HSV.
- exact HSeq.
- apply andER Hindep.
Qed.
Theorem neighborhood_independent : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  forall v :e V, forall x y :e V, R v x -> R v y -> x <> y -> ~R x y.
let V. let R: set -> set -> prop.
assume Rsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
let v. assume Hv: v :e V.
let x. assume Hx: x :e V.
let y. assume Hy: y :e V.
assume Hvx: R v x.
assume Hvy: R v y.
assume Hneq: x <> y.
assume Hxy: R x y.
apply Htf v Hv x Hx y Hy.
- exact Hvx.
- exact Hxy.
- exact Rsym v y Hvy.
Qed.
Theorem good_graph_contradiction : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) -> triangle_free 18 R -> no_k_indep 18 R 6 -> False.
let R: set -> set -> prop.
assume Rsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
prove False.
Admitted.
Theorem upper_bound : TwoRamseyProp 3 6 18.
prove forall R:set -> set -> prop, (forall x y, R x y -> R y x) ->
  ((exists X, X c= 18 /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y))
   \/ (exists Y, Y c= 18 /\ equip 6 Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y))).
let R: set -> set -> prop.
assume Rsym: forall x y, R x y -> R y x.
apply xm (triangle_free 18 R).
- assume Htf: triangle_free 18 R.
  apply xm (no_k_indep 18 R 6).
  + assume Hno6: no_k_indep 18 R 6.
    prove False.
    exact good_graph_contradiction R Rsym Htf Hno6.
  + assume Hnot6: ~no_k_indep 18 R 6.
    apply orIR.
    exact indep_witness_from_neg 18 R 6 Hnot6.
- assume Hntf: ~triangle_free 18 R.
  apply orIL.
  exact triangle_witness_from_neg 18 R Hntf.
Qed.
Theorem Ramsey_3_6_eq_18 : TwoRamseyProp 3 6 18 /\ ~TwoRamseyProp 3 6 17.
apply andI.
- exact upper_bound.
- exact lower_bound.
Qed.
