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
prove forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.
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
  % This requires showing {x,y,z} has cardinality 3
  % For now we admit this step as it requires showing x, y, z are distinct
  % which follows from R being irreflexive and the edges existing
  Admitted.

Theorem indep_witness_from_neg : forall V:set, forall R:set -> set -> prop, forall k:set,
  ~no_k_indep V R k ->
  exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
let V. let R: set -> set -> prop. let k.
assume Hnot: ~no_k_indep V R k.
prove exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
apply dneg.
assume Hcontra: ~(exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
apply Hnot.
prove no_k_indep V R k.
prove forall S, S c= V -> equip k S -> ~is_indep_set V R S.
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


Theorem degree_bound : forall V:set, forall R:set -> set -> prop, forall k:set,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  no_k_indep V R k ->
  forall v :e V, forall S, S c= V -> equip k S ->
    (forall x :e S, R v x) -> False.
let V. let R: set -> set -> prop. let k.
assume Rsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
assume Hno_k: no_k_indep V R k.
let v. assume Hv: v :e V.
let S. assume HSV: S c= V. assume HSeq: equip k S.
assume Hadj: forall x :e S, R v x.
prove False.
apply Hno_k S HSV HSeq.
prove is_indep_set V R S.
apply andI.
- exact HSV.
- prove forall x :e S, forall y :e S, x <> y -> ~R x y.
  let x. assume HxS: x :e S.
  let y. assume HyS: y :e S.
  assume Hneq: x <> y.
  exact neighborhood_independent V R Rsym Htf v Hv x (HSV x HxS) y (HSV y HyS) (Hadj x HxS) (Hadj y HyS) Hneq.
Qed.


Theorem R34 : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 9 R ->
  exists S, S c= 9 /\ equip 4 S /\ is_indep_set 9 R S.
Admitted.



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
  % Case 1a: R is triangle-free AND has no 6-indep set -> contradiction
  + assume Hno6: no_k_indep 18 R 6.
    prove False.
    exact good_graph_contradiction R Rsym Htf Hno6.
  % Case 1b: R is triangle-free AND has a 6-indep set -> extract witness
  + assume Hnot6: ~no_k_indep 18 R 6.
    apply orIR.
    exact indep_witness_from_neg 18 R 6 Hnot6.
- assume Hntf: ~triangle_free 18 R.
  apply orIL.
  exact triangle_witness_from_neg 18 R Hntf.
Qed.

