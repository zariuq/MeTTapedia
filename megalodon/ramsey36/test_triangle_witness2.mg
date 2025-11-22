Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Theorem triangle_witness_from_neg : forall V:set, forall R:set -> set -> prop,
  (forall x :e V, ~R x x) ->
  ~triangle_free V R ->
  exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
let V. let R: set -> set -> prop.
assume Hirr: forall x :e V, ~R x x.
assume Hntf: ~triangle_free V R.
prove exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
apply dneg (exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y)).
assume Hno: ~(exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y)).
prove False.
apply Hntf.
prove triangle_free V R.
let x. assume HxV: x :e V.
let y. assume HyV: y :e V.
let z. assume HzV: z :e V.
assume Rxy: R x y.
assume Ryz: R y z.
assume Rxz: R x z.
prove False.
claim Hxy: x <> y.
  assume Heq: x = y.
  apply Hirr x HxV.
  prove R x x.
  claim Heqsym: y = x.
    prove forall Q: set -> set -> prop, Q y x -> Q x y.
    let Q: set -> set -> prop. assume HQ: Q y x.
    exact Heq (fun a b => Q b a) HQ.
  exact Heqsym (fun a b => R x a) Rxy.
claim Hyz: y <> z.
  assume Heq: y = z.
  apply Hirr y HyV.
  prove R y y.
  claim Heqsym: z = y.
    prove forall Q: set -> set -> prop, Q z y -> Q y z.
    let Q: set -> set -> prop. assume HQ: Q z y.
    exact Heq (fun a b => Q b a) HQ.
  exact Heqsym (fun a b => R y a) Ryz.
claim Hxz: x <> z.
  assume Heq: x = z.
  apply Hirr x HxV.
  prove R x x.
  claim Heqsym: z = x.
    prove forall Q: set -> set -> prop, Q z x -> Q x z.
    let Q: set -> set -> prop. assume HQ: Q z x.
    exact Heq (fun a b => Q b a) HQ.
  exact Heqsym (fun a b => R x a) Rxz.
apply Hno.
witness {x, y} :\/: {z}.
apply and3I ({x, y} :\/: {z} c= V) (equip 3 ({x, y} :\/: {z})) (forall a :e {x, y} :\/: {z}, forall b :e {x, y} :\/: {z}, a <> b -> R a b).
- prove {x, y} :\/: {z} c= V.
  let w. assume Hw: w :e {x, y} :\/: {z}.
  apply binunionE {x, y} {z} w Hw.
  + assume Hwxy: w :e {x, y}.
    apply UPairE w x y Hwxy.
    * assume Hwx: w = x.
      prove w :e V.
      apply Hwx (fun a b => b :e V) HxV.
    * assume Hwy: w = y.
      prove w :e V.
      apply Hwy (fun a b => b :e V) HyV.
  + assume Hwz: w :e {z}.
    claim Hwz2: w = z.
      exact SingE z w Hwz.
    prove w :e V.
    apply Hwz2 (fun a b => b :e V) HzV.
- prove equip 3 ({x, y} :\/: {z}).
  aby.
- prove forall a :e {x, y} :\/: {z}, forall b :e {x, y} :\/: {z}, a <> b -> R a b.
  aby.
Qed.
