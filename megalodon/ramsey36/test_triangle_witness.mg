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
  claim Rxx: R x x.
    prove R x x.
    claim Rxx': R x y.
      exact Rxy.
    claim HeqR: R x y = R x x.
      exact f_eq_i_i R x x y x (eq_i_ref x) Heq.
    exact eq_i_sym (R x y) (R x x) HeqR Rxx'.
  exact Hirr x HxV Rxx.
claim Hyz: y <> z.
  assume Heq: y = z.
  claim Ryy: R y y.
    prove R y y.
    claim Ryz': R y z.
      exact Ryz.
    claim HeqR: R y z = R y y.
      exact f_eq_i_i R y y z y (eq_i_ref y) Heq.
    exact eq_i_sym (R y z) (R y y) HeqR Ryz'.
  exact Hirr y HyV Ryy.
claim Hxz: x <> z.
  assume Heq: x = z.
  claim Rxx: R x x.
    prove R x x.
    claim Rxz': R x z.
      exact Rxz.
    claim HeqR: R x z = R x x.
      exact f_eq_i_i R x x z x (eq_i_ref x) Heq.
    exact eq_i_sym (R x z) (R x x) HeqR Rxz'.
  exact Hirr x HxV Rxx.
aby.
Qed.
