Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Theorem no_k_indep_no_indep_set : forall V:set, forall R:set -> set -> prop, forall k:set,
  no_k_indep V R k ->
  ~(exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
let V. let R: set -> set -> prop. let k.
assume Hno: no_k_indep V R k.
assume Hex: exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
prove False.
apply Hex.
let Y.
assume HY: Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
claim HYsub: Y c= V.
  apply and3E (Y c= V) (equip k Y) (forall x :e Y, forall y :e Y, x <> y -> ~R x y) HY.
  assume H1: Y c= V.
  assume H2: equip k Y.
  assume H3: forall x :e Y, forall y :e Y, x <> y -> ~R x y.
  exact H1.
claim HYequip: equip k Y.
  apply and3E (Y c= V) (equip k Y) (forall x :e Y, forall y :e Y, x <> y -> ~R x y) HY.
  assume H1: Y c= V.
  assume H2: equip k Y.
  assume H3: forall x :e Y, forall y :e Y, x <> y -> ~R x y.
  exact H2.
claim HYindep: forall x :e Y, forall y :e Y, x <> y -> ~R x y.
  apply and3E (Y c= V) (equip k Y) (forall x :e Y, forall y :e Y, x <> y -> ~R x y) HY.
  assume H1: Y c= V.
  assume H2: equip k Y.
  assume H3: forall x :e Y, forall y :e Y, x <> y -> ~R x y.
  exact H3.
claim HYis: is_indep_set V R Y.
  prove Y c= V /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
  exact andI (Y c= V) (forall x :e Y, forall y :e Y, x <> y -> ~R x y) HYsub HYindep.
claim Hnot: ~is_indep_set V R Y.
  exact Hno Y HYsub HYequip.
exact Hnot HYis.
Qed.

Theorem triangle_free_no_3clique : forall V:set, forall R:set -> set -> prop,
  triangle_free V R ->
  ~(exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y)).
let V. let R: set -> set -> prop.
assume Htf: triangle_free V R.
assume H: exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
prove False.
apply H.
let X.
assume HX: X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
claim HXV: X c= V.
  apply and3E (X c= V) (equip 3 X) (forall x :e X, forall y :e X, x <> y -> R x y) HX.
  assume H1: X c= V. assume H2: equip 3 X. assume H3: forall x :e X, forall y :e X, x <> y -> R x y.
  exact H1.
claim HXeq: equip 3 X.
  apply and3E (X c= V) (equip 3 X) (forall x :e X, forall y :e X, x <> y -> R x y) HX.
  assume H1: X c= V. assume H2: equip 3 X. assume H3: forall x :e X, forall y :e X, x <> y -> R x y.
  exact H2.
claim HXclique: forall x :e X, forall y :e X, x <> y -> R x y.
  apply and3E (X c= V) (equip 3 X) (forall x :e X, forall y :e X, x <> y -> R x y) HX.
  assume H1: X c= V. assume H2: equip 3 X. assume H3: forall x :e X, forall y :e X, x <> y -> R x y.
  exact H3.
apply equip_bij 3 X HXeq.
let f: set -> set.
assume Hbij: bij 3 X f.
claim HfX: forall u :e 3, f u :e X.
  apply and3E (forall u :e 3, f u :e X) (forall u v :e 3, f u = f v -> u = v) (forall w :e X, exists u :e 3, f u = w) Hbij.
  assume H1: forall u :e 3, f u :e X. assume H2: forall u v :e 3, f u = f v -> u = v. assume H3: forall w :e X, exists u :e 3, f u = w.
  exact H1.
claim Hinj: forall u v :e 3, f u = f v -> u = v.
  apply and3E (forall u :e 3, f u :e X) (forall u v :e 3, f u = f v -> u = v) (forall w :e X, exists u :e 3, f u = w) Hbij.
  assume H1: forall u :e 3, f u :e X. assume H2: forall u v :e 3, f u = f v -> u = v. assume H3: forall w :e X, exists u :e 3, f u = w.
  exact H2.
claim Ha: f 0 :e X.
  exact HfX 0 In_0_3.
claim Hb: f 1 :e X.
  exact HfX 1 In_1_3.
claim Hc: f 2 :e X.
  exact HfX 2 In_2_3.
claim HaV: f 0 :e V.
  exact HXV (f 0) Ha.
claim HbV: f 1 :e V.
  exact HXV (f 1) Hb.
claim HcV: f 2 :e V.
  exact HXV (f 2) Hc.
claim Hab: f 0 <> f 1.
  assume Heq: f 0 = f 1.
  claim H01: 0 = 1.
    exact Hinj 0 In_0_3 1 In_1_3 Heq.
  exact neq_0_1 H01.
claim Hbc: f 1 <> f 2.
  assume Heq: f 1 = f 2.
  claim H12: 1 = 2.
    exact Hinj 1 In_1_3 2 In_2_3 Heq.
  exact neq_1_2 H12.
claim Hac: f 0 <> f 2.
  assume Heq: f 0 = f 2.
  claim H02: 0 = 2.
    exact Hinj 0 In_0_3 2 In_2_3 Heq.
  exact neq_0_2 H02.
claim Rab: R (f 0) (f 1).
  exact HXclique (f 0) Ha (f 1) Hb Hab.
claim Rbc: R (f 1) (f 2).
  exact HXclique (f 1) Hb (f 2) Hc Hbc.
claim Rac: R (f 0) (f 2).
  exact HXclique (f 0) Ha (f 2) Hc Hac.
exact Htf (f 0) HaV (f 1) HbV (f 2) HcV Rab Rbc Rac.
Qed.
