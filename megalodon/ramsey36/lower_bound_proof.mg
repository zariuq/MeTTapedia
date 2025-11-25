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
apply HXeq.
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

Theorem lower_bound : ~TwoRamseyProp 3 6 17.
assume H: TwoRamseyProp 3 6 17.
prove False.
apply H Adj17 Adj17_sym.
- assume H3: exists X, X c= 17 /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> Adj17 x y).
  exact triangle_free_no_3clique 17 Adj17 Adj17_triangle_free H3.
- assume H6: exists Y, Y c= 17 /\ equip 6 Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~Adj17 x y).
  exact no_k_indep_no_indep_set 17 Adj17 6 Adj17_no_6_indep H6.
Qed.
