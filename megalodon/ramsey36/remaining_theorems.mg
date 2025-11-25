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

Theorem triangle_witness_from_neg : forall V:set, forall R:set -> set -> prop,
  (forall x :e V, ~R x x) ->
  (forall x y, R x y -> R y x) ->
  ~triangle_free V R ->
  exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
let V. let R: set -> set -> prop.
assume Hirr: forall x :e V, ~R x x.
assume Hsym: forall x y, R x y -> R y x.
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
  set S := {x, y} :\/: {z}.
  set f := fun n:set => if n = 0 then x else (if n = 1 then y else z).
  claim H00: 0 = 0.
    prove forall Q: set -> set -> prop, Q 0 0 -> Q 0 0.
    let Q. assume HQ: Q 0 0. exact HQ.
  claim H11: 1 = 1.
    prove forall Q: set -> set -> prop, Q 1 1 -> Q 1 1.
    let Q. assume HQ: Q 1 1. exact HQ.
  claim H22: 2 = 2.
    prove forall Q: set -> set -> prop, Q 2 2 -> Q 2 2.
    let Q. assume HQ: Q 2 2. exact HQ.
  claim Hf0: f 0 = x.
    prove (if 0 = 0 then x else (if 0 = 1 then y else z)) = x.
    exact If_i_1 (0 = 0) x (if 0 = 1 then y else z) H00.
  claim Hf1: f 1 = y.
    prove (if 1 = 0 then x else (if 1 = 1 then y else z)) = y.
    claim H10: 1 <> 0.
      exact neq_1_0.
    claim Hstep1: (if 1 = 0 then x else (if 1 = 1 then y else z)) = (if 1 = 1 then y else z).
      exact If_i_0 (1 = 0) x (if 1 = 1 then y else z) H10.
    claim Hstep2: (if 1 = 1 then y else z) = y.
      exact If_i_1 (1 = 1) y z H11.
    exact eq_i_tra (if 1 = 0 then x else (if 1 = 1 then y else z)) (if 1 = 1 then y else z) y Hstep1 Hstep2.
  claim Hf2: f 2 = z.
    prove (if 2 = 0 then x else (if 2 = 1 then y else z)) = z.
    claim H20: 2 <> 0.
      exact neq_2_0.
    claim H21: 2 <> 1.
      exact neq_2_1.
    claim Hstep1: (if 2 = 0 then x else (if 2 = 1 then y else z)) = (if 2 = 1 then y else z).
      exact If_i_0 (2 = 0) x (if 2 = 1 then y else z) H20.
    claim Hstep2: (if 2 = 1 then y else z) = z.
      exact If_i_0 (2 = 1) y z H21.
    exact eq_i_tra (if 2 = 0 then x else (if 2 = 1 then y else z)) (if 2 = 1 then y else z) z Hstep1 Hstep2.
  claim HxS: x :e S.
    apply binunionI1 {x, y} {z} x.
    exact UPairI1 x y.
  claim Hf0S: f 0 :e S.
    exact Hf0 (fun a b => b :e S) HxS.
  claim HyS: y :e S.
    apply binunionI1 {x, y} {z} y.
    exact UPairI2 x y.
  claim Hf1S: f 1 :e S.
    exact Hf1 (fun a b => b :e S) HyS.
  claim HzS: z :e S.
    apply binunionI2 {x, y} {z} z.
    exact SingI z.
  claim Hf2S: f 2 :e S.
    exact Hf2 (fun a b => b :e S) HzS.
  prove exists g : set -> set, bij 3 S g.
  witness f.
  prove bij 3 S f.
  apply and3I (forall u :e 3, f u :e S) (forall u v :e 3, f u = f v -> u = v) (forall w :e S, exists u :e 3, f u = w).
  + prove forall u :e 3, f u :e S.
    let u. assume Hu: u :e 3.
    exact cases_3 u Hu (fun i => f i :e S) Hf0S Hf1S Hf2S.
  + prove forall u v :e 3, f u = f v -> u = v.
    let u. assume Hu: u :e 3.
    let v. assume Hv: v :e 3.
    assume Hfuv: f u = f v.
    prove u = v.
    claim Hcase0: f 0 = f v -> 0 = v.
      assume H0v: f 0 = f v.
      claim Hcase00: f 0 = f 0 -> 0 = 0.
        assume HH. exact H00.
      claim Hcase01: f 0 = f 1 -> 0 = 1.
        assume H01: f 0 = f 1.
        prove False.
        claim Hx_eq_y: x = y.
          claim H1: f 0 = x. exact Hf0.
          claim H2: f 1 = y. exact Hf1.
          claim H3: x = f 0. prove forall Q: set -> set -> prop, Q x (f 0) -> Q (f 0) x. let Q. assume HQ. exact H1 (fun a b => Q b a) HQ.
          claim H4: f 0 = y. exact eq_i_tra (f 0) (f 1) y H01 H2.
          exact eq_i_tra x (f 0) y H3 H4.
        exact Hxy Hx_eq_y.
      claim Hcase02: f 0 = f 2 -> 0 = 2.
        assume H02: f 0 = f 2.
        prove False.
        claim Hx_eq_z: x = z.
          claim H1: f 0 = x. exact Hf0.
          claim H2: f 2 = z. exact Hf2.
          claim H3: x = f 0. prove forall Q: set -> set -> prop, Q x (f 0) -> Q (f 0) x. let Q. assume HQ. exact H1 (fun a b => Q b a) HQ.
          claim H4: f 0 = z. exact eq_i_tra (f 0) (f 2) z H02 H2.
          exact eq_i_tra x (f 0) z H3 H4.
        exact Hxz Hx_eq_z.
      exact cases_3 v Hv (fun j => f 0 = f j -> 0 = j) Hcase00 Hcase01 Hcase02 H0v.
    claim Hcase1: f 1 = f v -> 1 = v.
      assume H1v: f 1 = f v.
      claim Hcase10: f 1 = f 0 -> 1 = 0.
        assume H10: f 1 = f 0.
        prove False.
        claim Hy_eq_x: y = x.
          claim H1: f 1 = y. exact Hf1.
          claim H2: f 0 = x. exact Hf0.
          claim H3: y = f 1. prove forall Q: set -> set -> prop, Q y (f 1) -> Q (f 1) y. let Q. assume HQ. exact H1 (fun a b => Q b a) HQ.
          claim H4: f 1 = x. exact eq_i_tra (f 1) (f 0) x H10 H2.
          exact eq_i_tra y (f 1) x H3 H4.
        claim Hx_eq_y: x = y.
          prove forall Q: set -> set -> prop, Q x y -> Q y x. let Q. assume HQ. exact Hy_eq_x (fun a b => Q b a) HQ.
        exact Hxy Hx_eq_y.
      claim Hcase11: f 1 = f 1 -> 1 = 1.
        assume HH. exact H11.
      claim Hcase12: f 1 = f 2 -> 1 = 2.
        assume H12: f 1 = f 2.
        prove False.
        claim Hy_eq_z: y = z.
          claim H1: f 1 = y. exact Hf1.
          claim H2: f 2 = z. exact Hf2.
          claim H3: y = f 1. prove forall Q: set -> set -> prop, Q y (f 1) -> Q (f 1) y. let Q. assume HQ. exact H1 (fun a b => Q b a) HQ.
          claim H4: f 1 = z. exact eq_i_tra (f 1) (f 2) z H12 H2.
          exact eq_i_tra y (f 1) z H3 H4.
        exact Hyz Hy_eq_z.
      exact cases_3 v Hv (fun j => f 1 = f j -> 1 = j) Hcase10 Hcase11 Hcase12 H1v.
    claim Hcase2: f 2 = f v -> 2 = v.
      assume H2v: f 2 = f v.
      claim Hcase20: f 2 = f 0 -> 2 = 0.
        assume H20: f 2 = f 0.
        prove False.
        claim Hz_eq_x: z = x.
          claim H1: f 2 = z. exact Hf2.
          claim H2: f 0 = x. exact Hf0.
          claim H3: z = f 2. prove forall Q: set -> set -> prop, Q z (f 2) -> Q (f 2) z. let Q. assume HQ. exact H1 (fun a b => Q b a) HQ.
          claim H4: f 2 = x. exact eq_i_tra (f 2) (f 0) x H20 H2.
          exact eq_i_tra z (f 2) x H3 H4.
        claim Hx_eq_z: x = z.
          prove forall Q: set -> set -> prop, Q x z -> Q z x. let Q. assume HQ. exact Hz_eq_x (fun a b => Q b a) HQ.
        exact Hxz Hx_eq_z.
      claim Hcase21: f 2 = f 1 -> 2 = 1.
        assume H21: f 2 = f 1.
        prove False.
        claim Hz_eq_y: z = y.
          claim H1: f 2 = z. exact Hf2.
          claim H2: f 1 = y. exact Hf1.
          claim H3: z = f 2. prove forall Q: set -> set -> prop, Q z (f 2) -> Q (f 2) z. let Q. assume HQ. exact H1 (fun a b => Q b a) HQ.
          claim H4: f 2 = y. exact eq_i_tra (f 2) (f 1) y H21 H2.
          exact eq_i_tra z (f 2) y H3 H4.
        claim Hy_eq_z: y = z.
          prove forall Q: set -> set -> prop, Q y z -> Q z y. let Q. assume HQ. exact Hz_eq_y (fun a b => Q b a) HQ.
        exact Hyz Hy_eq_z.
      claim Hcase22: f 2 = f 2 -> 2 = 2.
        assume HH. exact H22.
      exact cases_3 v Hv (fun j => f 2 = f j -> 2 = j) Hcase20 Hcase21 Hcase22 H2v.
    exact cases_3 u Hu (fun i => f i = f v -> i = v) Hcase0 Hcase1 Hcase2 Hfuv.
  + prove forall w :e S, exists u :e 3, f u = w.
    let w. assume Hw: w :e S.
    prove exists u :e 3, f u = w.
    claim Hcasex: w = x -> exists u :e 3, f u = w.
      assume Hwx: w = x.
      witness 0.
      claim Hxw: x = w. prove forall Q: set -> set -> prop, Q x w -> Q w x. let Q. assume HQ. exact Hwx (fun a b => Q b a) HQ.
      claim Hf0w: f 0 = w. exact eq_i_tra (f 0) x w Hf0 Hxw.
      exact andI (0 :e 3) (f 0 = w) In_0_3 Hf0w.
    claim Hcasey: w = y -> exists u :e 3, f u = w.
      assume Hwy: w = y.
      witness 1.
      claim Hyw: y = w. prove forall Q: set -> set -> prop, Q y w -> Q w y. let Q. assume HQ. exact Hwy (fun a b => Q b a) HQ.
      claim Hf1w: f 1 = w. exact eq_i_tra (f 1) y w Hf1 Hyw.
      exact andI (1 :e 3) (f 1 = w) In_1_3 Hf1w.
    claim Hcasez: w = z -> exists u :e 3, f u = w.
      assume Hwz: w = z.
      witness 2.
      claim Hzw: z = w. prove forall Q: set -> set -> prop, Q z w -> Q w z. let Q. assume HQ. exact Hwz (fun a b => Q b a) HQ.
      claim Hf2w: f 2 = w. exact eq_i_tra (f 2) z w Hf2 Hzw.
      exact andI (2 :e 3) (f 2 = w) In_2_3 Hf2w.
    apply binunionE {x, y} {z} w Hw.
    * assume Hwxy: w :e {x, y}.
      apply UPairE w x y Hwxy.
      - exact Hcasex.
      - exact Hcasey.
    * assume Hwz: w :e {z}.
      claim Hwz2: w = z. exact SingE z w Hwz.
      exact Hcasez Hwz2.
- prove forall a :e {x, y} :\/: {z}, forall b :e {x, y} :\/: {z}, a <> b -> R a b.
  let a. assume Ha: a :e {x, y} :\/: {z}.
  let b. assume Hb: b :e {x, y} :\/: {z}.
  assume Hab: a <> b.
  prove R a b.
  claim Ryx: R y x. exact Hsym x y Rxy.
  claim Rzy: R z y. exact Hsym y z Ryz.
  claim Rzx: R z x. exact Hsym x z Rxz.
  claim Hxx: x = x. prove forall Q: set -> set -> prop, Q x x -> Q x x. let Q. assume HQ. exact HQ.
  claim Hyy: y = y. prove forall Q: set -> set -> prop, Q y y -> Q y y. let Q. assume HQ. exact HQ.
  claim Hzz: z = z. prove forall Q: set -> set -> prop, Q z z -> Q z z. let Q. assume HQ. exact HQ.
  claim Hcase_x_x: a = x -> b = x -> R a b.
    assume Hax: a = x. assume Hbx: b = x.
    prove False.
    claim Hab2: x <> x.
      claim H4: x <> b. exact Hax (fun u v => u <> b) Hab.
      claim H6: x = b. prove forall Q: set -> set -> prop, Q x b -> Q b x. let Q. assume HQ. exact Hbx (fun u v => Q v u) HQ.
      exact H6 (fun u v => x <> v) H4.
    exact Hab2 Hxx.
  claim Hcase_x_y: a = x -> b = y -> R a b.
    assume Hax: a = x. assume Hby: b = y.
    claim Hxa: x = a. prove forall Q: set -> set -> prop, Q x a -> Q a x. let Q. assume HQ. exact Hax (fun u v => Q v u) HQ.
    claim Hyb: y = b. prove forall Q: set -> set -> prop, Q y b -> Q b y. let Q. assume HQ. exact Hby (fun u v => Q v u) HQ.
    claim Rxb: R x b. exact Hyb (fun u v => R x u) Rxy.
    exact Hxa (fun u v => R u b) Rxb.
  claim Hcase_x_z: a = x -> b = z -> R a b.
    assume Hax: a = x. assume Hbz: b = z.
    claim Hxa: x = a. prove forall Q: set -> set -> prop, Q x a -> Q a x. let Q. assume HQ. exact Hax (fun u v => Q v u) HQ.
    claim Hzb: z = b. prove forall Q: set -> set -> prop, Q z b -> Q b z. let Q. assume HQ. exact Hbz (fun u v => Q v u) HQ.
    claim Rxb: R x b. exact Hzb (fun u v => R x u) Rxz.
    exact Hxa (fun u v => R u b) Rxb.
  claim Hcase_y_x: a = y -> b = x -> R a b.
    assume Hay: a = y. assume Hbx: b = x.
    claim Hya: y = a. prove forall Q: set -> set -> prop, Q y a -> Q a y. let Q. assume HQ. exact Hay (fun u v => Q v u) HQ.
    claim Hxb: x = b. prove forall Q: set -> set -> prop, Q x b -> Q b x. let Q. assume HQ. exact Hbx (fun u v => Q v u) HQ.
    claim Ryb: R y b. exact Hxb (fun u v => R y u) Ryx.
    exact Hya (fun u v => R u b) Ryb.
  claim Hcase_y_y: a = y -> b = y -> R a b.
    assume Hay: a = y. assume Hby: b = y.
    prove False.
    claim Hab2: y <> y.
      claim H4: y <> b. exact Hay (fun u v => u <> b) Hab.
      claim H6: y = b. prove forall Q: set -> set -> prop, Q y b -> Q b y. let Q. assume HQ. exact Hby (fun u v => Q v u) HQ.
      exact H6 (fun u v => y <> v) H4.
    exact Hab2 Hyy.
  claim Hcase_y_z: a = y -> b = z -> R a b.
    assume Hay: a = y. assume Hbz: b = z.
    claim Hya: y = a. prove forall Q: set -> set -> prop, Q y a -> Q a y. let Q. assume HQ. exact Hay (fun u v => Q v u) HQ.
    claim Hzb: z = b. prove forall Q: set -> set -> prop, Q z b -> Q b z. let Q. assume HQ. exact Hbz (fun u v => Q v u) HQ.
    claim Ryb: R y b. exact Hzb (fun u v => R y u) Ryz.
    exact Hya (fun u v => R u b) Ryb.
  claim Hcase_z_x: a = z -> b = x -> R a b.
    assume Haz: a = z. assume Hbx: b = x.
    claim Hza: z = a. prove forall Q: set -> set -> prop, Q z a -> Q a z. let Q. assume HQ. exact Haz (fun u v => Q v u) HQ.
    claim Hxb: x = b. prove forall Q: set -> set -> prop, Q x b -> Q b x. let Q. assume HQ. exact Hbx (fun u v => Q v u) HQ.
    claim Rzb: R z b. exact Hxb (fun u v => R z u) Rzx.
    exact Hza (fun u v => R u b) Rzb.
  claim Hcase_z_y: a = z -> b = y -> R a b.
    assume Haz: a = z. assume Hby: b = y.
    claim Hza: z = a. prove forall Q: set -> set -> prop, Q z a -> Q a z. let Q. assume HQ. exact Haz (fun u v => Q v u) HQ.
    claim Hyb: y = b. prove forall Q: set -> set -> prop, Q y b -> Q b y. let Q. assume HQ. exact Hby (fun u v => Q v u) HQ.
    claim Rzb: R z b. exact Hyb (fun u v => R z u) Rzy.
    exact Hza (fun u v => R u b) Rzb.
  claim Hcase_z_z: a = z -> b = z -> R a b.
    assume Haz: a = z. assume Hbz: b = z.
    prove False.
    claim Hab2: z <> z.
      claim H4: z <> b. exact Haz (fun u v => u <> b) Hab.
      claim H6: z = b. prove forall Q: set -> set -> prop, Q z b -> Q b z. let Q. assume HQ. exact Hbz (fun u v => Q v u) HQ.
      exact H6 (fun u v => z <> v) H4.
    exact Hab2 Hzz.
  claim Hcase_a_x: a = x -> R a b.
    assume Hax: a = x.
    claim Hbx_case: b = x -> R a b. exact Hcase_x_x Hax.
    claim Hby_case: b = y -> R a b. exact Hcase_x_y Hax.
    claim Hbz_case: b = z -> R a b. exact Hcase_x_z Hax.
    claim Hbxy_case: b :e {x, y} -> R a b.
      assume Hbxy: b :e {x, y}.
      exact UPairE b x y Hbxy (R a b) Hbx_case Hby_case.
    claim Hbsz_case: b :e {z} -> R a b.
      assume Hbz: b :e {z}.
      exact Hbz_case (SingE z b Hbz).
    exact binunionE {x, y} {z} b Hb (R a b) Hbxy_case Hbsz_case.
  claim Hcase_a_y: a = y -> R a b.
    assume Hay: a = y.
    claim Hbx_case: b = x -> R a b. exact Hcase_y_x Hay.
    claim Hby_case: b = y -> R a b. exact Hcase_y_y Hay.
    claim Hbz_case: b = z -> R a b. exact Hcase_y_z Hay.
    claim Hbxy_case: b :e {x, y} -> R a b.
      assume Hbxy: b :e {x, y}.
      exact UPairE b x y Hbxy (R a b) Hbx_case Hby_case.
    claim Hbsz_case: b :e {z} -> R a b.
      assume Hbz: b :e {z}.
      exact Hbz_case (SingE z b Hbz).
    exact binunionE {x, y} {z} b Hb (R a b) Hbxy_case Hbsz_case.
  claim Hcase_a_z: a = z -> R a b.
    assume Haz: a = z.
    claim Hbx_case: b = x -> R a b. exact Hcase_z_x Haz.
    claim Hby_case: b = y -> R a b. exact Hcase_z_y Haz.
    claim Hbz_case: b = z -> R a b. exact Hcase_z_z Haz.
    claim Hbxy_case: b :e {x, y} -> R a b.
      assume Hbxy: b :e {x, y}.
      exact UPairE b x y Hbxy (R a b) Hbx_case Hby_case.
    claim Hbsz_case: b :e {z} -> R a b.
      assume Hbz: b :e {z}.
      exact Hbz_case (SingE z b Hbz).
    exact binunionE {x, y} {z} b Hb (R a b) Hbxy_case Hbsz_case.
  claim Haxy_case: a :e {x, y} -> R a b.
    assume Haxy: a :e {x, y}.
    exact UPairE a x y Haxy (R a b) Hcase_a_x Hcase_a_y.
  claim Hasz_case: a :e {z} -> R a b.
    assume Haz: a :e {z}.
    exact Hcase_a_z (SingE z a Haz).
  exact binunionE {x, y} {z} a Ha (R a b) Haxy_case Hasz_case.
Qed.

Theorem indep_witness_from_neg : forall V:set, forall R:set -> set -> prop, forall k:set,
  ~no_k_indep V R k ->
  exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
let V. let R: set -> set -> prop. let k.
assume Hnot: ~no_k_indep V R k.
prove exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
apply dneg (exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
assume Hcontra: ~(exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
apply Hnot.
prove no_k_indep V R k.
prove forall S, S c= V -> equip k S -> ~is_indep_set V R S.
let S. assume HSV: S c= V. assume HSeq: equip k S.
assume Hindep: is_indep_set V R S.
apply Hcontra.
witness S.
apply and3I (S c= V) (equip k S) (forall x :e S, forall y :e S, x <> y -> ~R x y).
- exact HSV.
- exact HSeq.
- prove forall x :e S, forall y :e S, x <> y -> ~R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) Hindep.
Qed.

Theorem good_graph_contradiction : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) -> triangle_free 18 R -> no_k_indep 18 R 6 -> False.
aby.
Qed.
