Theorem equip_3_triple : forall x y z: set,
  x <> y -> y <> z -> x <> z ->
  equip 3 ({x, y} :\/: {z}).
let x. let y. let z.
assume Hxy: x <> y.
assume Hyz: y <> z.
assume Hxz: x <> z.
prove equip 3 ({x, y} :\/: {z}).
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
    exact If_i_1 (1 = 1) y z (H11).
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
apply bij_equip 3 S f.
prove bij 3 S f.
apply and3I (forall u :e 3, f u :e S) (forall u v :e 3, f u = f v -> u = v) (forall w :e S, exists u :e 3, f u = w).
- prove forall u :e 3, f u :e S.
  let u. assume Hu: u :e 3.
  exact cases_3 u Hu (fun i => f i :e S) Hf0S Hf1S Hf2S.
- prove forall u v :e 3, f u = f v -> u = v.
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
- prove forall w :e S, exists u :e 3, f u = w.
  let w. assume Hw: w :e S.
  prove exists u :e 3, f u = w.
  apply binunionE {x, y} {z} w Hw.
  + assume Hwxy: w :e {x, y}.
    apply UPairE w x y Hwxy.
    * assume Hwx: w = x.
      witness 0.
      apply andI (0 :e 3) (f 0 = w).
      - exact In_0_3.
      - prove f 0 = w.
        claim Hxw: x = w. prove forall Q: set -> set -> prop, Q x w -> Q w x. let Q. assume HQ. exact Hwx (fun a b => Q b a) HQ.
        exact eq_i_tra (f 0) x w Hf0 Hxw.
    * assume Hwy: w = y.
      witness 1.
      apply andI (1 :e 3) (f 1 = w).
      - exact In_1_3.
      - prove f 1 = w.
        claim Hyw: y = w. prove forall Q: set -> set -> prop, Q y w -> Q w y. let Q. assume HQ. exact Hwy (fun a b => Q b a) HQ.
        exact eq_i_tra (f 1) y w Hf1 Hyw.
  + assume Hwz: w :e {z}.
    claim Hwz2: w = z.
      exact SingE z w Hwz.
    witness 2.
    apply andI (2 :e 3) (f 2 = w).
    - exact In_2_3.
    - prove f 2 = w.
      claim Hzw: z = w. prove forall Q: set -> set -> prop, Q z w -> Q w z. let Q. assume HQ. exact Hwz2 (fun a b => Q b a) HQ.
      exact eq_i_tra (f 2) z w Hf2 Hzw.
Qed.
