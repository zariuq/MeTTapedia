Theorem equip_4_quad : forall a b c d: set,
  a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d ->
  equip 4 (({a, b} :\/: {c}) :\/: {d}).
let a. let b. let c. let d.
assume Hab: a <> b.
assume Hac: a <> c.
assume Had: a <> d.
assume Hbc: b <> c.
assume Hbd: b <> d.
assume Hcd: c <> d.
prove equip 4 (({a, b} :\/: {c}) :\/: {d}).
set S := ({a, b} :\/: {c}) :\/: {d}.
set f := fun n:set => if n = 0 then a else (if n = 1 then b else (if n = 2 then c else d)).
claim H00: 0 = 0.
  prove forall Q: set -> set -> prop, Q 0 0 -> Q 0 0.
  let Q. assume HQ: Q 0 0. exact HQ.
claim H11: 1 = 1.
  prove forall Q: set -> set -> prop, Q 1 1 -> Q 1 1.
  let Q. assume HQ: Q 1 1. exact HQ.
claim H22: 2 = 2.
  prove forall Q: set -> set -> prop, Q 2 2 -> Q 2 2.
  let Q. assume HQ: Q 2 2. exact HQ.
claim H33: 3 = 3.
  prove forall Q: set -> set -> prop, Q 3 3 -> Q 3 3.
  let Q. assume HQ: Q 3 3. exact HQ.
claim Hf0: f 0 = a.
  prove (if 0 = 0 then a else (if 0 = 1 then b else (if 0 = 2 then c else d))) = a.
  exact If_i_1 (0 = 0) a (if 0 = 1 then b else (if 0 = 2 then c else d)) H00.
claim Hf1: f 1 = b.
  prove (if 1 = 0 then a else (if 1 = 1 then b else (if 1 = 2 then c else d))) = b.
  claim H10: 1 <> 0. exact neq_1_0.
  claim Hstep1: (if 1 = 0 then a else (if 1 = 1 then b else (if 1 = 2 then c else d))) = (if 1 = 1 then b else (if 1 = 2 then c else d)).
    exact If_i_0 (1 = 0) a (if 1 = 1 then b else (if 1 = 2 then c else d)) H10.
  claim Hstep2: (if 1 = 1 then b else (if 1 = 2 then c else d)) = b.
    exact If_i_1 (1 = 1) b (if 1 = 2 then c else d) H11.
  exact eq_i_tra (if 1 = 0 then a else (if 1 = 1 then b else (if 1 = 2 then c else d))) (if 1 = 1 then b else (if 1 = 2 then c else d)) b Hstep1 Hstep2.
claim Hf2: f 2 = c.
  prove (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) = c.
  claim H20: 2 <> 0. exact neq_2_0.
  claim H21: 2 <> 1. exact neq_2_1.
  claim Hstep1: (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) = (if 2 = 1 then b else (if 2 = 2 then c else d)).
    exact If_i_0 (2 = 0) a (if 2 = 1 then b else (if 2 = 2 then c else d)) H20.
  claim Hstep2: (if 2 = 1 then b else (if 2 = 2 then c else d)) = (if 2 = 2 then c else d).
    exact If_i_0 (2 = 1) b (if 2 = 2 then c else d) H21.
  claim Hstep3: (if 2 = 2 then c else d) = c.
    exact If_i_1 (2 = 2) c d H22.
  claim Hmid: (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) = (if 2 = 2 then c else d).
    exact eq_i_tra (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) (if 2 = 1 then b else (if 2 = 2 then c else d)) (if 2 = 2 then c else d) Hstep1 Hstep2.
  exact eq_i_tra (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) (if 2 = 2 then c else d) c Hmid Hstep3.
claim Hf3: f 3 = d.
  prove (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) = d.
  claim H30: 3 <> 0. exact neq_3_0.
  claim H31: 3 <> 1. exact neq_3_1.
  claim H32: 3 <> 2. exact neq_3_2.
  claim Hstep1: (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) = (if 3 = 1 then b else (if 3 = 2 then c else d)).
    exact If_i_0 (3 = 0) a (if 3 = 1 then b else (if 3 = 2 then c else d)) H30.
  claim Hstep2: (if 3 = 1 then b else (if 3 = 2 then c else d)) = (if 3 = 2 then c else d).
    exact If_i_0 (3 = 1) b (if 3 = 2 then c else d) H31.
  claim Hstep3: (if 3 = 2 then c else d) = d.
    exact If_i_0 (3 = 2) c d H32.
  claim Hmid: (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) = (if 3 = 2 then c else d).
    exact eq_i_tra (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) (if 3 = 1 then b else (if 3 = 2 then c else d)) (if 3 = 2 then c else d) Hstep1 Hstep2.
  exact eq_i_tra (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) (if 3 = 2 then c else d) d Hmid Hstep3.
claim HaS: a :e S.
  apply binunionI1 ({a, b} :\/: {c}) {d} a.
  apply binunionI1 {a, b} {c} a.
  exact UPairI1 a b.
claim Hf0S: f 0 :e S.
  exact Hf0 (fun x y => y :e S) HaS.
claim HbS: b :e S.
  apply binunionI1 ({a, b} :\/: {c}) {d} b.
  apply binunionI1 {a, b} {c} b.
  exact UPairI2 a b.
claim Hf1S: f 1 :e S.
  exact Hf1 (fun x y => y :e S) HbS.
claim HcS: c :e S.
  apply binunionI1 ({a, b} :\/: {c}) {d} c.
  apply binunionI2 {a, b} {c} c.
  exact SingI c.
claim Hf2S: f 2 :e S.
  exact Hf2 (fun x y => y :e S) HcS.
claim HdS: d :e S.
  apply binunionI2 ({a, b} :\/: {c}) {d} d.
  exact SingI d.
claim Hf3S: f 3 :e S.
  exact Hf3 (fun x y => y :e S) HdS.
apply bij_equip 4 S f.
prove bij 4 S f.
apply and3I (forall u :e 4, f u :e S) (forall u v :e 4, f u = f v -> u = v) (forall w :e S, exists u :e 4, f u = w).
- prove forall u :e 4, f u :e S.
  let u. assume Hu: u :e 4.
  exact cases_4 u Hu (fun i => f i :e S) Hf0S Hf1S Hf2S Hf3S.
- prove forall u v :e 4, f u = f v -> u = v.
  let u. assume Hu: u :e 4.
  let v. assume Hv: v :e 4.
  assume Hfuv: f u = f v.
  prove u = v.
  claim Hcase0: f 0 = f v -> 0 = v.
    assume H0v: f 0 = f v.
    claim Hcase00: f 0 = f 0 -> 0 = 0. assume HH. exact H00.
    claim Hcase01: f 0 = f 1 -> 0 = 1.
      assume H01: f 0 = f 1.
      prove False.
      claim Ha_eq_b: a = b.
        claim H1: f 0 = a. exact Hf0.
        claim H2: f 1 = b. exact Hf1.
        claim H3: a = f 0. prove forall Q: set -> set -> prop, Q a (f 0) -> Q (f 0) a. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 0 = b. exact eq_i_tra (f 0) (f 1) b H01 H2.
        exact eq_i_tra a (f 0) b H3 H4.
      exact Hab Ha_eq_b.
    claim Hcase02: f 0 = f 2 -> 0 = 2.
      assume H02: f 0 = f 2.
      prove False.
      claim Ha_eq_c: a = c.
        claim H1: f 0 = a. exact Hf0.
        claim H2: f 2 = c. exact Hf2.
        claim H3: a = f 0. prove forall Q: set -> set -> prop, Q a (f 0) -> Q (f 0) a. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 0 = c. exact eq_i_tra (f 0) (f 2) c H02 H2.
        exact eq_i_tra a (f 0) c H3 H4.
      exact Hac Ha_eq_c.
    claim Hcase03: f 0 = f 3 -> 0 = 3.
      assume H03: f 0 = f 3.
      prove False.
      claim Ha_eq_d: a = d.
        claim H1: f 0 = a. exact Hf0.
        claim H2: f 3 = d. exact Hf3.
        claim H3: a = f 0. prove forall Q: set -> set -> prop, Q a (f 0) -> Q (f 0) a. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 0 = d. exact eq_i_tra (f 0) (f 3) d H03 H2.
        exact eq_i_tra a (f 0) d H3 H4.
      exact Had Ha_eq_d.
    exact cases_4 v Hv (fun j => f 0 = f j -> 0 = j) Hcase00 Hcase01 Hcase02 Hcase03 H0v.
  claim Hcase1: f 1 = f v -> 1 = v.
    assume H1v: f 1 = f v.
    claim Hcase10: f 1 = f 0 -> 1 = 0.
      assume H10: f 1 = f 0.
      prove False.
      claim Hb_eq_a: b = a.
        claim H1: f 1 = b. exact Hf1.
        claim H2: f 0 = a. exact Hf0.
        claim H3: b = f 1. prove forall Q: set -> set -> prop, Q b (f 1) -> Q (f 1) b. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 1 = a. exact eq_i_tra (f 1) (f 0) a H10 H2.
        exact eq_i_tra b (f 1) a H3 H4.
      claim Ha_eq_b: a = b. prove forall Q: set -> set -> prop, Q a b -> Q b a. let Q. assume HQ. exact Hb_eq_a (fun x y => Q y x) HQ.
      exact Hab Ha_eq_b.
    claim Hcase11: f 1 = f 1 -> 1 = 1. assume HH. exact H11.
    claim Hcase12: f 1 = f 2 -> 1 = 2.
      assume H12: f 1 = f 2.
      prove False.
      claim Hb_eq_c: b = c.
        claim H1: f 1 = b. exact Hf1.
        claim H2: f 2 = c. exact Hf2.
        claim H3: b = f 1. prove forall Q: set -> set -> prop, Q b (f 1) -> Q (f 1) b. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 1 = c. exact eq_i_tra (f 1) (f 2) c H12 H2.
        exact eq_i_tra b (f 1) c H3 H4.
      exact Hbc Hb_eq_c.
    claim Hcase13: f 1 = f 3 -> 1 = 3.
      assume H13: f 1 = f 3.
      prove False.
      claim Hb_eq_d: b = d.
        claim H1: f 1 = b. exact Hf1.
        claim H2: f 3 = d. exact Hf3.
        claim H3: b = f 1. prove forall Q: set -> set -> prop, Q b (f 1) -> Q (f 1) b. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 1 = d. exact eq_i_tra (f 1) (f 3) d H13 H2.
        exact eq_i_tra b (f 1) d H3 H4.
      exact Hbd Hb_eq_d.
    exact cases_4 v Hv (fun j => f 1 = f j -> 1 = j) Hcase10 Hcase11 Hcase12 Hcase13 H1v.
  claim Hcase2: f 2 = f v -> 2 = v.
    assume H2v: f 2 = f v.
    claim Hcase20: f 2 = f 0 -> 2 = 0.
      assume H20: f 2 = f 0.
      prove False.
      claim Hc_eq_a: c = a.
        claim H1: f 2 = c. exact Hf2.
        claim H2: f 0 = a. exact Hf0.
        claim H3: c = f 2. prove forall Q: set -> set -> prop, Q c (f 2) -> Q (f 2) c. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 2 = a. exact eq_i_tra (f 2) (f 0) a H20 H2.
        exact eq_i_tra c (f 2) a H3 H4.
      claim Ha_eq_c: a = c. prove forall Q: set -> set -> prop, Q a c -> Q c a. let Q. assume HQ. exact Hc_eq_a (fun x y => Q y x) HQ.
      exact Hac Ha_eq_c.
    claim Hcase21: f 2 = f 1 -> 2 = 1.
      assume H21: f 2 = f 1.
      prove False.
      claim Hc_eq_b: c = b.
        claim H1: f 2 = c. exact Hf2.
        claim H2: f 1 = b. exact Hf1.
        claim H3: c = f 2. prove forall Q: set -> set -> prop, Q c (f 2) -> Q (f 2) c. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 2 = b. exact eq_i_tra (f 2) (f 1) b H21 H2.
        exact eq_i_tra c (f 2) b H3 H4.
      claim Hb_eq_c: b = c. prove forall Q: set -> set -> prop, Q b c -> Q c b. let Q. assume HQ. exact Hc_eq_b (fun x y => Q y x) HQ.
      exact Hbc Hb_eq_c.
    claim Hcase22: f 2 = f 2 -> 2 = 2. assume HH. exact H22.
    claim Hcase23: f 2 = f 3 -> 2 = 3.
      assume H23: f 2 = f 3.
      prove False.
      claim Hc_eq_d: c = d.
        claim H1: f 2 = c. exact Hf2.
        claim H2: f 3 = d. exact Hf3.
        claim H3: c = f 2. prove forall Q: set -> set -> prop, Q c (f 2) -> Q (f 2) c. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 2 = d. exact eq_i_tra (f 2) (f 3) d H23 H2.
        exact eq_i_tra c (f 2) d H3 H4.
      exact Hcd Hc_eq_d.
    exact cases_4 v Hv (fun j => f 2 = f j -> 2 = j) Hcase20 Hcase21 Hcase22 Hcase23 H2v.
  claim Hcase3: f 3 = f v -> 3 = v.
    assume H3v: f 3 = f v.
    claim Hcase30: f 3 = f 0 -> 3 = 0.
      assume H30: f 3 = f 0.
      prove False.
      claim Hd_eq_a: d = a.
        claim H1: f 3 = d. exact Hf3.
        claim H2: f 0 = a. exact Hf0.
        claim H3: d = f 3. prove forall Q: set -> set -> prop, Q d (f 3) -> Q (f 3) d. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 3 = a. exact eq_i_tra (f 3) (f 0) a H30 H2.
        exact eq_i_tra d (f 3) a H3 H4.
      claim Ha_eq_d: a = d. prove forall Q: set -> set -> prop, Q a d -> Q d a. let Q. assume HQ. exact Hd_eq_a (fun x y => Q y x) HQ.
      exact Had Ha_eq_d.
    claim Hcase31: f 3 = f 1 -> 3 = 1.
      assume H31: f 3 = f 1.
      prove False.
      claim Hd_eq_b: d = b.
        claim H1: f 3 = d. exact Hf3.
        claim H2: f 1 = b. exact Hf1.
        claim H3: d = f 3. prove forall Q: set -> set -> prop, Q d (f 3) -> Q (f 3) d. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 3 = b. exact eq_i_tra (f 3) (f 1) b H31 H2.
        exact eq_i_tra d (f 3) b H3 H4.
      claim Hb_eq_d: b = d. prove forall Q: set -> set -> prop, Q b d -> Q d b. let Q. assume HQ. exact Hd_eq_b (fun x y => Q y x) HQ.
      exact Hbd Hb_eq_d.
    claim Hcase32: f 3 = f 2 -> 3 = 2.
      assume H32: f 3 = f 2.
      prove False.
      claim Hd_eq_c: d = c.
        claim H1: f 3 = d. exact Hf3.
        claim H2: f 2 = c. exact Hf2.
        claim H3: d = f 3. prove forall Q: set -> set -> prop, Q d (f 3) -> Q (f 3) d. let Q. assume HQ. exact H1 (fun x y => Q y x) HQ.
        claim H4: f 3 = c. exact eq_i_tra (f 3) (f 2) c H32 H2.
        exact eq_i_tra d (f 3) c H3 H4.
      claim Hc_eq_d: c = d. prove forall Q: set -> set -> prop, Q c d -> Q d c. let Q. assume HQ. exact Hd_eq_c (fun x y => Q y x) HQ.
      exact Hcd Hc_eq_d.
    claim Hcase33: f 3 = f 3 -> 3 = 3. assume HH. exact H33.
    exact cases_4 v Hv (fun j => f 3 = f j -> 3 = j) Hcase30 Hcase31 Hcase32 Hcase33 H3v.
  exact cases_4 u Hu (fun i => f i = f v -> i = v) Hcase0 Hcase1 Hcase2 Hcase3 Hfuv.
- prove forall w :e S, exists u :e 4, f u = w.
  let w. assume Hw: w :e S.
  prove exists u :e 4, f u = w.
  claim Hcasea: w = a -> exists u :e 4, f u = w.
    assume Hwa: w = a.
    witness 0.
    claim Haw: a = w. prove forall Q: set -> set -> prop, Q a w -> Q w a. let Q. assume HQ. exact Hwa (fun x y => Q y x) HQ.
    claim Hf0w: f 0 = w. exact eq_i_tra (f 0) a w Hf0 Haw.
    exact andI (0 :e 4) (f 0 = w) In_0_4 Hf0w.
  claim Hcaseb: w = b -> exists u :e 4, f u = w.
    assume Hwb: w = b.
    witness 1.
    claim Hbw: b = w. prove forall Q: set -> set -> prop, Q b w -> Q w b. let Q. assume HQ. exact Hwb (fun x y => Q y x) HQ.
    claim Hf1w: f 1 = w. exact eq_i_tra (f 1) b w Hf1 Hbw.
    exact andI (1 :e 4) (f 1 = w) In_1_4 Hf1w.
  claim Hcasec: w = c -> exists u :e 4, f u = w.
    assume Hwc: w = c.
    witness 2.
    claim Hcw: c = w. prove forall Q: set -> set -> prop, Q c w -> Q w c. let Q. assume HQ. exact Hwc (fun x y => Q y x) HQ.
    claim Hf2w: f 2 = w. exact eq_i_tra (f 2) c w Hf2 Hcw.
    exact andI (2 :e 4) (f 2 = w) In_2_4 Hf2w.
  claim Hcased: w = d -> exists u :e 4, f u = w.
    assume Hwd: w = d.
    witness 3.
    claim Hdw: d = w. prove forall Q: set -> set -> prop, Q d w -> Q w d. let Q. assume HQ. exact Hwd (fun x y => Q y x) HQ.
    claim Hf3w: f 3 = w. exact eq_i_tra (f 3) d w Hf3 Hdw.
    exact andI (3 :e 4) (f 3 = w) In_3_4 Hf3w.
  apply binunionE ({a, b} :\/: {c}) {d} w Hw.
  + assume Hwabc: w :e ({a, b} :\/: {c}).
    apply binunionE {a, b} {c} w Hwabc.
    * assume Hwab: w :e {a, b}.
      apply UPairE w a b Hwab.
      - exact Hcasea.
      - exact Hcaseb.
    * assume Hwc: w :e {c}.
      exact Hcasec (SingE c w Hwc).
  + assume Hwd: w :e {d}.
    exact Hcased (SingE d w Hwd).
Qed.
