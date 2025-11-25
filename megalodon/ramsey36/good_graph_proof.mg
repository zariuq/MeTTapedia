Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Theorem equip_subset : forall n k U:set,
  k c= n ->
  equip n U ->
  exists T:set, T c= U /\ equip k T.
let n. let k. let U.
assume Hkn: k c= n.
assume Heq: equip n U.
apply Heq.
let f: set -> set.
assume Hbij: bij n U f.
set T := {f i | i :e k}.
witness T.
prove T c= U /\ equip k T.
apply and3E (forall u :e n, f u :e U) (forall u v :e n, f u = f v -> u = v) (forall w :e U, exists u :e n, f u = w) Hbij (T c= U /\ equip k T).
assume HfU: forall u :e n, f u :e U.
assume Hinj: forall u v :e n, f u = f v -> u = v.
assume Hsurj: forall w :e U, exists u :e n, f u = w.
apply andI (T c= U) (equip k T).
- prove T c= U.
  let y. assume Hy: y :e T.
  apply ReplE_impred k f y Hy (y :e U).
  let i. assume Hi: i :e k.
  assume Hyi: y = f i.
  prove y :e U.
  claim Hin: i :e n. exact Hkn i Hi.
  claim HfiU: f i :e U. exact HfU i Hin.
  exact Hyi (fun a b => b :e U) HfiU.
- prove equip k T.
  prove exists g : set -> set, bij k T g.
  witness f.
  prove bij k T f.
  apply and3I (forall u :e k, f u :e T) (forall u v :e k, f u = f v -> u = v) (forall w :e T, exists u :e k, f u = w).
  + prove forall u :e k, f u :e T.
    let u. assume Hu: u :e k.
    exact ReplI k f u Hu.
  + prove forall u v :e k, f u = f v -> u = v.
    let u. assume Hu: u :e k.
    let v. assume Hv: v :e k.
    assume Hfuv: f u = f v.
    exact Hinj u (Hkn u Hu) v (Hkn v Hv) Hfuv.
  + prove forall w :e T, exists u :e k, f u = w.
    let w. assume Hw: w :e T.
    apply ReplE_impred k f w Hw (exists u :e k, f u = w).
    let i. assume Hi: i :e k.
    assume Hwi: w = f i.
    witness i.
    prove i :e k /\ f i = w.
    claim Hfiw: f i = w.
      prove forall Q: set -> set -> prop, Q (f i) w -> Q w (f i).
      let Q: set -> set -> prop. assume HQ: Q (f i) w.
      exact Hwi (fun a b => Q b a) HQ.
    exact andI (i :e k) (f i = w) Hi Hfiw.
Qed.

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
let V. let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
assume Hno6: no_k_indep V R 6.
let v. assume Hv: v :e V.
let S. assume HSV: S c= V. assume HS6: equip 6 S.
assume Hadj: forall x :e S, R v x.
assume Hneqv: forall x :e S, v <> x.
prove False.
apply Hno6 S HSV HS6.
prove is_indep_set V R S.
prove S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).
apply andI (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y).
- exact HSV.
- prove forall x :e S, forall y :e S, x <> y -> ~R x y.
  let x. assume HxS: x :e S.
  let y. assume HyS: y :e S.
  assume Hneq: x <> y.
  exact neighborhood_indep V R Hsym Htf v Hv x (HSV x HxS) y (HSV y HyS)
        (Hadj x HxS) (Hadj y HyS) Hneq.
Qed.

Theorem non_neighbors_triangle_free : forall V:set, forall R:set -> set -> prop,
  triangle_free V R ->
  forall T:set, T c= V ->
  triangle_free T R.
let V. let R: set -> set -> prop.
assume Htf: triangle_free V R.
let T. assume HTV: T c= V.
prove triangle_free T R.
prove forall x :e T, forall y :e T, forall z :e T, R x y -> R y z -> R x z -> False.
let x. assume Hx: x :e T.
let y. assume Hy: y :e T.
let z. assume Hz: z :e T.
assume Rxy: R x y.
assume Ryz: R y z.
assume Rxz: R x z.
exact Htf x (HTV x Hx) y (HTV y Hy) z (HTV z Hz) Rxy Ryz Rxz.
Qed.

Theorem indep_subset_extends : forall V:set, forall R:set -> set -> prop, forall S T:set,
  is_indep_set V R S ->
  T c= S ->
  is_indep_set V R T.
let V. let R: set -> set -> prop. let S. let T.
assume HS: is_indep_set V R S.
assume HTS: T c= S.
prove is_indep_set V R T.
prove T c= V /\ (forall x :e T, forall y :e T, x <> y -> ~R x y).
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) HS.
claim HSindep: forall x :e S, forall y :e S, x <> y -> ~R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) HS.
apply andI (T c= V) (forall x :e T, forall y :e T, x <> y -> ~R x y).
- prove T c= V.
  let t. assume Ht: t :e T.
  exact HSV t (HTS t Ht).
- prove forall x :e T, forall y :e T, x <> y -> ~R x y.
  let x. assume Hx: x :e T.
  let y. assume Hy: y :e T.
  assume Hneq: x <> y.
  exact HSindep x (HTS x Hx) y (HTS y Hy) Hneq.
Qed.

Theorem indep_add_vertex : forall V:set, forall R:set -> set -> prop, forall S:set, forall v:set,
  is_indep_set V R S ->
  v :e V ->
  v /:e S ->
  (forall x :e S, ~R v x) ->
  (forall x :e S, ~R x v) ->
  is_indep_set V R (S :\/: {v}).
let V. let R: set -> set -> prop. let S. let v.
assume HS: is_indep_set V R S.
assume HvV: v :e V.
assume HvnotS: v /:e S.
assume Hvnonadj: forall x :e S, ~R v x.
assume Hnonadjv: forall x :e S, ~R x v.
prove is_indep_set V R (S :\/: {v}).
prove (S :\/: {v}) c= V /\ (forall x :e (S :\/: {v}), forall y :e (S :\/: {v}), x <> y -> ~R x y).
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) HS.
claim HSindep: forall x :e S, forall y :e S, x <> y -> ~R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) HS.
apply andI ((S :\/: {v}) c= V) (forall x :e (S :\/: {v}), forall y :e (S :\/: {v}), x <> y -> ~R x y).
- prove (S :\/: {v}) c= V.
  let z. assume Hz: z :e S :\/: {v}.
  apply binunionE S {v} z Hz.
  + assume HzS: z :e S.
    exact HSV z HzS.
  + assume Hzv: z :e {v}.
    claim Hzeqv: z = v. exact SingE v z Hzv.
    rewrite Hzeqv.
    exact HvV.
- prove forall x :e (S :\/: {v}), forall y :e (S :\/: {v}), x <> y -> ~R x y.
  let x. assume Hx: x :e S :\/: {v}.
  let y. assume Hy: y :e S :\/: {v}.
  assume Hneq: x <> y.
  prove ~R x y.
  assume Hxy: R x y.
  apply binunionE S {v} x Hx.
  + assume HxS: x :e S.
    apply binunionE S {v} y Hy.
    * assume HyS: y :e S.
      apply HSindep x HxS y HyS Hneq.
      exact Hxy.
    * assume Hyv: y :e {v}.
      claim Hyeqv: y = v. exact SingE v y Hyv.
      apply Hnonadjv x HxS.
      rewrite <- Hyeqv.
      exact Hxy.
  + assume Hxv: x :e {v}.
    claim Hxeqv: x = v. exact SingE v x Hxv.
    apply binunionE S {v} y Hy.
    * assume HyS: y :e S.
      apply Hvnonadj y HyS.
      rewrite <- Hxeqv.
      exact Hxy.
    * assume Hyv: y :e {v}.
      claim Hyeqv: y = v. exact SingE v y Hyv.
      claim Hveqy: v = y.
        prove forall Q: set -> set -> prop, Q v y -> Q y v.
        let Q: set -> set -> prop. assume HQ: Q v y.
        exact Hyeqv (fun a b => Q b a) HQ.
      apply Hneq.
      prove x = y.
      exact eq_i_tra x v y Hxeqv Hveqy.
Qed.

Theorem neighbors_form_indep : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  forall v :e V, forall S:set,
    S c= V -> (forall x :e S, R v x) -> (forall x :e S, forall y :e S, x <> y -> ~R x y).
let V. let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
let v. assume Hv: v :e V.
let S. assume HSV: S c= V.
assume Hadj: forall x :e S, R v x.
let x. assume Hx: x :e S.
let y. assume Hy: y :e S.
assume Hneq: x <> y.
exact neighborhood_indep V R Hsym Htf v Hv x (HSV x Hx) y (HSV y Hy)
      (Hadj x Hx) (Hadj y Hy) Hneq.
Qed.

Theorem equip_4_quad : forall a b c d: set,
  a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d ->
  equip 4 (({a, b} :\/: {c}) :\/: {d}).
let a. let b. let c. let d.
assume Hab: a <> b. assume Hac: a <> c. assume Had: a <> d.
assume Hbc: b <> c. assume Hbd: b <> d. assume Hcd: c <> d.
set S := ({a, b} :\/: {c}) :\/: {d}.
set f := fun n:set => if n = 0 then a else (if n = 1 then b else (if n = 2 then c else d)).
claim H00: 0 = 0. prove forall Q: set -> set -> prop, Q 0 0 -> Q 0 0. let Q. assume HQ. exact HQ.
claim H11: 1 = 1. prove forall Q: set -> set -> prop, Q 1 1 -> Q 1 1. let Q. assume HQ. exact HQ.
claim H22: 2 = 2. prove forall Q: set -> set -> prop, Q 2 2 -> Q 2 2. let Q. assume HQ. exact HQ.
claim H33: 3 = 3. prove forall Q: set -> set -> prop, Q 3 3 -> Q 3 3. let Q. assume HQ. exact HQ.
claim Hf0: f 0 = a. exact If_i_1 (0 = 0) a (if 0 = 1 then b else (if 0 = 2 then c else d)) H00.
claim Hf1: f 1 = b.
  claim Hstep1: (if 1 = 0 then a else (if 1 = 1 then b else (if 1 = 2 then c else d))) = (if 1 = 1 then b else (if 1 = 2 then c else d)).
    exact If_i_0 (1 = 0) a (if 1 = 1 then b else (if 1 = 2 then c else d)) neq_1_0.
  claim Hstep2: (if 1 = 1 then b else (if 1 = 2 then c else d)) = b. exact If_i_1 (1 = 1) b (if 1 = 2 then c else d) H11.
  exact eq_i_tra (if 1 = 0 then a else (if 1 = 1 then b else (if 1 = 2 then c else d))) (if 1 = 1 then b else (if 1 = 2 then c else d)) b Hstep1 Hstep2.
claim Hf2: f 2 = c.
  claim Hstep1: (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) = (if 2 = 1 then b else (if 2 = 2 then c else d)).
    exact If_i_0 (2 = 0) a (if 2 = 1 then b else (if 2 = 2 then c else d)) neq_2_0.
  claim Hstep2: (if 2 = 1 then b else (if 2 = 2 then c else d)) = (if 2 = 2 then c else d). exact If_i_0 (2 = 1) b (if 2 = 2 then c else d) neq_2_1.
  claim Hstep3: (if 2 = 2 then c else d) = c. exact If_i_1 (2 = 2) c d H22.
  claim Hmid: (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) = (if 2 = 2 then c else d).
    exact eq_i_tra (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) (if 2 = 1 then b else (if 2 = 2 then c else d)) (if 2 = 2 then c else d) Hstep1 Hstep2.
  exact eq_i_tra (if 2 = 0 then a else (if 2 = 1 then b else (if 2 = 2 then c else d))) (if 2 = 2 then c else d) c Hmid Hstep3.
claim Hf3: f 3 = d.
  claim Hstep1: (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) = (if 3 = 1 then b else (if 3 = 2 then c else d)).
    exact If_i_0 (3 = 0) a (if 3 = 1 then b else (if 3 = 2 then c else d)) neq_3_0.
  claim Hstep2: (if 3 = 1 then b else (if 3 = 2 then c else d)) = (if 3 = 2 then c else d). exact If_i_0 (3 = 1) b (if 3 = 2 then c else d) neq_3_1.
  claim Hstep3: (if 3 = 2 then c else d) = d. exact If_i_0 (3 = 2) c d neq_3_2.
  claim Hmid: (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) = (if 3 = 2 then c else d).
    exact eq_i_tra (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) (if 3 = 1 then b else (if 3 = 2 then c else d)) (if 3 = 2 then c else d) Hstep1 Hstep2.
  exact eq_i_tra (if 3 = 0 then a else (if 3 = 1 then b else (if 3 = 2 then c else d))) (if 3 = 2 then c else d) d Hmid Hstep3.
claim HaS: a :e S. apply binunionI1 ({a, b} :\/: {c}) {d} a. apply binunionI1 {a, b} {c} a. exact UPairI1 a b.
claim Hf0S: f 0 :e S. exact Hf0 (fun x y => y :e S) HaS.
claim HbS: b :e S. apply binunionI1 ({a, b} :\/: {c}) {d} b. apply binunionI1 {a, b} {c} b. exact UPairI2 a b.
claim Hf1S: f 1 :e S. exact Hf1 (fun x y => y :e S) HbS.
claim HcS: c :e S. apply binunionI1 ({a, b} :\/: {c}) {d} c. apply binunionI2 {a, b} {c} c. exact SingI c.
claim Hf2S: f 2 :e S. exact Hf2 (fun x y => y :e S) HcS.
claim HdS: d :e S. apply binunionI2 ({a, b} :\/: {c}) {d} d. exact SingI d.
claim Hf3S: f 3 :e S. exact Hf3 (fun x y => y :e S) HdS.
prove equip 4 S.
prove exists g : set -> set, bij 4 S g.
witness f.
prove bij 4 S f.
apply and3I (forall u :e 4, f u :e S) (forall u v :e 4, f u = f v -> u = v) (forall w :e S, exists u :e 4, f u = w).
- let u. assume Hu: u :e 4. exact cases_4 u Hu (fun i => f i :e S) Hf0S Hf1S Hf2S Hf3S.
- let u. assume Hu: u :e 4. let v. assume Hv: v :e 4. assume Hfuv: f u = f v.
  claim Hcase0: f 0 = f v -> 0 = v.
    assume H0v: f 0 = f v.
    claim Hcase00: f 0 = f 0 -> 0 = 0. assume HH. exact H00.
    claim Hcase01: f 0 = f 1 -> 0 = 1.
      assume H01: f 0 = f 1. prove False.
      claim Ha_eq_b: a = b. claim H3: a = f 0. prove forall Q: set -> set -> prop, Q a (f 0) -> Q (f 0) a. let Q. assume HQ. exact Hf0 (fun x y => Q y x) HQ.
        claim H4: f 0 = b. exact eq_i_tra (f 0) (f 1) b H01 Hf1. exact eq_i_tra a (f 0) b H3 H4.
      exact Hab Ha_eq_b.
    claim Hcase02: f 0 = f 2 -> 0 = 2.
      assume H02: f 0 = f 2. prove False.
      claim Ha_eq_c: a = c. claim H3: a = f 0. prove forall Q: set -> set -> prop, Q a (f 0) -> Q (f 0) a. let Q. assume HQ. exact Hf0 (fun x y => Q y x) HQ.
        claim H4: f 0 = c. exact eq_i_tra (f 0) (f 2) c H02 Hf2. exact eq_i_tra a (f 0) c H3 H4.
      exact Hac Ha_eq_c.
    claim Hcase03: f 0 = f 3 -> 0 = 3.
      assume H03: f 0 = f 3. prove False.
      claim Ha_eq_d: a = d. claim H3: a = f 0. prove forall Q: set -> set -> prop, Q a (f 0) -> Q (f 0) a. let Q. assume HQ. exact Hf0 (fun x y => Q y x) HQ.
        claim H4: f 0 = d. exact eq_i_tra (f 0) (f 3) d H03 Hf3. exact eq_i_tra a (f 0) d H3 H4.
      exact Had Ha_eq_d.
    exact cases_4 v Hv (fun j => f 0 = f j -> 0 = j) Hcase00 Hcase01 Hcase02 Hcase03 H0v.
  claim Hcase1: f 1 = f v -> 1 = v.
    assume H1v: f 1 = f v.
    claim Hcase10: f 1 = f 0 -> 1 = 0.
      assume H10: f 1 = f 0. prove False.
      claim Hb_eq_a: b = a. claim H3: b = f 1. prove forall Q: set -> set -> prop, Q b (f 1) -> Q (f 1) b. let Q. assume HQ. exact Hf1 (fun x y => Q y x) HQ.
        claim H4: f 1 = a. exact eq_i_tra (f 1) (f 0) a H10 Hf0. exact eq_i_tra b (f 1) a H3 H4.
      claim Ha_eq_b: a = b. prove forall Q: set -> set -> prop, Q a b -> Q b a. let Q. assume HQ. exact Hb_eq_a (fun x y => Q y x) HQ.
      exact Hab Ha_eq_b.
    claim Hcase11: f 1 = f 1 -> 1 = 1. assume HH. exact H11.
    claim Hcase12: f 1 = f 2 -> 1 = 2.
      assume H12: f 1 = f 2. prove False.
      claim Hb_eq_c: b = c. claim H3: b = f 1. prove forall Q: set -> set -> prop, Q b (f 1) -> Q (f 1) b. let Q. assume HQ. exact Hf1 (fun x y => Q y x) HQ.
        claim H4: f 1 = c. exact eq_i_tra (f 1) (f 2) c H12 Hf2. exact eq_i_tra b (f 1) c H3 H4.
      exact Hbc Hb_eq_c.
    claim Hcase13: f 1 = f 3 -> 1 = 3.
      assume H13: f 1 = f 3. prove False.
      claim Hb_eq_d: b = d. claim H3: b = f 1. prove forall Q: set -> set -> prop, Q b (f 1) -> Q (f 1) b. let Q. assume HQ. exact Hf1 (fun x y => Q y x) HQ.
        claim H4: f 1 = d. exact eq_i_tra (f 1) (f 3) d H13 Hf3. exact eq_i_tra b (f 1) d H3 H4.
      exact Hbd Hb_eq_d.
    exact cases_4 v Hv (fun j => f 1 = f j -> 1 = j) Hcase10 Hcase11 Hcase12 Hcase13 H1v.
  claim Hcase2: f 2 = f v -> 2 = v.
    assume H2v: f 2 = f v.
    claim Hcase20: f 2 = f 0 -> 2 = 0.
      assume H20: f 2 = f 0. prove False.
      claim Hc_eq_a: c = a. claim H3: c = f 2. prove forall Q: set -> set -> prop, Q c (f 2) -> Q (f 2) c. let Q. assume HQ. exact Hf2 (fun x y => Q y x) HQ.
        claim H4: f 2 = a. exact eq_i_tra (f 2) (f 0) a H20 Hf0. exact eq_i_tra c (f 2) a H3 H4.
      claim Ha_eq_c: a = c. prove forall Q: set -> set -> prop, Q a c -> Q c a. let Q. assume HQ. exact Hc_eq_a (fun x y => Q y x) HQ.
      exact Hac Ha_eq_c.
    claim Hcase21: f 2 = f 1 -> 2 = 1.
      assume H21: f 2 = f 1. prove False.
      claim Hc_eq_b: c = b. claim H3: c = f 2. prove forall Q: set -> set -> prop, Q c (f 2) -> Q (f 2) c. let Q. assume HQ. exact Hf2 (fun x y => Q y x) HQ.
        claim H4: f 2 = b. exact eq_i_tra (f 2) (f 1) b H21 Hf1. exact eq_i_tra c (f 2) b H3 H4.
      claim Hb_eq_c: b = c. prove forall Q: set -> set -> prop, Q b c -> Q c b. let Q. assume HQ. exact Hc_eq_b (fun x y => Q y x) HQ.
      exact Hbc Hb_eq_c.
    claim Hcase22: f 2 = f 2 -> 2 = 2. assume HH. exact H22.
    claim Hcase23: f 2 = f 3 -> 2 = 3.
      assume H23: f 2 = f 3. prove False.
      claim Hc_eq_d: c = d. claim H3: c = f 2. prove forall Q: set -> set -> prop, Q c (f 2) -> Q (f 2) c. let Q. assume HQ. exact Hf2 (fun x y => Q y x) HQ.
        claim H4: f 2 = d. exact eq_i_tra (f 2) (f 3) d H23 Hf3. exact eq_i_tra c (f 2) d H3 H4.
      exact Hcd Hc_eq_d.
    exact cases_4 v Hv (fun j => f 2 = f j -> 2 = j) Hcase20 Hcase21 Hcase22 Hcase23 H2v.
  claim Hcase3: f 3 = f v -> 3 = v.
    assume H3v: f 3 = f v.
    claim Hcase30: f 3 = f 0 -> 3 = 0.
      assume H30: f 3 = f 0. prove False.
      claim Hd_eq_a: d = a. claim H3: d = f 3. prove forall Q: set -> set -> prop, Q d (f 3) -> Q (f 3) d. let Q. assume HQ. exact Hf3 (fun x y => Q y x) HQ.
        claim H4: f 3 = a. exact eq_i_tra (f 3) (f 0) a H30 Hf0. exact eq_i_tra d (f 3) a H3 H4.
      claim Ha_eq_d: a = d. prove forall Q: set -> set -> prop, Q a d -> Q d a. let Q. assume HQ. exact Hd_eq_a (fun x y => Q y x) HQ.
      exact Had Ha_eq_d.
    claim Hcase31: f 3 = f 1 -> 3 = 1.
      assume H31: f 3 = f 1. prove False.
      claim Hd_eq_b: d = b. claim H3: d = f 3. prove forall Q: set -> set -> prop, Q d (f 3) -> Q (f 3) d. let Q. assume HQ. exact Hf3 (fun x y => Q y x) HQ.
        claim H4: f 3 = b. exact eq_i_tra (f 3) (f 1) b H31 Hf1. exact eq_i_tra d (f 3) b H3 H4.
      claim Hb_eq_d: b = d. prove forall Q: set -> set -> prop, Q b d -> Q d b. let Q. assume HQ. exact Hd_eq_b (fun x y => Q y x) HQ.
      exact Hbd Hb_eq_d.
    claim Hcase32: f 3 = f 2 -> 3 = 2.
      assume H32: f 3 = f 2. prove False.
      claim Hd_eq_c: d = c. claim H3: d = f 3. prove forall Q: set -> set -> prop, Q d (f 3) -> Q (f 3) d. let Q. assume HQ. exact Hf3 (fun x y => Q y x) HQ.
        claim H4: f 3 = c. exact eq_i_tra (f 3) (f 2) c H32 Hf2. exact eq_i_tra d (f 3) c H3 H4.
      claim Hc_eq_d: c = d. prove forall Q: set -> set -> prop, Q c d -> Q d c. let Q. assume HQ. exact Hd_eq_c (fun x y => Q y x) HQ.
      exact Hcd Hc_eq_d.
    claim Hcase33: f 3 = f 3 -> 3 = 3. assume HH. exact H33.
    exact cases_4 v Hv (fun j => f 3 = f j -> 3 = j) Hcase30 Hcase31 Hcase32 Hcase33 H3v.
  exact cases_4 u Hu (fun i => f i = f v -> i = v) Hcase0 Hcase1 Hcase2 Hcase3 Hfuv.
- let w. assume Hw: w :e S.
  claim Hcasea: w = a -> exists u :e 4, f u = w.
    assume Hwa: w = a. witness 0.
    claim Haw: a = w. prove forall Q: set -> set -> prop, Q a w -> Q w a. let Q. assume HQ. exact Hwa (fun x y => Q y x) HQ.
    exact andI (0 :e 4) (f 0 = w) In_0_4 (eq_i_tra (f 0) a w Hf0 Haw).
  claim Hcaseb: w = b -> exists u :e 4, f u = w.
    assume Hwb: w = b. witness 1.
    claim Hbw: b = w. prove forall Q: set -> set -> prop, Q b w -> Q w b. let Q. assume HQ. exact Hwb (fun x y => Q y x) HQ.
    exact andI (1 :e 4) (f 1 = w) In_1_4 (eq_i_tra (f 1) b w Hf1 Hbw).
  claim Hcasec: w = c -> exists u :e 4, f u = w.
    assume Hwc: w = c. witness 2.
    claim Hcw: c = w. prove forall Q: set -> set -> prop, Q c w -> Q w c. let Q. assume HQ. exact Hwc (fun x y => Q y x) HQ.
    exact andI (2 :e 4) (f 2 = w) In_2_4 (eq_i_tra (f 2) c w Hf2 Hcw).
  claim Hcased: w = d -> exists u :e 4, f u = w.
    assume Hwd: w = d. witness 3.
    claim Hdw: d = w. prove forall Q: set -> set -> prop, Q d w -> Q w d. let Q. assume HQ. exact Hwd (fun x y => Q y x) HQ.
    exact andI (3 :e 4) (f 3 = w) In_3_4 (eq_i_tra (f 3) d w Hf3 Hdw).
  apply binunionE ({a, b} :\/: {c}) {d} w Hw.
  + assume Hwabc: w :e ({a, b} :\/: {c}).
    apply binunionE {a, b} {c} w Hwabc.
    * assume Hwab: w :e {a, b}. apply UPairE w a b Hwab. exact Hcasea. exact Hcaseb.
    * assume Hwc: w :e {c}. exact Hcasec (SingE c w Hwc).
  + assume Hwd: w :e {d}. exact Hcased (SingE d w Hwd).
Qed.

Theorem four_neighbors_give_4indep : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  forall v :e V, forall n1 n2 n3 n4 :e V,
    n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n2 <> n3 -> n2 <> n4 -> n3 <> n4 ->
    R v n1 -> R v n2 -> R v n3 -> R v n4 ->
    exists S, S c= V /\ equip 4 S /\ is_indep_set V R S.
let V. let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
let v. assume Hv: v :e V.
let n1. assume Hn1: n1 :e V.
let n2. assume Hn2: n2 :e V.
let n3. assume Hn3: n3 :e V.
let n4. assume Hn4: n4 :e V.
assume H12: n1 <> n2. assume H13: n1 <> n3. assume H14: n1 <> n4.
assume H23: n2 <> n3. assume H24: n2 <> n4. assume H34: n3 <> n4.
assume Rv1: R v n1. assume Rv2: R v n2. assume Rv3: R v n3. assume Rv4: R v n4.
set S := ({n1, n2} :\/: {n3}) :\/: {n4}.
witness S.
apply and3I (S c= V) (equip 4 S) (is_indep_set V R S).
- prove S c= V.
  let w. assume Hw: w :e S.
  apply binunionE ({n1, n2} :\/: {n3}) {n4} w Hw.
  + assume Hw123: w :e ({n1, n2} :\/: {n3}).
    apply binunionE {n1, n2} {n3} w Hw123.
    * assume Hw12: w :e {n1, n2}.
      apply UPairE w n1 n2 Hw12.
      - assume Hwn1: w = n1. exact Hwn1 (fun a b => b :e V) Hn1.
      - assume Hwn2: w = n2. exact Hwn2 (fun a b => b :e V) Hn2.
    * assume Hw3: w :e {n3}. claim Hwn3: w = n3. exact SingE n3 w Hw3. exact Hwn3 (fun a b => b :e V) Hn3.
  + assume Hw4: w :e {n4}. claim Hwn4: w = n4. exact SingE n4 w Hw4. exact Hwn4 (fun a b => b :e V) Hn4.
- prove equip 4 S.
  exact equip_4_quad n1 n2 n3 n4 H12 H13 H14 H23 H24 H34.
- prove is_indep_set V R S.
  apply andI (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y).
  + let w. assume Hw: w :e S.
    apply binunionE ({n1, n2} :\/: {n3}) {n4} w Hw.
    * assume Hw123: w :e ({n1, n2} :\/: {n3}).
      apply binunionE {n1, n2} {n3} w Hw123.
      - assume Hw12: w :e {n1, n2}. apply UPairE w n1 n2 Hw12.
        + assume Hwn1: w = n1. exact Hwn1 (fun a b => b :e V) Hn1.
        + assume Hwn2: w = n2. exact Hwn2 (fun a b => b :e V) Hn2.
      - assume Hw3: w :e {n3}. claim Hwn3: w = n3. exact SingE n3 w Hw3. exact Hwn3 (fun a b => b :e V) Hn3.
    * assume Hw4: w :e {n4}. claim Hwn4: w = n4. exact SingE n4 w Hw4. exact Hwn4 (fun a b => b :e V) Hn4.
  + prove forall x :e S, forall y :e S, x <> y -> ~R x y.
    exact neighbors_form_indep V R Hsym Htf v Hv S
      (fun w Hw =>
        binunionE ({n1, n2} :\/: {n3}) {n4} w Hw (w :e V)
          (fun Hw123 => binunionE {n1, n2} {n3} w Hw123 (w :e V)
            (fun Hw12 => UPairE w n1 n2 Hw12 (w :e V)
              (fun Hwn1 => Hwn1 (fun a b => b :e V) Hn1)
              (fun Hwn2 => Hwn2 (fun a b => b :e V) Hn2))
            (fun Hw3 => (SingE n3 w Hw3) (fun a b => b :e V) Hn3))
          (fun Hw4 => (SingE n4 w Hw4) (fun a b => b :e V) Hn4))
      (fun w Hw =>
        binunionE ({n1, n2} :\/: {n3}) {n4} w Hw (R v w)
          (fun Hw123 => binunionE {n1, n2} {n3} w Hw123 (R v w)
            (fun Hw12 => UPairE w n1 n2 Hw12 (R v w)
              (fun Hwn1 =>
                let Hn1w : n1 = w := (fun Q HQ => Hwn1 (fun a b => Q b a) HQ)
                in Hn1w (fun a b => R v a) Rv1)
              (fun Hwn2 =>
                let Hn2w : n2 = w := (fun Q HQ => Hwn2 (fun a b => Q b a) HQ)
                in Hn2w (fun a b => R v a) Rv2))
            (fun Hw3 =>
              let Hwn3 := SingE n3 w Hw3 in
              let Hn3w : n3 = w := (fun Q HQ => Hwn3 (fun a b => Q b a) HQ)
              in Hn3w (fun a b => R v a) Rv3))
          (fun Hw4 =>
            let Hwn4 := SingE n4 w Hw4 in
            let Hn4w : n4 = w := (fun Q HQ => Hwn4 (fun a b => Q b a) HQ)
            in Hn4w (fun a b => R v a) Rv4)).
Qed.

Theorem six_nonneighbors_contradiction_on_9 : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  equip 9 V ->
  triangle_free V R ->
  ~(exists x y z :e V, R x y /\ R y z /\ R x z) ->
  ~(exists S, S c= V /\ equip 4 S /\ is_indep_set V R S) ->
  forall v :e V, forall m1 m2 m3 m4 m5 m6 :e V,
    m1 <> m2 -> m1 <> m3 -> m1 <> m4 -> m1 <> m5 -> m1 <> m6 ->
    m2 <> m3 -> m2 <> m4 -> m2 <> m5 -> m2 <> m6 ->
    m3 <> m4 -> m3 <> m5 -> m3 <> m6 ->
    m4 <> m5 -> m4 <> m6 ->
    m5 <> m6 ->
    ~R v m1 -> ~R v m2 -> ~R v m3 -> ~R v m4 -> ~R v m5 -> ~R v m6 -> False.
Admitted.

Theorem degree_parity_contradiction_on_9 : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  equip 9 V ->
  triangle_free V R ->
  (forall v :e V, forall n1 n2 n3 n4 :e V,
    n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n2 <> n3 -> n2 <> n4 -> n3 <> n4 ->
    R v n1 -> R v n2 -> R v n3 -> R v n4 -> False) ->
  (forall v :e V, forall m1 m2 m3 m4 m5 m6 :e V,
    m1 <> m2 -> m1 <> m3 -> m1 <> m4 -> m1 <> m5 -> m1 <> m6 ->
    m2 <> m3 -> m2 <> m4 -> m2 <> m5 -> m2 <> m6 ->
    m3 <> m4 -> m3 <> m5 -> m3 <> m6 ->
    m4 <> m5 -> m4 <> m6 ->
    m5 <> m6 ->
    ~R v m1 -> ~R v m2 -> ~R v m3 -> ~R v m4 -> ~R v m5 -> ~R v m6 -> False) ->
  False.
Admitted.

Theorem has_triangle_or_4indep_on_9 : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  equip 9 V ->
  (exists x y z :e V, R x y /\ R y z /\ R x z) \/
  (exists S, S c= V /\ equip 4 S /\ is_indep_set V R S).
let V. let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Hequip: equip 9 V.
apply dneg.
assume Hneg: ~((exists x y z :e V, R x y /\ R y z /\ R x z) \/
              (exists S, S c= V /\ equip 4 S /\ is_indep_set V R S)).
prove False.
claim Hno_tri: ~(exists x y z :e V, R x y /\ R y z /\ R x z).
  assume Htri. apply Hneg. apply orIL. exact Htri.
claim Hno_4indep: ~(exists S, S c= V /\ equip 4 S /\ is_indep_set V R S).
  assume H4. apply Hneg. apply orIR. exact H4.
claim Htf: triangle_free V R.
  prove forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.
  let x. assume Hx: x :e V.
  let y. assume Hy: y :e V.
  let z. assume Hz: z :e V.
  assume Rxy: R x y.
  assume Ryz: R y z.
  assume Rxz: R x z.
  apply Hno_tri.
  prove exists x :e V, exists y :e V, exists z :e V, R x y /\ R y z /\ R x z.
  witness x.
  prove x :e V /\ (exists y :e V, exists z :e V, R x y /\ R y z /\ R x z).
  claim H1: exists y :e V, exists z :e V, R x y /\ R y z /\ R x z.
    witness y.
    prove y :e V /\ (exists z :e V, R x y /\ R y z /\ R x z).
    claim H2: exists z :e V, R x y /\ R y z /\ R x z.
      witness z.
      prove z :e V /\ (R x y /\ R y z /\ R x z).
      exact andI (z :e V) (R x y /\ R y z /\ R x z) Hz (and3I (R x y) (R y z) (R x z) Rxy Ryz Rxz).
    exact andI (y :e V) (exists z :e V, R x y /\ R y z /\ R x z) Hy H2.
  exact andI (x :e V) (exists y :e V, exists z :e V, R x y /\ R y z /\ R x z) Hx H1.
claim Hno_4neighbors: forall v :e V, forall n1 n2 n3 n4 :e V,
    n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n2 <> n3 -> n2 <> n4 -> n3 <> n4 ->
    R v n1 -> R v n2 -> R v n3 -> R v n4 -> False.
  let v. assume Hv: v :e V.
  let n1. assume Hn1: n1 :e V.
  let n2. assume Hn2: n2 :e V.
  let n3. assume Hn3: n3 :e V.
  let n4. assume Hn4: n4 :e V.
  assume H12: n1 <> n2.
  assume H13: n1 <> n3.
  assume H14: n1 <> n4.
  assume H23: n2 <> n3.
  assume H24: n2 <> n4.
  assume H34: n3 <> n4.
  assume Rv1: R v n1.
  assume Rv2: R v n2.
  assume Rv3: R v n3.
  assume Rv4: R v n4.
  apply Hno_4indep.
  exact four_neighbors_give_4indep V R Hsym Htf v Hv n1 Hn1 n2 Hn2 n3 Hn3 n4 Hn4
        H12 H13 H14 H23 H24 H34 Rv1 Rv2 Rv3 Rv4.
claim Hno_6nonneighbors: forall v :e V, forall m1 m2 m3 m4 m5 m6 :e V,
    m1 <> m2 -> m1 <> m3 -> m1 <> m4 -> m1 <> m5 -> m1 <> m6 ->
    m2 <> m3 -> m2 <> m4 -> m2 <> m5 -> m2 <> m6 ->
    m3 <> m4 -> m3 <> m5 -> m3 <> m6 ->
    m4 <> m5 -> m4 <> m6 ->
    m5 <> m6 ->
    ~R v m1 -> ~R v m2 -> ~R v m3 -> ~R v m4 -> ~R v m5 -> ~R v m6 -> False.
  exact six_nonneighbors_contradiction_on_9 V R Hsym Hequip Htf Hno_tri Hno_4indep.
exact degree_parity_contradiction_on_9 V R Hsym Hequip Htf Hno_4neighbors Hno_6nonneighbors.
Qed.

Theorem triangle_free_9_has_4indep : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  equip 9 V ->
  exists S, S c= V /\ equip 4 S /\ is_indep_set V R S.
let V. let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
assume Hequip: equip 9 V.
prove exists S, S c= V /\ equip 4 S /\ is_indep_set V R S.
apply has_triangle_or_4indep_on_9 V R Hsym Hequip.
- assume Htri: exists x y z :e V, R x y /\ R y z /\ R x z.
  prove False.
  apply Htri.
  let x. assume Hx: x :e V /\ (exists y :e V, exists z :e V, R x y /\ R y z /\ R x z).
  claim HxV: x :e V. exact andEL (x :e V) (exists y :e V, exists z :e V, R x y /\ R y z /\ R x z) Hx.
  claim Hrest: exists y :e V, exists z :e V, R x y /\ R y z /\ R x z.
    exact andER (x :e V) (exists y :e V, exists z :e V, R x y /\ R y z /\ R x z) Hx.
  apply Hrest.
  let y. assume Hy: y :e V /\ (exists z :e V, R x y /\ R y z /\ R x z).
  claim HyV: y :e V. exact andEL (y :e V) (exists z :e V, R x y /\ R y z /\ R x z) Hy.
  claim Hrest2: exists z :e V, R x y /\ R y z /\ R x z.
    exact andER (y :e V) (exists z :e V, R x y /\ R y z /\ R x z) Hy.
  apply Hrest2.
  let z. assume Hz: z :e V /\ (R x y /\ R y z /\ R x z).
  claim HzV: z :e V. exact andEL (z :e V) (R x y /\ R y z /\ R x z) Hz.
  claim Hedges: R x y /\ R y z /\ R x z.
    exact andER (z :e V) (R x y /\ R y z /\ R x z) Hz.
  apply and3E (R x y) (R y z) (R x z) Hedges False.
  prove R x y -> R y z -> R x z -> False.
  assume Rxy: R x y. assume Ryz: R y z. assume Rxz: R x z.
  exact Htf x HxV y HyV z HzV Rxy Ryz Rxz.
- assume H4: exists S, S c= V /\ equip 4 S /\ is_indep_set V R S.
  exact H4.
Qed.

Theorem triangle_free_Subq : forall V W:set, forall R:set -> set -> prop,
  W c= V ->
  triangle_free V R ->
  triangle_free W R.
let V. let W. let R: set -> set -> prop.
assume HWV: W c= V.
assume Htf: triangle_free V R.
prove triangle_free W R.
prove forall x :e W, forall y :e W, forall z :e W, R x y -> R y z -> R x z -> False.
let x. assume Hx: x :e W.
let y. assume Hy: y :e W.
let z. assume Hz: z :e W.
exact Htf x (HWV x Hx) y (HWV y Hy) z (HWV z Hz).
Qed.

Theorem is_indep_set_enlarge : forall V W:set, forall R:set -> set -> prop, forall S:set,
  V c= W ->
  S c= V ->
  is_indep_set V R S ->
  is_indep_set W R S.
let V. let W. let R: set -> set -> prop. let S.
assume HVW: V c= W.
assume HSV: S c= V.
assume Hindep: is_indep_set V R S.
prove is_indep_set W R S.
prove S c= W /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).
apply andI (S c= W) (forall x :e S, forall y :e S, x <> y -> ~R x y).
- prove S c= W.
  let s. assume Hs: s :e S.
  exact HVW s (HSV s Hs).
- prove forall x :e S, forall y :e S, x <> y -> ~R x y.
  apply andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) Hindep.
Qed.

Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem in_9_12 : 9 :e 12.
prove 9 :e 12.
prove 9 :e ordsucc 11.
apply ordsuccI1 11.
prove 9 :e 11.
apply ordsuccI1 10.
prove 9 :e 10.
exact ordsuccI2 9.
Qed.

Theorem Subq_9_12 : 9 c= 12.
prove forall x :e 9, x :e 12.
let x. assume Hx: x :e 9.
exact nat_trans 12 nat_p_12 9 in_9_12 x Hx.
Qed.

Theorem non_neighbors_contain_4indep : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  forall v :e 18, forall T:set,
    T c= 18 ->
    equip 12 T ->
    (forall t :e T, ~R v t) ->
    exists S, S c= T /\ equip 4 S /\ is_indep_set 18 R S.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
let v. assume Hv: v :e 18.
let T. assume HT18: T c= 18.
assume HT12: equip 12 T.
assume Hnonadj: forall t :e T, ~R v t.
prove exists S, S c= T /\ equip 4 S /\ is_indep_set 18 R S.
apply equip_subset 12 9 T Subq_9_12 HT12.
let T'. assume HT'prop: T' c= T /\ equip 9 T'.
claim HT'T: T' c= T. exact andEL (T' c= T) (equip 9 T') HT'prop.
claim HT'9: equip 9 T'. exact andER (T' c= T) (equip 9 T') HT'prop.
claim HT'18: T' c= 18.
  let x. assume Hx: x :e T'.
  exact HT18 x (HT'T x Hx).
claim Htf_T': triangle_free T' R.
  exact triangle_free_Subq 18 T' R HT'18 Htf.
apply triangle_free_9_has_4indep T' R Hsym Htf_T' HT'9.
let S. assume HS: S c= T' /\ equip 4 S /\ is_indep_set T' R S.
apply and3E (S c= T') (equip 4 S) (is_indep_set T' R S) HS (exists S, S c= T /\ equip 4 S /\ is_indep_set 18 R S).
assume HS_T': S c= T'.
assume HS4: equip 4 S.
assume HS_indep_T': is_indep_set T' R S.
witness S.
prove S c= T /\ equip 4 S /\ is_indep_set 18 R S.
apply and3I (S c= T) (equip 4 S) (is_indep_set 18 R S).
- prove S c= T.
  let s. assume Hs: s :e S.
  exact HT'T s (HS_T' s Hs).
- prove equip 4 S.
  exact HS4.
- prove is_indep_set 18 R S.
  exact is_indep_set_enlarge T' 18 R S HT'18 HS_T' HS_indep_T'.
Qed.

Theorem vertex_has_12_nonneighbors : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
let v. assume Hv: v :e 18.
prove exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
Admitted.

Theorem can_extend_4indep_with_nonneighbor : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall S:set,
    S c= 18 ->
    equip 4 S ->
    (forall s :e S, ~R v s) ->
    (forall s :e S, ~R s v) ->
    is_indep_set 18 R S ->
    v /:e S ->
    False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
let v. assume Hv: v :e 18.
let S. assume HS18: S c= 18.
assume HS4: equip 4 S.
assume Hvs_nonadj1: forall s :e S, ~R v s.
assume Hvs_nonadj2: forall s :e S, ~R s v.
assume HS_indep: is_indep_set 18 R S.
assume Hv_notin_S: v /:e S.
prove False.
Admitted.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13 (nat_ordsucc 12
      (nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))))))))))).
Qed.

Theorem zero_in_18 : 0 :e 18.
exact nat_0_in_ordsucc 17 nat_p_17.
Qed.

Theorem good_graph_contradiction : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) -> triangle_free 18 R -> no_k_indep 18 R 6 -> False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
prove False.
apply vertex_has_12_nonneighbors R Hsym Htf Hno6 0 zero_in_18.
let T. assume HT: T c= 18 /\ equip 12 T /\ (forall t :e T, ~R 0 t) /\ 0 /:e T.
apply and4E (T c= 18) (equip 12 T) (forall t :e T, ~R 0 t) (0 /:e T) HT False.
assume HTV: T c= 18.
assume HT12: equip 12 T.
assume HT_nonadj: forall t :e T, ~R 0 t.
assume H0notinT: 0 /:e T.
apply non_neighbors_contain_4indep R Hsym Htf 0 zero_in_18 T HTV HT12 HT_nonadj.
let S. assume HS: S c= T /\ equip 4 S /\ is_indep_set 18 R S.
apply and3E (S c= T) (equip 4 S) (is_indep_set 18 R S) HS False.
assume HST: S c= T.
assume HS4: equip 4 S.
assume HS_indep: is_indep_set 18 R S.
claim HS18: S c= 18.
  let s. assume Hs: s :e S.
  exact HTV s (HST s Hs).
claim HS_nonadj0: forall s :e S, ~R 0 s.
  let s. assume Hs: s :e S.
  exact HT_nonadj s (HST s Hs).
claim HS_nonadj0_sym: forall s :e S, ~R s 0.
  let s. assume Hs: s :e S.
  assume HRs0: R s 0.
  apply HS_nonadj0 s Hs.
  exact Hsym s 0 HRs0.
claim H0notinS: 0 /:e S.
  assume H0S: 0 :e S.
  apply H0notinT.
  exact HST 0 H0S.
exact can_extend_4indep_with_nonneighbor R Hsym Htf Hno6 0 zero_in_18 S HS18 HS4
      HS_nonadj0 HS_nonadj0_sym HS_indep H0notinS.
Qed.

Definition TwoRamseyProp : set -> set -> set -> prop
 := fun M N V =>
      forall R:set -> set -> prop,
        (forall x y, R x y -> R y x)
       -> ((exists X, X c= V /\ equip M X /\ (forall x :e X, forall y :e X, x <> y -> R x y))
        \/ (exists Y, Y c= V /\ equip N Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y))).

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
  prove equip 3 S.
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
- prove forall x :e S, forall y :e S, x <> y -> ~R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) Hindep.
Qed.

Theorem R_18_irrefl : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  forall x :e 18, ~R x x.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
let x. assume Hx: x :e 18.
assume Hxx: R x x.
exact Htf x Hx x Hx x Hx Hxx Hxx Hxx.
Qed.

Theorem upper_bound_with_irrefl : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  (forall x :e 18, ~R x x) ->
  ((exists X, X c= 18 /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y))
   \/ (exists Y, Y c= 18 /\ equip 6 Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y))).
let R: set -> set -> prop.
assume Rsym: forall x y, R x y -> R y x.
assume Rirrefl: forall x :e 18, ~R x x.
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
  exact triangle_witness_from_neg 18 R Rirrefl Rsym Hntf.
Qed.
