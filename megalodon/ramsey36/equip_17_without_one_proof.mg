Theorem eq_sym : forall x y:set, x = y -> y = x.
let x. let y.
assume Hxy: x = y.
prove y = x.
prove forall Q: set -> set -> prop, Q y x -> Q x y.
let Q: set -> set -> prop.
assume Hqyx: Q y x.
exact Hxy (fun a b => Q b a) Hqyx.
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13 (nat_ordsucc 12 (nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))))))))))).
Qed.

Theorem ordinal_17 : ordinal 17.
exact nat_p_ordinal 17 nat_p_17.
Qed.

Theorem ordinal_18 : ordinal 18.
exact nat_p_ordinal 18 (nat_ordsucc 17 nat_p_17).
Qed.

Theorem In_17_18 : 17 :e 18.
prove 17 :e ordsucc 17.
exact ordsuccI2 17.
Qed.

Theorem ordsucc_setminus_singleton_base : forall n:set, ordinal n -> ordsucc n :\: {n} = n.
let n.
assume Hn: ordinal n.
prove ordsucc n :\: {n} = n.
apply set_ext.
- prove ordsucc n :\: {n} c= n.
  let x. assume Hx: x :e ordsucc n :\: {n}.
  apply setminusE (ordsucc n) {n} x Hx.
  assume Hx_succ: x :e ordsucc n.
  assume Hx_notn: x /:e {n}.
  apply ordsuccE n x Hx_succ.
  + assume Hx_n: x :e n.
    exact Hx_n.
  + assume Hx_eq: x = n.
    apply Hx_notn.
    prove x :e {n}.
    rewrite Hx_eq.
    exact SingI n.
- prove n c= ordsucc n :\: {n}.
  let x. assume Hx: x :e n.
  apply setminusI (ordsucc n) {n} x.
  + prove x :e ordsucc n.
    exact ordsuccI1 n x Hx.
  + prove x /:e {n}.
    assume Hxn: x :e {n}.
    claim Hxeqn: x = n.
      exact SingE n x Hxn.
    claim Hnn: n :e n.
      rewrite <- Hxeqn at 1.
      exact Hx.
    exact In_irref n Hnn.
Qed.

Theorem equip_17_without_17 : equip 17 (18 :\: {17}).
prove equip 17 (ordsucc 17 :\: {17}).
rewrite ordsucc_setminus_singleton_base 17 ordinal_17.
exact equip_ref 17.
Qed.

Definition shift_at : set -> set -> set := fun v x => if x :e v then x else ordsucc x.

Theorem shift_at_maps_to_succ_minus_v : forall v :e 17, forall x :e 17, shift_at v x :e 18 :\: {v}.
let v. assume Hv: v :e 17.
let x. assume Hx: x :e 17.
prove shift_at v x :e 18 :\: {v}.
prove (if x :e v then x else ordsucc x) :e 18 :\: {v}.
apply xm (x :e v).
- assume Hxv: x :e v.
  claim Hif: (if x :e v then x else ordsucc x) = x.
    exact If_i_1 (x :e v) x (ordsucc x) Hxv.
  rewrite Hif.
  prove x :e 18 :\: {v}.
  apply setminusI 18 {v} x.
  + prove x :e 18.
    exact ordsuccI1 17 x Hx.
  + prove x /:e {v}.
    assume Hxv_sing: x :e {v}.
    claim Hxeqv: x = v.
      exact SingE v x Hxv_sing.
    claim Hvv: v :e v.
      rewrite <- Hxeqv at 1.
      exact Hxv.
    exact In_irref v Hvv.
- assume Hxv_not: x /:e v.
  claim Hif: (if x :e v then x else ordsucc x) = ordsucc x.
    exact If_i_0 (x :e v) x (ordsucc x) Hxv_not.
  rewrite Hif.
  prove ordsucc x :e 18 :\: {v}.
  apply setminusI 18 {v} (ordsucc x).
  + prove ordsucc x :e 18.
    prove ordsucc x :e ordsucc 17.
    exact ordinal_ordsucc_In 17 ordinal_17 x Hx.
  + prove ordsucc x /:e {v}.
    assume Hsx_v: ordsucc x :e {v}.
    claim Hsx_eq_v: ordsucc x = v.
      exact SingE v (ordsucc x) Hsx_v.
    claim Hx_in_v: x :e v.
      exact Hsx_eq_v (fun a b => x :e a) (ordsuccI2 x).
    exact Hxv_not Hx_in_v.
Qed.

Theorem shift_at_injective : forall v :e 17, forall x y :e 17, shift_at v x = shift_at v y -> x = y.
let v. assume Hv: v :e 17.
let x. assume Hx: x :e 17.
let y. assume Hy: y :e 17.
assume Heq: shift_at v x = shift_at v y.
prove x = y.
apply xm (x :e v).
- assume Hxv: x :e v.
  apply xm (y :e v).
  + assume Hyv: y :e v.
    claim Hfx: shift_at v x = x.
      exact If_i_1 (x :e v) x (ordsucc x) Hxv.
    claim Hfy: shift_at v y = y.
      exact If_i_1 (y :e v) y (ordsucc y) Hyv.
    claim Hxy: x = y.
      exact eq_i_tra x (shift_at v x) y (eq_sym (shift_at v x) x Hfx) (eq_i_tra (shift_at v x) (shift_at v y) y Heq Hfy).
    exact Hxy.
  + assume Hyv_not: y /:e v.
    claim Hfx: shift_at v x = x.
      exact If_i_1 (x :e v) x (ordsucc x) Hxv.
    claim Hfy: shift_at v y = ordsucc y.
      exact If_i_0 (y :e v) y (ordsucc y) Hyv_not.
    claim Heq2: x = ordsucc y.
      exact eq_i_tra x (shift_at v x) (ordsucc y) (eq_sym (shift_at v x) x Hfx) (eq_i_tra (shift_at v x) (shift_at v y) (ordsucc y) Heq Hfy).
    claim Hy_in_x: y :e x.
      exact Heq2 (fun a b => y :e b) (ordsuccI2 y).
    claim Hord_v: ordinal v.
      exact nat_p_ordinal v (nat_p_trans 17 nat_p_17 v Hv).
    claim Hord_y: ordinal y.
      exact nat_p_ordinal y (nat_p_trans 17 nat_p_17 y Hy).
    claim Hord_x: ordinal x.
      exact nat_p_ordinal x (nat_p_trans 17 nat_p_17 x Hx).
    claim Hy_in_v: y :e v.
      exact (ordinal_TransSet v Hord_v) x Hxv y Hy_in_x.
    exact FalseE (Hyv_not Hy_in_v) (x = y).
- assume Hxv_not: x /:e v.
  apply xm (y :e v).
  + assume Hyv: y :e v.
    claim Hfx: shift_at v x = ordsucc x.
      exact If_i_0 (x :e v) x (ordsucc x) Hxv_not.
    claim Hfy: shift_at v y = y.
      exact If_i_1 (y :e v) y (ordsucc y) Hyv.
    claim Heq2: ordsucc x = y.
      exact eq_i_tra (ordsucc x) (shift_at v x) y (eq_sym (shift_at v x) (ordsucc x) Hfx) (eq_i_tra (shift_at v x) (shift_at v y) y Heq Hfy).
    claim Hx_in_y: x :e y.
      exact Heq2 (fun a b => x :e a) (ordsuccI2 x).
    claim Hord_v: ordinal v.
      exact nat_p_ordinal v (nat_p_trans 17 nat_p_17 v Hv).
    claim Hx_in_v: x :e v.
      exact (ordinal_TransSet v Hord_v) y Hyv x Hx_in_y.
    exact FalseE (Hxv_not Hx_in_v) (x = y).
  + assume Hyv_not: y /:e v.
    claim Hfx: shift_at v x = ordsucc x.
      exact If_i_0 (x :e v) x (ordsucc x) Hxv_not.
    claim Hfy: shift_at v y = ordsucc y.
      exact If_i_0 (y :e v) y (ordsucc y) Hyv_not.
    claim Heq2: ordsucc x = ordsucc y.
      exact eq_i_tra (ordsucc x) (shift_at v x) (ordsucc y) (eq_sym (shift_at v x) (ordsucc x) Hfx) (eq_i_tra (shift_at v x) (shift_at v y) (ordsucc y) Heq Hfy).
    exact ordsucc_inj x y Heq2.
Qed.

Theorem shift_at_surjective : forall v :e 17, forall z :e 18 :\: {v}, exists x :e 17, shift_at v x = z.
let v. assume Hv: v :e 17.
let z. assume Hz: z :e 18 :\: {v}.
prove exists x :e 17, shift_at v x = z.
claim Hz18: z :e 18.
  exact setminusE1 18 {v} z Hz.
claim Hzv: z /:e {v}.
  exact setminusE2 18 {v} z Hz.
claim Hzneqv: z <> v.
  assume Hzeqv: z = v.
  apply Hzv.
  rewrite Hzeqv.
  exact SingI v.
claim Hord_v: ordinal v.
  exact nat_p_ordinal v (nat_p_trans 17 nat_p_17 v Hv).
claim Hord_z: ordinal z.
  exact nat_p_ordinal z (nat_p_trans 18 (nat_ordsucc 17 nat_p_17) z Hz18).
apply xm (z :e v).
- assume Hzv_in: z :e v.
  witness z.
  apply andI (z :e 17) (shift_at v z = z).
  + prove z :e 17.
    exact nat_trans 17 nat_p_17 v Hv z Hzv_in.
  + prove shift_at v z = z.
    prove (if z :e v then z else ordsucc z) = z.
    exact If_i_1 (z :e v) z (ordsucc z) Hzv_in.
- assume Hzv_not: z /:e v.
  claim Hz_gt_v: v :e z \/ v = z.
  {
    apply ordinal_In_Or_Subq v z Hord_v Hord_z.
    - assume Hvz: v :e z.
      exact orIL (v :e z) (v = z) Hvz.
    - assume Hzv_sub: z c= v.
      apply xm (v = z).
      + assume Heq: v = z.
        exact orIR (v :e z) (v = z) Heq.
      + assume Hneq: v <> z.
        apply ordinal_In_Or_Subq z v Hord_z Hord_v.
        * assume Hzv': z :e v. exact FalseE (Hzv_not Hzv') (v :e z \/ v = z).
        * assume Hvz_sub: v c= z.
          apply orIR (v :e z) (v = z).
          exact set_ext v z Hvz_sub Hzv_sub.
  }
  apply Hz_gt_v.
  + assume Hvz: v :e z.
    claim Hz_nat: nat_p z.
      exact nat_p_trans 18 (nat_ordsucc 17 nat_p_17) z Hz18.
    claim Hz_inv: z = 0 \/ exists x:set, nat_p x /\ z = ordsucc x.
      exact nat_inv z Hz_nat.
    apply Hz_inv.
    + assume Hz0: z = 0.
      claim Hv0: v :e 0.
        exact Hz0 (fun a b => v :e a) Hvz.
      exact FalseE (EmptyE v Hv0) (exists x :e 17, shift_at v x = z).
    + assume Hz_ex: exists x:set, nat_p x /\ z = ordsucc x.
      apply Hz_ex.
      let w. assume Hw: nat_p w /\ z = ordsucc w.
      apply Hw.
      assume Hw_nat: nat_p w.
      assume Hweq: z = ordsucc w.
      claim Hwz: w :e z.
        exact (eq_sym z (ordsucc w) Hweq) (fun a b => w :e a) (ordsuccI2 w).
      witness w.
      apply andI (w :e 17) (shift_at v w = z).
      - prove w :e 17.
        claim Hw18: ordsucc w :e 18.
          exact Hweq (fun a b => a :e 18) Hz18.
        apply ordsuccE 17 (ordsucc w) Hw18.
        * assume Hsw17: ordsucc w :e 17.
          exact nat_trans 17 nat_p_17 (ordsucc w) Hsw17 w (ordsuccI2 w).
        * assume Hsw_eq: ordsucc w = 17.
          exact ordsucc_inj w 16 Hsw_eq (fun a b => b :e 17) (ordsuccI2 16).
      - prove shift_at v w = z.
        prove (if w :e v then w else ordsucc w) = z.
        claim Hw_notin_v: w /:e v.
        {
          assume Hwv: w :e v.
          claim Hord_sw: ordinal (ordsucc w).
            exact ordinal_ordsucc w (nat_p_ordinal w (nat_p_trans z Hz_nat w Hwz)).
          claim Hsw_in_v: ordsucc w :e v \/ ordsucc w = v.
          {
            apply ordinal_In_Or_Subq (ordsucc w) v Hord_sw Hord_v.
            - assume Hswv: ordsucc w :e v.
              exact orIL (ordsucc w :e v) (ordsucc w = v) Hswv.
            - assume Hv_sw: v c= ordsucc w.
              apply orIR (ordsucc w :e v) (ordsucc w = v).
              claim Hsw_sub_v: ordsucc w c= v.
              {
                let y. assume Hy: y :e ordsucc w.
                apply ordsuccE w y Hy.
                + assume Hyw: y :e w.
                  exact (ordinal_TransSet v Hord_v) w Hwv y Hyw.
                + assume Hyeqw: y = w.
                  exact Hyeqw (fun a b => b :e v) Hwv.
              }
              exact set_ext (ordsucc w) v Hsw_sub_v Hv_sw.
          }
          apply Hsw_in_v.
          - assume Hswv: ordsucc w :e v.
            claim Hzv': z :e v.
              exact Hweq (fun a b => b :e v) Hswv.
            exact Hzv_not Hzv'.
          - assume Hsweqv: ordsucc w = v.
            claim Hzeqv': z = v.
              exact eq_i_tra z (ordsucc w) v Hweq Hsweqv.
            exact Hzneqv Hzeqv'.
        }
        claim Hif_val: (if w :e v then w else ordsucc w) = ordsucc w.
          exact If_i_0 (w :e v) w (ordsucc w) Hw_notin_v.
        exact eq_i_tra (if w :e v then w else ordsucc w) (ordsucc w) z Hif_val (eq_sym z (ordsucc w) Hweq).
  + assume Hveqz: v = z.
    apply FalseE.
    exact Hzneqv (eq_sym v z Hveqz).
Qed.

Theorem equip_17_without_v_small : forall v :e 17, equip 17 (18 :\: {v}).
let v. assume Hv: v :e 17.
prove equip 17 (18 :\: {v}).
prove exists f:set->set, (forall x :e 17, f x :e 18 :\: {v}) /\ (forall x y :e 17, f x = f y -> x = y) /\ (forall z :e 18 :\: {v}, exists x :e 17, f x = z).
witness (shift_at v).
apply and3I (forall x :e 17, shift_at v x :e 18 :\: {v}) (forall x y :e 17, shift_at v x = shift_at v y -> x = y) (forall z :e 18 :\: {v}, exists x :e 17, shift_at v x = z).
- exact shift_at_maps_to_succ_minus_v v Hv.
- exact shift_at_injective v Hv.
- exact shift_at_surjective v Hv.
Qed.

Theorem equip_17_without_one : forall v :e 18, equip 17 (18 :\: {v}).
let v. assume Hv: v :e 18.
prove equip 17 (18 :\: {v}).
apply ordsuccE 17 v Hv.
- assume Hv17: v :e 17.
  exact equip_17_without_v_small v Hv17.
- assume Hv_eq_17: v = 17.
  rewrite Hv_eq_17.
  exact equip_17_without_17.
Qed.
