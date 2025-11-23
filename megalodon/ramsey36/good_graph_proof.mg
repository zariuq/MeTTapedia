Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

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

Theorem has_triangle_or_4indep_on_9 : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  equip 9 V ->
  (exists x y z :e V, R x y /\ R y z /\ R x z) \/
  (exists S, S c= V /\ equip 4 S /\ is_indep_set V R S).
Admitted.

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

Theorem non_neighbors_contain_4indep : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  forall v :e 18, forall T:set,
    T c= 18 ->
    equip 12 T ->
    (forall t :e T, ~R v t) ->
    exists S, S c= T /\ equip 4 S /\ is_indep_set 18 R S.
Admitted.

Theorem vertex_has_12_nonneighbors : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
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
  ~triangle_free V R ->
  exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
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
  exact triangle_witness_from_neg 18 R Rirrefl Hntf.
Qed.
