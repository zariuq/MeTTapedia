Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Theorem eq_sym : forall x y:set, x = y -> y = x.
let x. let y.
assume Hxy: x = y.
prove forall Q: set -> set -> prop, Q y x -> Q x y.
let Q: set -> set -> prop.
assume Hqyx: Q y x.
exact Hxy (fun a b => Q b a) Hqyx.
Qed.

Theorem indep_add_vertex : forall V:set, forall R:set -> set -> prop,
  forall S v:set,
  is_indep_set V R S ->
  v :e V ->
  v /:e S ->
  (forall s :e S, ~R v s) ->
  (forall s :e S, ~R s v) ->
  is_indep_set V R (S :\/: {v}).
let V. let R: set -> set -> prop.
let S. let v.
assume HS_indep: is_indep_set V R S.
assume HvV: v :e V.
assume Hv_notin_S: v /:e S.
assume Hnonadj1: forall s :e S, ~R v s.
assume Hnonadj2: forall s :e S, ~R s v.
claim HSV: S c= V.
  exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) HS_indep.
claim HS_pairs: forall x :e S, forall y :e S, x <> y -> ~R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) HS_indep.
prove is_indep_set V R (S :\/: {v}).
apply andI (S :\/: {v} c= V) (forall x :e S :\/: {v}, forall y :e S :\/: {v}, x <> y -> ~R x y).
- prove S :\/: {v} c= V.
  let x. assume Hx: x :e S :\/: {v}.
  apply binunionE S {v} x Hx.
  + assume HxS: x :e S.
    exact HSV x HxS.
  + assume Hxv: x :e {v}.
    claim Hxeqv: x = v.
      exact SingE v x Hxv.
    rewrite Hxeqv.
    exact HvV.
- prove forall x :e S :\/: {v}, forall y :e S :\/: {v}, x <> y -> ~R x y.
  let x. assume Hx: x :e S :\/: {v}.
  let y. assume Hy: y :e S :\/: {v}.
  assume Hneq: x <> y.
  apply binunionE S {v} x Hx.
  + assume HxS: x :e S.
    apply binunionE S {v} y Hy.
    * assume HyS: y :e S.
      exact HS_pairs x HxS y HyS Hneq.
    * assume Hyv: y :e {v}.
      claim Hyeqv: y = v.
        exact SingE v y Hyv.
      rewrite Hyeqv.
      exact Hnonadj2 x HxS.
  + assume Hxv: x :e {v}.
    claim Hxeqv: x = v.
      exact SingE v x Hxv.
    rewrite Hxeqv.
    apply binunionE S {v} y Hy.
    * assume HyS: y :e S.
      exact Hnonadj1 y HyS.
    * assume Hyv: y :e {v}.
      apply Hneq.
      claim Hxeqv2: x = v. exact SingE v x Hxv.
      claim Hyeqv2: y = v. exact SingE v y Hyv.
      claim Hveqy: v = y. exact eq_sym y v Hyeqv2.
      exact eq_i_tra x v y Hxeqv2 Hveqy.
Qed.
