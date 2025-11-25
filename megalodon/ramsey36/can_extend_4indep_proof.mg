Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Axiom vertex_has_12_nonneighbors : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.

Theorem indep_add_vertex : forall V:set, forall R:set -> set -> prop,
  forall S v:set,
  is_indep_set V R S ->
  v :e V ->
  v /:e S ->
  (forall s :e S, ~R v s) ->
  (forall s :e S, ~R s v) ->
  is_indep_set V R (S :\/: {v}).
let V. let R: set -> set -> prop. let S. let v.
assume HS: is_indep_set V R S.
assume HvV: v :e V.
assume HvnotS: v /:e S.
assume Hvnonadj: forall s :e S, ~R v s.
assume Hnonadjv: forall s :e S, ~R s v.
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
