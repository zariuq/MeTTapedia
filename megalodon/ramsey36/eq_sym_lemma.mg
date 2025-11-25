Theorem eq_sym : forall x y:set, x = y -> y = x.
let x. let y.
assume Hxy: x = y.
prove y = x.
prove forall Q: set -> set -> prop, Q y x -> Q x y.
let Q: set -> set -> prop.
assume Hqyx: Q y x.
exact Hxy (fun a b => Q b a) Hqyx.
Qed.

Theorem eq_sym_test : forall v:set, forall x y:set,
  x :e {v} ->
  y :e {v} ->
  x = y.
let v. let x. let y.
assume Hxv: x :e {v}.
assume Hyv: y :e {v}.
claim Hxeqv: x = v.
  exact SingE v x Hxv.
claim Hyeqv: y = v.
  exact SingE v y Hyv.
claim Hveqy: v = y.
  exact eq_sym y v Hyeqv.
exact eq_i_tra x v y Hxeqv Hveqy.
Qed.
