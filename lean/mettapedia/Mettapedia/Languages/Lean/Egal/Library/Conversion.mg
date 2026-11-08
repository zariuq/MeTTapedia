(** Conversion: membership and inclusion carried along equations.  Loaded
    before the general construction, which uses it. **)

Theorem In_eq_l : forall x y z, x = y -> x :e z -> y :e z.
let x y z. assume H: x = y. assume Hx: x :e z.
rewrite <- H. exact Hx.
Qed.

Theorem In_eq_r : forall x y z, y = z -> x :e y -> x :e z.
let x y z. assume H: y = z. assume Hx: x :e y.
rewrite <- H. exact Hx.
Qed.

Theorem In_eq_ls : forall x y z, x = y -> y :e z -> x :e z.
let x y z. assume H: x = y. assume Hy: y :e z.
rewrite H. exact Hy.
Qed.

Theorem Subq_eq_l : forall y z w, y = z -> z c= w -> y c= w.
let y z w. assume H: y = z. assume Hz: z c= w.
rewrite H. exact Hz.
Qed.

Theorem eq_sym_i : forall x y, x = y -> y = x.
let x y. assume H: x = y. rewrite H. reflexivity.
Qed.

Theorem In_fam_eq : forall F:set -> set, forall i i', i = i' -> forall x, x :e F i -> x :e F i'.
let F i i'. assume H: i = i'.
rewrite <- H. let x. assume Hx: x :e F i. exact Hx.
Qed.
