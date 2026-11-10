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

Theorem Predicate2_pair : forall P:set -> set -> prop, forall x y,
  P x y -> P (proj0 (setsum x y)) (proj1 (setsum x y)).
let P x y. rewrite proj0_pair_eq x y. rewrite proj1_pair_eq x y.
assume H: P x y. exact H.
Qed.

Theorem Predicate2_unpair : forall P:set -> set -> prop, forall x y,
  P (proj0 (setsum x y)) (proj1 (setsum x y)) -> P x y.
let P x y. rewrite proj0_pair_eq x y. rewrite proj1_pair_eq x y.
assume H: P x y. exact H.
Qed.

(** Pointwise conversion under a bounded dependent-function binder. **)
Theorem Pi_family_eq : forall X, forall Y Z : set -> set,
  (forall x :e X, Y x = Z x) -> Pi X Y = Pi X Z.
let X Y Z. assume H: forall x :e X, Y x = Z x.
claim HYZ: forall x :e X, Y x c= Z x.
{ let x. assume Hx: x :e X. rewrite H x Hx. exact Subq_ref (Z x). }
claim HZY: forall x :e X, Z x c= Y x.
{ let x. assume Hx: x :e X. rewrite H x Hx. exact Subq_ref (Z x). }
apply set_ext.
- exact Pi_cod_mon X Y Z HYZ.
- exact Pi_cod_mon X Z Y HZY.
Qed.

(** Bounded set-valued lambdas are Sigma graphs in the interpretation. **)
Theorem Sigma_family_eq : forall X, forall Y Z : set -> set,
  (forall x :e X, Y x = Z x) -> Sigma X Y = Sigma X Z.
let X Y Z. assume H: forall x :e X, Y x = Z x.
claim HYZ: forall x :e X, Y x c= Z x.
{ let x. assume Hx: x :e X. rewrite H x Hx. exact Subq_ref (Z x). }
claim HZY: forall x :e X, Z x c= Y x.
{ let x. assume Hx: x :e X. rewrite H x Hx. exact Subq_ref (Z x). }
apply set_ext.
- exact Sigma_mon1 X Y Z HYZ.
- exact Sigma_mon1 X Z Y HZY.
Qed.
