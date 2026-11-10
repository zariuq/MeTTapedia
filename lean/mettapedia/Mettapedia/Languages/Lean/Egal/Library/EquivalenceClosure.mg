(** The least equivalence relation containing a relation on its carrier. **)

Definition LeanEqvClosure : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun X R x y => forall S : set -> set -> prop,
    (forall a :e X, S a a) ->
    (forall a b :e X, S a b -> S b a) ->
    (forall a b c :e X, S a b -> S b c -> S a c) ->
    (forall a b :e X, R a b -> S a b) -> S x y.

Theorem LeanEqvClosure_refl : forall X, forall R : set -> set -> prop,
  forall x :e X, LeanEqvClosure X R x x.
let X R x. assume Hx: x :e X. let S.
assume Hrefl: forall a :e X, S a a.
assume Hsym: forall a b :e X, S a b -> S b a.
assume Htrans: forall a b c :e X, S a b -> S b c -> S a c.
assume Hedge: forall a b :e X, R a b -> S a b.
exact Hrefl x Hx.
Qed.

Theorem LeanEqvClosure_symm : forall X, forall R : set -> set -> prop,
  forall x y :e X, LeanEqvClosure X R x y -> LeanEqvClosure X R y x.
let X R x. assume Hx: x :e X. let y. assume Hy: y :e X.
assume Hxy: LeanEqvClosure X R x y. let S.
assume Hrefl: forall a :e X, S a a.
assume Hsym: forall a b :e X, S a b -> S b a.
assume Htrans: forall a b c :e X, S a b -> S b c -> S a c.
assume Hedge: forall a b :e X, R a b -> S a b.
exact Hsym x Hx y Hy (Hxy S Hrefl Hsym Htrans Hedge).
Qed.

Theorem LeanEqvClosure_trans : forall X, forall R : set -> set -> prop,
  forall x y z :e X, LeanEqvClosure X R x y -> LeanEqvClosure X R y z -> LeanEqvClosure X R x z.
let X R x. assume Hx: x :e X. let y. assume Hy: y :e X. let z. assume Hz: z :e X.
assume Hxy: LeanEqvClosure X R x y. assume Hyz: LeanEqvClosure X R y z. let S.
assume Hrefl: forall a :e X, S a a.
assume Hsym: forall a b :e X, S a b -> S b a.
assume Htrans: forall a b c :e X, S a b -> S b c -> S a c.
assume Hedge: forall a b :e X, R a b -> S a b.
exact Htrans x Hx y Hy z Hz (Hxy S Hrefl Hsym Htrans Hedge) (Hyz S Hrefl Hsym Htrans Hedge).
Qed.

Theorem LeanEqvClosure_edge : forall X, forall R : set -> set -> prop,
  forall x y :e X, R x y -> LeanEqvClosure X R x y.
let X R x. assume Hx: x :e X. let y. assume Hy: y :e X. assume Hxy: R x y. let S.
assume Hrefl: forall a :e X, S a a.
assume Hsym: forall a b :e X, S a b -> S b a.
assume Htrans: forall a b c :e X, S a b -> S b c -> S a c.
assume Hedge: forall a b :e X, R a b -> S a b.
exact Hedge x Hx y Hy Hxy.
Qed.

Theorem LeanEqvClosure_respect : forall X, forall R : set -> set -> prop,
  forall f : set -> set, (forall x y :e X, R x y -> f x = f y) ->
  forall x y, LeanEqvClosure X R x y -> f x = f y.
let X R f. assume Hrespect: forall x y :e X, R x y -> f x = f y.
let x y. assume Hxy: LeanEqvClosure X R x y.
claim Hrefl: forall a :e X, f a = f a.
{ let a. assume Ha: a :e X. reflexivity. }
exact Hxy (fun a b => f a = f b) Hrefl
  (fun a Ha b Hb H => eq_sym_i (f a) (f b) H)
  (fun a Ha b Hb c Hc Hab Hbc => eq_i_tra (f a) (f b) (f c) Hab Hbc) Hrespect.
Qed.

Theorem LeanEqvClosure_already_equivalent : forall X, forall R : set -> set -> prop,
  (forall x :e X, R x x) ->
  (forall x y :e X, R x y -> R y x) ->
  (forall x y z :e X, R x y -> R y z -> R x z) ->
  forall x y, LeanEqvClosure X R x y -> R x y.
let X R. assume Hrefl: forall x :e X, R x x.
assume Hsym: forall x y :e X, R x y -> R y x.
assume Htrans: forall x y z :e X, R x y -> R y z -> R x z.
let x y. assume Hxy: LeanEqvClosure X R x y.
exact Hxy R Hrefl Hsym Htrans (fun a Ha b Hb H => H).
Qed.

(** The closure adds the reverse of a directed edge. **)
Theorem LeanEqvClosure_reverse_edge :
  LeanEqvClosure {0,1} (fun x y => x = 0 /\ y = 1) 1 0.
claim H01: 0 = 0 /\ 1 = 1.
{ apply andI.
  - reflexivity.
  - reflexivity. }
exact LeanEqvClosure_symm {0,1} (fun x y => x = 0 /\ y = 1)
  0 (UPairI1 0 1) 1 (UPairI2 0 1)
  (LeanEqvClosure_edge {0,1} (fun x y => x = 0 /\ y = 1)
    0 (UPairI1 0 1) 1 (UPairI2 0 1) H01).
Qed.

Theorem LeanEqvClosure_reverse_edge_not_original : ~(1 = 0 /\ 0 = 1).
assume H: 1 = 0 /\ 0 = 1.
exact neq_1_0 (andEL (1 = 0) (0 = 1) H).
Qed.

Theorem LeanEqvClosure_empty_distinguishes : ~ LeanEqvClosure {0,1} (fun x y => False) 0 1.
assume H: LeanEqvClosure {0,1} (fun x y => False) 0 1.
exact neq_0_1 (LeanEqvClosure_respect {0,1} (fun x y => False) (fun x => x)
  (fun x Hx y Hy Hfalse => FalseE Hfalse (x = y)) 0 1 H).
Qed.

(** Quotient classes and lifts for a relation that is not assumed equivalent. **)
Definition LeanRelationQuot : set -> (set -> set -> prop) -> set :=
  fun X R => LeanSetoidQuot X (LeanEqvClosure X R).
Definition LeanRelationClass : set -> (set -> set -> prop) -> set -> set :=
  fun X R x => LeanQuotClass X (LeanEqvClosure X R) x.

Theorem LeanRelationClass_typed : forall X, forall R : set -> set -> prop,
  forall x :e X, LeanRelationClass X R x :e LeanRelationQuot X R.
let X R. exact LeanQuotClass_typed X (LeanEqvClosure X R).
Qed.

Theorem LeanRelationClass_sound : forall X, forall R : set -> set -> prop,
  forall x y :e X, R x y -> LeanRelationClass X R x = LeanRelationClass X R y.
let X R x. assume Hx: x :e X. let y. assume Hy: y :e X. assume Hxy: R x y.
exact LeanQuotClass_sound X (LeanEqvClosure X R) (LeanEqvClosure_symm X R) (LeanEqvClosure_trans X R)
  x Hx y Hy (LeanEqvClosure_edge X R x Hx y Hy Hxy).
Qed.

Theorem LeanRelationLift_beta : forall X, forall R : set -> set -> prop,
  forall f : set -> set, (forall x y :e X, R x y -> f x = f y) ->
  forall x :e X, LeanQuotLift f (LeanRelationClass X R x) = f x.
let X R f. assume Hrespect: forall x y :e X, R x y -> f x = f y.
exact LeanQuotLift_beta X (LeanEqvClosure X R) (LeanEqvClosure_refl X R) f
  (fun x Hx y Hy Hxy => LeanEqvClosure_respect X R f Hrespect x y Hxy).
Qed.

Theorem LeanRelationLift_typed : forall X Y, forall R : set -> set -> prop,
  forall f : set -> set, (forall x y :e X, R x y -> f x = f y) ->
  (forall x :e X, f x :e Y) -> forall value :e LeanRelationQuot X R, LeanQuotLift f value :e Y.
let X Y R f. assume Hrespect: forall x y :e X, R x y -> f x = f y.
exact LeanQuotLift_typed X Y (LeanEqvClosure X R) (LeanEqvClosure_refl X R) f
  (fun x Hx y Hy Hxy => LeanEqvClosure_respect X R f Hrespect x y Hxy).
Qed.

Theorem LeanRelationClass_of_equivalence : forall X, forall R : set -> set -> prop,
  (forall x :e X, R x x) ->
  (forall x y :e X, R x y -> R y x) ->
  (forall x y z :e X, R x y -> R y z -> R x z) ->
  forall x :e X, LeanRelationClass X R x = LeanQuotClass X R x.
let X R. assume Hrefl: forall x :e X, R x x.
assume Hsym: forall x y :e X, R x y -> R y x.
assume Htrans: forall x y z :e X, R x y -> R y z -> R x z.
let x. assume Hx: x :e X. apply set_ext.
- let y. assume Hy: y :e LeanRelationClass X R x.
  exact LeanQuotClass_member X R x y (LeanQuotClass_carrier X (LeanEqvClosure X R) x y Hy)
    (LeanEqvClosure_already_equivalent X R Hrefl Hsym Htrans x y
      (LeanQuotClass_relation X (LeanEqvClosure X R) x y Hy)).
- let y. assume Hy: y :e LeanQuotClass X R x.
  exact LeanQuotClass_member X (LeanEqvClosure X R) x y (LeanQuotClass_carrier X R x y Hy)
    (LeanEqvClosure_edge X R x Hx y (LeanQuotClass_carrier X R x y Hy) (LeanQuotClass_relation X R x y Hy)).
Qed.
