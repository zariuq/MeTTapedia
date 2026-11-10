(** Setoid quotients as extensional classes. The relation laws hold on the
    carrier. An arbitrary relation needs its equivalence closure before this
    interface can interpret Lean's Quot. **)

Definition LeanQuotClass : set -> (set -> set -> prop) -> set -> set :=
  fun X R x => {y :e X | R x y}.

Definition LeanSetoidQuot : set -> (set -> set -> prop) -> set :=
  fun X R => {LeanQuotClass X R x | x :e X}.

Definition LeanQuotLift : (set -> set) -> set -> set :=
  fun f c => Union {f x | x :e c}.

Theorem LeanQuotClass_member : forall X, forall R:set -> set -> prop,
  forall x y, y :e X -> R x y -> y :e LeanQuotClass X R x.
let X R x y. assume Hy: y :e X. assume Hxy: R x y.
exact SepI X (R x) y Hy Hxy.
Qed.

Theorem LeanQuotClass_carrier : forall X, forall R:set -> set -> prop,
  forall x y, y :e LeanQuotClass X R x -> y :e X.
let X R x y. assume H: y :e LeanQuotClass X R x.
exact SepE1 X (R x) y H.
Qed.

Theorem LeanQuotClass_relation : forall X, forall R:set -> set -> prop,
  forall x y, y :e LeanQuotClass X R x -> R x y.
let X R x y. assume H: y :e LeanQuotClass X R x.
exact SepE2 X (R x) y H.
Qed.

Theorem LeanQuotClass_typed : forall X, forall R:set -> set -> prop,
  forall x :e X, LeanQuotClass X R x :e LeanSetoidQuot X R.
let X R x. assume Hx: x :e X.
exact ReplI X (LeanQuotClass X R) x Hx.
Qed.

Theorem LeanQuotClass_sound : forall X, forall R:set -> set -> prop,
  (forall x y :e X, R x y -> R y x) ->
  (forall x y z :e X, R x y -> R y z -> R x z) ->
  forall x y :e X, R x y -> LeanQuotClass X R x = LeanQuotClass X R y.
let X R. assume Hsym: forall x y :e X, R x y -> R y x.
assume Htrans: forall x y z :e X, R x y -> R y z -> R x z.
let x. assume Hx: x :e X. let y. assume Hy: y :e X. assume Hxy: R x y.
apply set_ext.
- let z. assume Hz: z :e LeanQuotClass X R x.
  exact LeanQuotClass_member X R y z (LeanQuotClass_carrier X R x z Hz)
    (Htrans y Hy x Hx z (LeanQuotClass_carrier X R x z Hz)
      (Hsym x Hx y Hy Hxy) (LeanQuotClass_relation X R x z Hz)).
- let z. assume Hz: z :e LeanQuotClass X R y.
  exact LeanQuotClass_member X R x z (LeanQuotClass_carrier X R y z Hz)
    (Htrans x Hx y Hy z (LeanQuotClass_carrier X R y z Hz)
      Hxy (LeanQuotClass_relation X R y z Hz)).
Qed.

Theorem LeanQuotClass_effective : forall X, forall R:set -> set -> prop,
  (forall x :e X, R x x) -> forall x y :e X,
  LeanQuotClass X R x = LeanQuotClass X R y -> R x y.
let X R. assume Hrefl: forall x :e X, R x x.
let x. assume Hx: x :e X. let y. assume Hy: y :e X.
assume H: LeanQuotClass X R x = LeanQuotClass X R y.
apply LeanQuotClass_relation X R x y.
rewrite H. exact LeanQuotClass_member X R y y Hy (Hrefl y Hy).
Qed.

(** The result is independent of the representative precisely when the
    operation respects the relation. No representative is selected. **)
Theorem LeanQuotLift_beta : forall X, forall R:set -> set -> prop,
  (forall x :e X, R x x) -> forall f:set -> set,
  (forall x y :e X, R x y -> f x = f y) ->
  forall x :e X, LeanQuotLift f (LeanQuotClass X R x) = f x.
let X R. assume Hrefl: forall x :e X, R x x. let f.
assume Hrespect: forall x y :e X, R x y -> f x = f y.
let x. assume Hx: x :e X.
apply set_ext.
- let z. assume Hz: z :e LeanQuotLift f (LeanQuotClass X R x).
  apply UnionE_impred {f y | y :e LeanQuotClass X R x} z Hz.
  let value. assume Hv: z :e value. assume Hvalue: value :e {f y | y :e LeanQuotClass X R x}.
  apply ReplE_impred (LeanQuotClass X R x) f value Hvalue.
  let y. assume Hy: y :e LeanQuotClass X R x. assume Heq: value = f y.
  rewrite (Hrespect x Hx y (LeanQuotClass_carrier X R x y Hy)
    (LeanQuotClass_relation X R x y Hy)).
  rewrite <- Heq. exact Hv.
- let z. assume Hz: z :e f x.
  exact UnionI {f y | y :e LeanQuotClass X R x} z (f x) Hz
    (ReplI (LeanQuotClass X R x) f x (LeanQuotClass_member X R x x Hx (Hrefl x Hx))).
Qed.

Theorem LeanQuotLift_typed : forall X Y, forall R:set -> set -> prop,
  (forall x :e X, R x x) -> forall f:set -> set,
  (forall x y :e X, R x y -> f x = f y) ->
  (forall x :e X, f x :e Y) -> forall c :e LeanSetoidQuot X R, LeanQuotLift f c :e Y.
let X Y R. assume Hrefl: forall x :e X, R x x. let f.
assume Hrespect: forall x y :e X, R x y -> f x = f y.
assume Htyped: forall x :e X, f x :e Y. let c. assume Hc: c :e LeanSetoidQuot X R.
apply ReplE_impred X (LeanQuotClass X R) c Hc.
let x. assume Hx: x :e X. assume Hclass: c = LeanQuotClass X R x.
rewrite Hclass. rewrite LeanQuotLift_beta X R Hrefl f Hrespect x Hx.
exact Htyped x Hx.
Qed.

Theorem LeanQuotLift_unique : forall X, forall R:set -> set -> prop,
  (forall x :e X, R x x) -> forall f g:set -> set,
  (forall x y :e X, R x y -> f x = f y) ->
  (forall x :e X, g (LeanQuotClass X R x) = f x) ->
  forall c :e LeanSetoidQuot X R, g c = LeanQuotLift f c.
let X R. assume Hrefl: forall x :e X, R x x. let f g.
assume Hrespect: forall x y :e X, R x y -> f x = f y.
assume Hbeta: forall x :e X, g (LeanQuotClass X R x) = f x.
let c. assume Hc: c :e LeanSetoidQuot X R.
apply ReplE_impred X (LeanQuotClass X R) c Hc.
let x. assume Hx: x :e X. assume Hclass: c = LeanQuotClass X R x.
rewrite Hclass. rewrite LeanQuotLift_beta X R Hrefl f Hrespect x Hx.
exact Hbeta x Hx.
Qed.

Theorem LeanQuotLift_requires_respect : forall X, forall R:set -> set -> prop,
  (forall x y :e X, R x y -> R y x) ->
  (forall x y z :e X, R x y -> R y z -> R x z) ->
  forall f g:set -> set, (forall x :e X, g (LeanQuotClass X R x) = f x) ->
  forall x y :e X, R x y -> f x = f y.
let X R. assume Hsym: forall x y :e X, R x y -> R y x.
assume Htrans: forall x y z :e X, R x y -> R y z -> R x z.
let f g. assume Hbeta: forall x :e X, g (LeanQuotClass X R x) = f x.
let x. assume Hx: x :e X. let y. assume Hy: y :e X. assume Hxy: R x y.
rewrite <- (Hbeta x Hx). rewrite <- (Hbeta y Hy).
rewrite (LeanQuotClass_sound X R Hsym Htrans x Hx y Hy Hxy).
reflexivity.
Qed.

(** A representative-observing function cannot be a quotient lift. **)
Theorem LeanQuot_no_representative_observer : forall g:set -> set,
  g (LeanQuotClass {0,1} (fun _ _ => True) 0) = 0 ->
  g (LeanQuotClass {0,1} (fun _ _ => True) 1) = 1 -> False.
let g. assume H0: g (LeanQuotClass {0,1} (fun _ _ => True) 0) = 0.
assume H1: g (LeanQuotClass {0,1} (fun _ _ => True) 1) = 1.
claim Hclass: LeanQuotClass {0,1} (fun _ _ => True) 0 =
  LeanQuotClass {0,1} (fun _ _ => True) 1.
{ exact LeanQuotClass_sound {0,1} (fun _ _ => True)
    (fun x Hx y Hy H => TrueI) (fun x Hx y Hy z Hz Hxy Hyz => TrueI)
    0 (UPairI1 0 1) 1 (UPairI2 0 1) TrueI. }
claim Hboth: g (LeanQuotClass {0,1} (fun _ _ => True) 0) = 1.
{ exact eq_i_tra (g (LeanQuotClass {0,1} (fun _ _ => True) 0))
    (g (LeanQuotClass {0,1} (fun _ _ => True) 1)) 1
    (f_eq_i g (LeanQuotClass {0,1} (fun _ _ => True) 0)
      (LeanQuotClass {0,1} (fun _ _ => True) 1) Hclass) H1. }
exact neq_0_1 (eq_i_tra 0 (g (LeanQuotClass {0,1} (fun _ _ => True) 0)) 1
  (eq_sym_i (g (LeanQuotClass {0,1} (fun _ _ => True) 0)) 0 H0) Hboth).
Qed.
