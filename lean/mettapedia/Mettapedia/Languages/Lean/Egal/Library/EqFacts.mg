(** Facts about Lean's equality in the set model. **)

(** Equality is sound: a proof of Eq A a b gives a = b. **)
Theorem LeanEq_sound : forall A a b, forall t :e Lean_Eq_Prop A a b, a = b.
let A a b t. assume Ht: t :e Lean_Eq_Prop A a b.
apply SepE2 1 (fun x:set => exists w, w :e Lean_Eq A a b) t Ht.
let w. assume Hw: w :e Lean_Eq A a b.
claim Hu: w = Lean_Eq_refl_node A a.
{ exact Lean_Eq_unique A a w (Lean_Eq_in_All A a b w Hw). }
claim Hr: Lean_Eq_refl_node A a :e Lean_Eq A a b.
{ exact In_eq_l w (Lean_Eq_refl_node A a) (Lean_Eq A a b) Hu Hw. }
exact Lean_Eq_one_index A a a b (Lean_Eq_refl_node A a) (Lean_Eq_refl_typed A a) Hr.
Qed.

(** And at different indices it is false. **)
Theorem control_eq_0_1_false : forall t, t /:e Lean_Eq_Prop omega 0 1.
let t. assume Ht: t :e Lean_Eq_Prop omega 0 1.
exact neq_0_1 (LeanEq_sound omega 0 1 t Ht).
Qed.

(** Equal values have a proof of their equation. **)
Theorem Lean_Eq_proof_of : forall A a b, a = b -> 0 :e Lean_Eq_Prop A a b.
let A a b. assume H: a = b.
rewrite <- H. exact Lean_Eq_refl_proof_ok A a.
Qed.

(** Pointwise equations give the proof value of a dependent product of equalities. **)
Theorem Lean_Eq_Pi1 : forall X A, forall f g:set -> set,
  (forall x :e X, f x = g x) -> 0 :e (Pi_ x :e X, Lean_Eq_Prop A (f x) (g x)).
let X A f g. assume H: forall x :e X, f x = g x.
exact Pi_0_In X (fun x => Lean_Eq_Prop A (f x) (g x))
  (fun x Hx => Lean_Eq_proof_of A (f x) (g x) (H x Hx)).
Qed.

Theorem Lean_Eq_Pi2 : forall X Y A, forall f g:set -> set -> set,
  (forall x :e X, forall y :e Y, f x y = g x y) ->
  0 :e (Pi_ x :e X, (Pi_ y :e Y, Lean_Eq_Prop A (f x y) (g x y))).
let X Y A f g. assume H: forall x :e X, forall y :e Y, f x y = g x y.
exact Pi_0_In X (fun x => Pi_ y :e Y, Lean_Eq_Prop A (f x y) (g x y))
  (fun x Hx => Lean_Eq_Pi1 Y A (f x) (g x) (fun y Hy => H x Hx y Hy)).
Qed.

Theorem Lean_Eq_Pi3 : forall X Y Z A, forall f g:set -> set -> set -> set,
  (forall x :e X, forall y :e Y, forall z :e Z, f x y z = g x y z) ->
  0 :e (Pi_ x :e X, (Pi_ y :e Y, (Pi_ z :e Z, Lean_Eq_Prop A (f x y z) (g x y z)))).
let X Y Z A f g. assume H: forall x :e X, forall y :e Y, forall z :e Z, f x y z = g x y z.
exact Pi_0_In X (fun x => Pi_ y :e Y, Pi_ z :e Z, Lean_Eq_Prop A (f x y z) (g x y z))
  (fun x Hx => Lean_Eq_Pi2 Y Z A (f x) (g x) (fun y Hy z Hz => H x Hx y Hy z Hz)).
Qed.
