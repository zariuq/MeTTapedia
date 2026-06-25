Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
Infix /\ 780 left := and.

Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
End Eq.
Infix = 502 := eq.

Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.
Binder+ exists , := ex.

Parameter In:set->set->prop.
Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.
Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.

Axiom In_ind : forall P:set->prop, (forall X:set, (forall x :e X, P x) -> P X) -> forall X:set, P X.

Theorem Subq_refl : forall X:set, X c= X.
let X x.
assume H: x :e X.
exact H.
Qed.

Theorem set_ext_self : forall X:set, X = X.
let X.
apply set_ext X X.
exact (Subq_refl X).
exact (Subq_refl X).
Qed.

Theorem no_self_mem : forall x:set, ~ (x :e x).
claim L: forall X:set, (forall y :e X, ~ (y :e y)) -> ~ (X :e X).
{
  let X.
  assume IH: forall y :e X, ~ (y :e y).
  assume HX: X :e X.
  prove False.
  exact (IH X HX HX).
}
exact (In_ind (fun X:set => ~ (X :e X)) L).
Qed.
