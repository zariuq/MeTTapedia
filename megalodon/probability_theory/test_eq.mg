Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
Definition neq : A->A->prop := fun x y:A => ~ eq x y.
End Eq.

Infix = 502 := eq.
Infix <> 502 := neq.

Theorem eq_ref : forall A:SType, forall x:A, x = x.
let A. let x.
assume Q.
assume H: Q x x.
exact H.
Qed.
