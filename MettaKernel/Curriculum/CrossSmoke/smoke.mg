Definition False : prop := forall p:prop, p.
Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
Infix /\ 780 left := and.
Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
End Eq.
Infix = 502 := eq.

Theorem imp_id : forall P:prop, P -> P.
let P. assume p: P. exact p.
Qed.
Theorem and_elim_l : forall P Q:prop, P /\ Q -> P.
let P Q. assume h: P /\ Q. exact (h P (fun p q => p)).
Qed.
Theorem ex_falso : forall P:prop, False -> P.
let P. assume f: False. exact (f P).
Qed.
Theorem eq_refl_set : forall a:set, a = a.
let a. exact (fun Q h => h).
Qed.
