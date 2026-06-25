Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.

Prefix ~ 700 := not.

Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
Infix /\ 780 left := and.

Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.

Theorem TrueI : True.
exact (fun p H => H).
Qed.

Theorem andI : forall A B:prop, A -> B -> A /\ B.
exact (fun A B a b p H => H a b).
Qed.

Theorem andEL : forall A B:prop, A /\ B -> A.
exact (fun A B H => H A (fun a b => a)).
Qed.

Theorem andER : forall A B:prop, A /\ B -> B.
exact (fun A B H => H B (fun a b => b)).
Qed.

Theorem orIL : forall A B:prop, A -> A \/ B.
exact (fun A B a p H1 H2 => H1 a).
Qed.

Theorem orIR : forall A B:prop, B -> A \/ B.
exact (fun A B b p H1 H2 => H2 b).
Qed.

Theorem FalseE : False -> forall p:prop, p.
exact (fun H => H).
Qed.
