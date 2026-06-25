Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
Infix /\ 780 left := and.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.
Definition iff : prop -> prop -> prop := fun A B:prop => and (A -> B) (B -> A).
Infix <-> 805 := iff.

Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
Definition neq : A->A->prop := fun x y:A => ~ eq x y.
End Eq.
Infix = 502 := eq.
(* Unicode <> "2260" *)
Infix <> 502 := neq.

Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.
(* Unicode exists "2203" *)
Binder+ exists , := ex.

Axiom prop_ext : forall p q:prop, iff p q -> p = q.

Parameter In:set->set->prop.

Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.

Parameter Empty : set.
Axiom EmptyAx : ~exists x:set, x :e Empty.

(* Unicode Union "22C3" *)
Parameter Union : set->set.
Axiom UnionEq : forall X x, x :e Union X <-> exists Y, x :e Y /\ Y :e X.

(* Unicode Power "1D4AB" *)
Parameter Power : set->set.
Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.

Binder+ exists , := ex; and.

Theorem iffI : forall A B:prop, (A -> B) -> (B -> A) -> (A <-> B).
let A B.
assume H1: A -> B.
assume H2: B -> A.
prove (A -> B) /\ (B -> A).
exact (fun p H => H H1 H2).
Qed.

Theorem iffEL : forall A B:prop, (A <-> B) -> A -> B.
let A B.
assume H: (A -> B) /\ (B -> A).
apply H.
assume H1: A -> B.
assume _: B -> A.
exact H1.
Qed.

Theorem EmptyE : forall x:set, x :e Empty -> False.
let x.
assume H: x :e Empty.
apply EmptyAx.
witness x.
exact H.
Qed.

Theorem Subq_ref : forall X:set, X c= X.
let X x.
assume H: x :e X.
exact H.
Qed.

Theorem Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
let X Y Z.
assume H1: X c= Y.
assume H2: Y c= Z.
let x.
assume H: x :e X.
prove x :e Z.
exact (H2 x (H1 x H)).
Qed.

Theorem PowerI : forall X Y:set, Y c= X -> Y :e Power X.
let X Y.
assume H: Y c= X.
apply PowerEq X Y.
assume _ H2.
exact (H2 H).
Qed.

Theorem PowerE : forall X Y:set, Y :e Power X -> Y c= X.
let X Y.
assume H: Y :e Power X.
apply PowerEq X Y.
assume H1 _.
exact (H1 H).
Qed.

Theorem Empty_Subq : forall X:set, Empty c= X.
let X x.
assume H: x :e Empty.
prove False.
exact EmptyE x H.
Qed.
