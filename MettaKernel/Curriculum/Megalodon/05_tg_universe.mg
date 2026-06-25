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

Parameter In:set->set->prop.
Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.
Parameter Power : set->set.
Parameter Union : set->set.

Parameter UnivOf : set->set.
Axiom UnivOf_In : forall N:set, N :e UnivOf N.
Axiom UnivOf_Power : forall N X:set, X :e UnivOf N -> Power X :e UnivOf N.
Axiom UnivOf_Union : forall N X:set, X :e UnivOf N -> Union X :e UnivOf N.

Theorem univ_power_self : forall N:set, Power N :e UnivOf N.
let N.
exact (UnivOf_Power N N (UnivOf_In N)).
Qed.

Theorem univ_power_power : forall N:set, Power (Power N) :e UnivOf N.
let N.
exact (UnivOf_Power N (Power N) (UnivOf_Power N N (UnivOf_In N))).
Qed.

Theorem univ_union_power : forall N:set, Union (Power N) :e UnivOf N.
let N.
exact (UnivOf_Union N (Power N) (UnivOf_Power N N (UnivOf_In N))).
Qed.
