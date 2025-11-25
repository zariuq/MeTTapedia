Definition DummyStart : prop := True.

Definition MyReal : set := Empty.
Definition R_zero : set := Empty.
Definition R_one : set := Empty.
Definition R_leq : set -> set -> prop := fun x y => True.
Definition R_plus : set -> set -> set := fun x y => Empty.
Infix <= 490 := R_leq.
Infix + 360 right := R_plus.

Definition sum_nat : (set -> set) -> set := fun f => Empty.

Axiom sum_nat_clos : forall f : set -> set, (forall n :e omega, f n :e MyReal /\ R_zero <= f n) -> sum_nat f :e MyReal.

Axiom sum_nat_zero : sum_nat (fun n => R_zero) = R_zero.

Axiom sum_nat_pair : forall a b :e MyReal,
  sum_nat (fun n => if n = R_zero then a else if n = R_one then b else R_zero) = a + b.
