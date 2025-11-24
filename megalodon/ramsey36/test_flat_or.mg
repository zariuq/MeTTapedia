Definition SimpleAdj4 : set -> set -> prop :=
  fun i j =>
    (i = 0 /\ j = 1) \/
    (i = 1 /\ j = 0) \/
    (i = 2 /\ j = 3) \/
    (i = 3 /\ j = 2).

Theorem SimpleAdj4_not_0_0 : ~SimpleAdj4 0 0.
assume H: SimpleAdj4 0 0.
prove False.
apply H.
- assume H1.
  apply H1.
  + assume H2.
    apply H2.
    * assume HD0.
      apply HD0.
      assume Heq1: 0 = 0.
      assume Heq2: 0 = 1.
      exact neq_0_1 Heq2.
    * assume HD1.
      apply HD1.
      assume Heq1: 0 = 1.
      assume Heq2: 0 = 0.
      exact neq_0_1 Heq1.
  + assume HD2.
    apply HD2.
    assume Heq1: 0 = 2.
    assume Heq2: 0 = 3.
    exact neq_0_2 Heq1.
- assume HD3.
  apply HD3.
  assume Heq1: 0 = 3.
  assume Heq2: 0 = 2.
  exact neq_0_3 Heq1.
Qed.
