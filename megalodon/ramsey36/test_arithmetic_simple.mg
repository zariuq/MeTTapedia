Theorem nat_p_3 : nat_p 3.
exact nat_ordsucc 2 nat_2.
Qed.

Theorem test_1_plus_0 : 1 + 0 = 1.
prove 1 + 0 = 1.
exact (add_nat_0R 1).
Qed.

Theorem test_1_plus_1 : 1 + 1 = 2.
prove 1 + 1 = 2.
prove 1 + ordsucc 0 = 2.
exact (add_nat_SR 1 0 nat_0).
Qed.
