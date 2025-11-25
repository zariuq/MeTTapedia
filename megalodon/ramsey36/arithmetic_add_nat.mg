Theorem nat_p_3 : nat_p 3.
exact nat_ordsucc 2 nat_2.
Qed.

Theorem nat_p_4 : nat_p 4.
exact nat_ordsucc 3 nat_p_3.
Qed.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 nat_p_4.
Qed.

Theorem nat_p_6 : nat_p 6.
exact nat_ordsucc 5 nat_p_5.
Qed.

Theorem nat_p_7 : nat_p 7.
exact nat_ordsucc 6 nat_p_6.
Qed.

Theorem nat_p_8 : nat_p 8.
exact nat_ordsucc 7 nat_p_7.
Qed.

Theorem nat_p_9 : nat_p 9.
exact nat_ordsucc 8 nat_p_8.
Qed.

Theorem nat_p_10 : nat_p 10.
exact nat_ordsucc 9 nat_p_9.
Qed.

Theorem nat_p_11 : nat_p 11.
exact nat_ordsucc 10 nat_p_10.
Qed.

Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 nat_p_11.
Qed.

Theorem add_12_1 : add_nat 12 1 = 13.
prove add_nat 12 1 = 13.
prove add_nat 12 (ordsucc 0) = 13.
rewrite (add_nat_SR 12 0 nat_0).
prove ordsucc (add_nat 12 0) = 13.
rewrite (add_nat_0R 12).
Qed.

Theorem add_12_2 : add_nat 12 2 = 14.
prove add_nat 12 2 = 14.
rewrite (add_nat_SR 12 1 nat_1).
prove ordsucc (add_nat 12 1) = 14.
rewrite add_12_1.
Qed.

Theorem add_12_3 : add_nat 12 3 = 15.
prove add_nat 12 3 = 15.
rewrite (add_nat_SR 12 2 nat_2).
rewrite add_12_2.
Qed.

Theorem add_12_4 : add_nat 12 4 = 16.
prove add_nat 12 4 = 16.
rewrite (add_nat_SR 12 3 nat_p_3).
rewrite add_12_3.
Qed.

Theorem add_12_5 : add_nat 12 5 = 17.
prove add_nat 12 5 = 17.
rewrite (add_nat_SR 12 4 nat_p_4).
rewrite add_12_4.
Qed.

Theorem add_5_12_is_17 : add_nat 5 12 = 17.
prove add_nat 5 12 = 17.
rewrite (add_nat_com 5 12 nat_p_5 nat_p_12).
exact add_12_5.
Qed.
