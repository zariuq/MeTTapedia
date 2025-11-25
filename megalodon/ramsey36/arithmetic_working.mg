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

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 nat_p_12.
Qed.

Theorem nat_p_14 : nat_p 14.
exact nat_ordsucc 13 nat_p_13.
Qed.

Theorem nat_p_15 : nat_p 15.
exact nat_ordsucc 14 nat_p_14.
Qed.

Theorem nat_p_16 : nat_p 16.
exact nat_ordsucc 15 nat_p_15.
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 nat_p_16.
Qed.

Theorem add_12_1 : 12 + 1 = 13.
prove 12 + 1 = 13.
rewrite (add_nat_SR 12 0 nat_0).
rewrite (add_nat_0R 12).
exact (eq_i_refl (ordsucc 12)).
Qed.

Theorem add_12_2 : 12 + 2 = 14.
prove 12 + 2 = 14.
rewrite (add_nat_SR 12 1 nat_1).
rewrite add_12_1.
exact (eq_i_refl (ordsucc 13)).
Qed.

Theorem add_12_3 : 12 + 3 = 15.
prove 12 + 3 = 15.
rewrite (add_nat_SR 12 2 nat_2).
rewrite add_12_2.
exact (eq_i_refl (ordsucc 14)).
Qed.

Theorem add_12_4 : 12 + 4 = 16.
prove 12 + 4 = 16.
rewrite (add_nat_SR 12 3 nat_p_3).
rewrite add_12_3.
exact (eq_i_refl (ordsucc 15)).
Qed.

Theorem add_12_5 : 12 + 5 = 17.
prove 12 + 5 = 17.
rewrite (add_nat_SR 12 4 nat_p_4).
rewrite add_12_4.
exact (eq_i_refl (ordsucc 16)).
Qed.

Theorem add_5_12_is_17 : 5 + 12 = 17.
prove 5 + 12 = 17.
rewrite (add_nat_com 5 12 nat_p_5 nat_p_12).
exact add_12_5.
Qed.

Theorem add_0_17 : 0 + 17 = 17.
exact add_nat_0L 17 nat_p_17.
Qed.

Theorem add_17_1 : 17 + 1 = 18.
prove 17 + 1 = 18.
rewrite (add_nat_SR 17 0 nat_0).
rewrite (add_nat_0R 17).
exact (eq_i_refl (ordsucc 17)).
Qed.

Theorem add_16_1 : 16 + 1 = 17.
prove 16 + 1 = 17.
rewrite (add_nat_SR 16 0 nat_0).
rewrite (add_nat_0R 16).
exact (eq_i_refl (ordsucc 16)).
Qed.

Theorem add_1_16 : 1 + 16 = 17.
rewrite (add_nat_com 1 16 nat_1 nat_p_16).
exact add_16_1.
Qed.

Theorem add_15_1 : 15 + 1 = 16.
prove 15 + 1 = 16.
rewrite (add_nat_SR 15 0 nat_0).
rewrite (add_nat_0R 15).
exact (eq_i_refl (ordsucc 15)).
Qed.

Theorem add_15_2 : 15 + 2 = 17.
prove 15 + 2 = 17.
rewrite (add_nat_SR 15 1 nat_1).
rewrite add_15_1.
exact (eq_i_refl (ordsucc 16)).
Qed.

Theorem add_2_15 : 2 + 15 = 17.
rewrite (add_nat_com 2 15 nat_2 nat_p_15).
exact add_15_2.
Qed.

Theorem add_14_1 : 14 + 1 = 15.
prove 14 + 1 = 15.
rewrite (add_nat_SR 14 0 nat_0).
rewrite (add_nat_0R 14).
exact (eq_i_refl (ordsucc 14)).
Qed.

Theorem add_14_2 : 14 + 2 = 16.
prove 14 + 2 = 16.
rewrite (add_nat_SR 14 1 nat_1).
rewrite add_14_1.
exact (eq_i_refl (ordsucc 15)).
Qed.

Theorem add_14_3 : 14 + 3 = 17.
prove 14 + 3 = 17.
rewrite (add_nat_SR 14 2 nat_2).
rewrite add_14_2.
exact (eq_i_refl (ordsucc 16)).
Qed.

Theorem add_3_14 : 3 + 14 = 17.
rewrite (add_nat_com 3 14 nat_p_3 nat_p_14).
exact add_14_3.
Qed.

Theorem add_13_1 : 13 + 1 = 14.
prove 13 + 1 = 14.
rewrite (add_nat_SR 13 0 nat_0).
rewrite (add_nat_0R 13).
exact (eq_i_refl (ordsucc 13)).
Qed.

Theorem add_13_2 : 13 + 2 = 15.
prove 13 + 2 = 15.
rewrite (add_nat_SR 13 1 nat_1).
rewrite add_13_1.
exact (eq_i_refl (ordsucc 14)).
Qed.

Theorem add_13_3 : 13 + 3 = 16.
prove 13 + 3 = 16.
rewrite (add_nat_SR 13 2 nat_2).
rewrite add_13_2.
exact (eq_i_refl (ordsucc 15)).
Qed.

Theorem add_13_4 : 13 + 4 = 17.
prove 13 + 4 = 17.
rewrite (add_nat_SR 13 3 nat_p_3).
rewrite add_13_3.
exact (eq_i_refl (ordsucc 16)).
Qed.

Theorem add_4_13 : 4 + 13 = 17.
rewrite (add_nat_com 4 13 nat_p_4 nat_p_13).
exact add_13_4.
Qed.
