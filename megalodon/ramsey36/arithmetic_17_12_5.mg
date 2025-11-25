Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)).
Qed.

Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13
      (nat_ordsucc 12 nat_p_12)))).
Qed.

Theorem add_5_12_is_17 : 5 + 12 = 17.
prove 5 + 12 = 17.
prove 5 + ordsucc 11 = 17.
rewrite add_nat_SR 5 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
prove ordsucc (5 + 11) = 17.
apply f_eq_i ordsucc.
prove 5 + 11 = 16.
prove 5 + ordsucc 10 = 16.
rewrite add_nat_SR 5 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))))).
prove ordsucc (5 + 10) = 16.
apply f_eq_i ordsucc.
prove 5 + 10 = 15.
prove 5 + ordsucc 9 = 15.
rewrite add_nat_SR 5 9 (nat_ordsucc 8 (nat_ordsucc 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))).
prove ordsucc (5 + 9) = 15.
apply f_eq_i ordsucc.
prove 5 + 9 = 14.
prove 5 + ordsucc 8 = 14.
rewrite add_nat_SR 5 8 (nat_ordsucc 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))).
prove ordsucc (5 + 8) = 14.
apply f_eq_i ordsucc.
prove 5 + 8 = 13.
prove 5 + ordsucc 7 = 13.
rewrite add_nat_SR 5 7 (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))).
prove ordsucc (5 + 7) = 13.
apply f_eq_i ordsucc.
prove 5 + 7 = 12.
prove 5 + ordsucc 6 = 12.
rewrite add_nat_SR 5 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))).
prove ordsucc (5 + 6) = 12.
apply f_eq_i ordsucc.
prove 5 + 6 = 11.
prove 5 + ordsucc 5 = 11.
rewrite add_nat_SR 5 5 nat_p_5.
prove ordsucc (5 + 5) = 11.
apply f_eq_i ordsucc.
prove 5 + 5 = 10.
prove 5 + ordsucc 4 = 10.
rewrite add_nat_SR 5 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)).
prove ordsucc (5 + 4) = 10.
apply f_eq_i ordsucc.
prove 5 + 4 = 9.
prove 5 + ordsucc 3 = 9.
rewrite add_nat_SR 5 3 (nat_ordsucc 2 nat_2).
prove ordsucc (5 + 3) = 9.
apply f_eq_i ordsucc.
prove 5 + 3 = 8.
prove 5 + ordsucc 2 = 8.
rewrite add_nat_SR 5 2 nat_2.
prove ordsucc (5 + 2) = 8.
apply f_eq_i ordsucc.
prove 5 + 2 = 7.
prove 5 + ordsucc 1 = 7.
rewrite add_nat_SR 5 1 nat_1.
prove ordsucc (5 + 1) = 7.
apply f_eq_i ordsucc.
prove 5 + 1 = 6.
prove 5 + ordsucc 0 = 6.
rewrite add_nat_SR 5 0 nat_0.
prove ordsucc (5 + 0) = 6.
rewrite add_nat_0R 5.
prove ordsucc 5 = 6.
exact eq_i_refl 6.
Qed.

Theorem add_12_5_is_17 : 12 + 5 = 17.
rewrite add_nat_com 12 5 nat_p_12 nat_p_5.
exact add_5_12_is_17.
Qed.
