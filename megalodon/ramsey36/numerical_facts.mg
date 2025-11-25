Theorem nat_p_4 : nat_p 4.
exact nat_ordsucc 3 (nat_ordsucc 2 nat_2).
Qed.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 nat_p_4.
Qed.

Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8
      (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5 nat_p_5)))))).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 nat_p_12.
Qed.

Theorem nat_p_14 : nat_p 14.
exact nat_ordsucc 13 nat_p_13.
Qed.

Theorem nat_p_16 : nat_p 16.
exact nat_ordsucc 15 (nat_ordsucc 14 nat_p_14).
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 nat_p_16.
Qed.

Theorem nat_p_18 : nat_p 18.
exact nat_ordsucc 17 nat_p_17.
Qed.

Theorem nat_0_in_13 : 0 :e 13.
prove 0 :e ordsucc 12.
apply ordsuccI1 12 0.
prove 0 :e 12.
apply ordsuccI1 11 0.
prove 0 :e 11.
apply ordsuccI1 10 0.
prove 0 :e 10.
apply ordsuccI1 9 0.
prove 0 :e 9.
apply ordsuccI1 8 0.
prove 0 :e 8.
apply ordsuccI1 7 0.
prove 0 :e 7.
apply ordsuccI1 6 0.
prove 0 :e 6.
apply ordsuccI1 5 0.
prove 0 :e 5.
apply ordsuccI1 4 0.
prove 0 :e 4.
apply ordsuccI1 3 0.
prove 0 :e 3.
apply ordsuccI1 2 0.
exact In_0_2.
Qed.

Theorem nat_13_subset_17 : 13 c= 17.
exact nat_trans 17 nat_p_17 13
  (ordsuccI1 16 13 (ordsuccI1 15 13 (ordsuccI1 14 13 (ordsuccI2 13)))).
Qed.

Theorem nat_4_in_5 : 4 :e 5.
exact ordsuccI2 4.
Qed.

Theorem nat_5_in_6 : 5 :e 6.
exact ordsuccI2 5.
Qed.

Theorem nat_4_in_6 : 4 :e 6.
apply ordsuccI1 5 4.
exact ordsuccI2 4.
Qed.

Theorem nat_5_in_14 : 5 :e 14.
prove 5 :e ordsucc 13.
apply ordsuccI1 13 5.
prove 5 :e 13.
apply ordsuccI1 12 5.
prove 5 :e 12.
apply ordsuccI1 11 5.
prove 5 :e 11.
apply ordsuccI1 10 5.
prove 5 :e 10.
apply ordsuccI1 9 5.
prove 5 :e 9.
apply ordsuccI1 8 5.
prove 5 :e 8.
apply ordsuccI1 7 5.
prove 5 :e 7.
apply ordsuccI1 6 5.
exact ordsuccI2 5.
Qed.

Theorem nat_4_in_14 : 4 :e 14.
prove 4 :e ordsucc 13.
apply ordsuccI1 13 4.
prove 4 :e 13.
exact nat_trans 13 nat_p_13 5 (ordsuccI1 12 5 (ordsuccI1 11 5 (ordsuccI1 10 5
  (ordsuccI1 9 5 (ordsuccI1 8 5 (ordsuccI1 7 5 (ordsuccI1 6 5 (ordsuccI2 5)))))))) 4 nat_4_in_5.
Qed.

Theorem nat_4_in_13 : 4 :e 13.
apply ordsuccI1 12 4.
prove 4 :e 12.
apply ordsuccI1 11 4.
prove 4 :e 11.
apply ordsuccI1 10 4.
prove 4 :e 10.
apply ordsuccI1 9 4.
prove 4 :e 9.
apply ordsuccI1 8 4.
prove 4 :e 8.
apply ordsuccI1 7 4.
prove 4 :e 7.
apply ordsuccI1 6 4.
exact nat_4_in_6.
Qed.

Theorem nat_13_in_17 : 13 :e 17.
prove 13 :e ordsucc 16.
apply ordsuccI1 16 13.
prove 13 :e 16.
apply ordsuccI1 15 13.
prove 13 :e 15.
apply ordsuccI1 14 13.
exact ordsuccI2 13.
Qed.

Theorem nat_4_in_18 : 4 :e 18.
prove 4 :e ordsucc 17.
apply ordsuccI1 17 4.
prove 4 :e 17.
apply ordsuccI1 16 4.
prove 4 :e 16.
apply ordsuccI1 15 4.
prove 4 :e 15.
apply ordsuccI1 14 4.
exact nat_4_in_14.
Qed.

Theorem nat_5_in_18 : 5 :e 18.
prove 5 :e ordsucc 17.
apply ordsuccI1 17 5.
prove 5 :e 17.
apply ordsuccI1 16 5.
prove 5 :e 16.
apply ordsuccI1 15 5.
prove 5 :e 15.
apply ordsuccI1 14 5.
exact nat_5_in_14.
Qed.

Theorem nat_4_subset_5 : 4 c= 5.
exact nat_trans 5 nat_p_5 4 nat_4_in_5.
Qed.

Theorem nat_4_subset_13 : 4 c= 13.
exact nat_trans 13 nat_p_13 4 nat_4_in_13.
Qed.

Theorem nat_5_subset_14 : 5 c= 14.
exact nat_trans 14 nat_p_14 5 nat_5_in_14.
Qed.

Theorem nat_4_subset_14 : 4 c= 14.
exact nat_trans 14 nat_p_14 4 nat_4_in_14.
Qed.

Theorem nat_5_in_13 : 5 :e 13.
prove 5 :e ordsucc 12.
apply ordsuccI1 12 5.
prove 5 :e 12.
apply ordsuccI1 11 5.
prove 5 :e 11.
apply ordsuccI1 10 5.
prove 5 :e 10.
apply ordsuccI1 9 5.
prove 5 :e 9.
apply ordsuccI1 8 5.
prove 5 :e 8.
apply ordsuccI1 7 5.
prove 5 :e 7.
apply ordsuccI1 6 5.
exact ordsuccI2 5.
Qed.

Theorem nat_5_subset_13 : 5 c= 13.
exact nat_trans 13 nat_p_13 5 nat_5_in_13.
Qed.

Theorem nat_13_subset_14 : 13 c= 14.
exact nat_trans 14 nat_p_14 13 (ordsuccI2 13).
Qed.

Theorem nat_14_subset_17 : 14 c= 17.
exact nat_trans 17 nat_p_17 14 (ordsuccI1 16 14 (ordsuccI1 15 14 (ordsuccI2 14))).
Qed.

Theorem nat_4_in_17 : 4 :e 17.
prove 4 :e ordsucc 16.
apply ordsuccI1 16 4.
prove 4 :e 16.
apply ordsuccI1 15 4.
prove 4 :e 15.
apply ordsuccI1 14 4.
exact nat_4_in_14.
Qed.

Theorem nat_4_subset_17 : 4 c= 17.
exact nat_trans 17 nat_p_17 4 nat_4_in_17.
Qed.

Theorem nat_4_subset_18 : 4 c= 18.
exact nat_trans 18 nat_p_18 4 nat_4_in_18.
Qed.

Theorem nat_5_subset_18 : 5 c= 18.
exact nat_trans 18 nat_p_18 5 nat_5_in_18.
Qed.

Theorem compile_check : True.
exact TrueI.
Qed.
