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

Theorem compile_check : True.
exact TrueI.
Qed.
