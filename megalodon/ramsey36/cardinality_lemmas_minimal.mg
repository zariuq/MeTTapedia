Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 nat_p_12.
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13 nat_p_13))).
Qed.

Theorem nat_p_18 : nat_p 18.
exact nat_ordsucc 17 nat_p_17.
Qed.

Theorem in_13_18 : 13 :e 18.
prove 13 :e ordsucc 17.
apply ordsuccI1 17.
prove 13 :e 17.
apply ordsuccI1 16.
prove 13 :e 16.
apply ordsuccI1 15.
prove 13 :e 15.
apply ordsuccI1 14.
prove 13 :e 14.
exact ordsuccI2 13.
Qed.

Theorem Subq_13_18 : 13 c= 18.
prove forall x :e 13, x :e 18.
let x. assume Hx: x :e 13.
exact nat_trans 18 nat_p_18 13 in_13_18 x Hx.
Qed.
