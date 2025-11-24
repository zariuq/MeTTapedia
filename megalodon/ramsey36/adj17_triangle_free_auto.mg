Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition Adj17 : set -> set -> prop :=
  fun i j =>
    (i = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16)) \/
    (i = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16)) \/
    (i = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15)) \/
    (i = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16)) \/
    (i = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16)) \/
    (i = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13)) \/
    (i = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14)) \/
    (i = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15)) \/
    (i = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14)) \/
    (i = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12)) \/
    (i = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16)) \/
    (i = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15)) \/
    (i = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13)) \/
    (i = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14)) \/
    (i = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13)) \/
    (i = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11)) \/
    (i = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10)).

Theorem Adj17_not_0_0 : ~Adj17 0 0.
assume H: Adj17 0 0.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andER Hcase.
  assume Hjcases: 0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16.
  apply Hjcases.
  + assume Heq: 0 = 9.
    exact neq_9_0 Heq.
  + assume Heq: 0 = 14.
    exact neq_14_0 Heq.
  + assume Heq: 0 = 15.
    exact neq_15_0 Heq.
  + assume Heq: 0 = 16.
    exact neq_16_0 Heq.
- assume Hcase: 0 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_1 : ~Adj17 0 1.
assume H: Adj17 0 1.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andER Hcase.
  assume Hjcases: 1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16.
  apply Hjcases.
  + assume Heq: 1 = 9.
    exact neq_9_1 Heq.
  + assume Heq: 1 = 14.
    exact neq_14_1 Heq.
  + assume Heq: 1 = 15.
    exact neq_15_1 Heq.
  + assume Heq: 1 = 16.
    exact neq_16_1 Heq.
- assume Hcase: 0 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_2 : ~Adj17 0 2.
assume H: Adj17 0 2.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andER Hcase.
  assume Hjcases: 2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16.
  apply Hjcases.
  + assume Heq: 2 = 9.
    exact neq_9_2 Heq.
  + assume Heq: 2 = 14.
    exact neq_14_2 Heq.
  + assume Heq: 2 = 15.
    exact neq_15_2 Heq.
  + assume Heq: 2 = 16.
    exact neq_16_2 Heq.
- assume Hcase: 0 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_3 : ~Adj17 0 3.
assume H: Adj17 0 3.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andER Hcase.
  assume Hjcases: 3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16.
  apply Hjcases.
  + assume Heq: 3 = 9.
    exact neq_9_3 Heq.
  + assume Heq: 3 = 14.
    exact neq_14_3 Heq.
  + assume Heq: 3 = 15.
    exact neq_15_3 Heq.
  + assume Heq: 3 = 16.
    exact neq_16_3 Heq.
- assume Hcase: 0 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_4 : ~Adj17 0 4.
assume H: Adj17 0 4.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andER Hcase.
  assume Hjcases: 4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16.
  apply Hjcases.
  + assume Heq: 4 = 9.
    exact neq_9_4 Heq.
  + assume Heq: 4 = 14.
    exact neq_14_4 Heq.
  + assume Heq: 4 = 15.
    exact neq_15_4 Heq.
  + assume Heq: 4 = 16.
    exact neq_16_4 Heq.
- assume Hcase: 0 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_5 : ~Adj17 0 5.
assume H: Adj17 0 5.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andER Hcase.
  assume Hjcases: 5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16.
  apply Hjcases.
  + assume Heq: 5 = 9.
    exact neq_9_5 Heq.
  + assume Heq: 5 = 14.
    exact neq_14_5 Heq.
  + assume Heq: 5 = 15.
    exact neq_15_5 Heq.
  + assume Heq: 5 = 16.
    exact neq_16_5 Heq.
- assume Hcase: 0 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_6 : ~Adj17 0 6.
assume H: Adj17 0 6.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andER Hcase.
  assume Hjcases: 6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16.
  apply Hjcases.
  + assume Heq: 6 = 9.
    exact neq_9_6 Heq.
  + assume Heq: 6 = 14.
    exact neq_14_6 Heq.
  + assume Heq: 6 = 15.
    exact neq_15_6 Heq.
  + assume Heq: 6 = 16.
    exact neq_16_6 Heq.
- assume Hcase: 0 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_7 : ~Adj17 0 7.
assume H: Adj17 0 7.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andER Hcase.
  assume Hjcases: 7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16.
  apply Hjcases.
  + assume Heq: 7 = 9.
    exact neq_9_7 Heq.
  + assume Heq: 7 = 14.
    exact neq_14_7 Heq.
  + assume Heq: 7 = 15.
    exact neq_15_7 Heq.
  + assume Heq: 7 = 16.
    exact neq_16_7 Heq.
- assume Hcase: 0 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_8 : ~Adj17 0 8.
assume H: Adj17 0 8.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andER Hcase.
  assume Hjcases: 8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16.
  apply Hjcases.
  + assume Heq: 8 = 9.
    exact neq_9_8 Heq.
  + assume Heq: 8 = 14.
    exact neq_14_8 Heq.
  + assume Heq: 8 = 15.
    exact neq_15_8 Heq.
  + assume Heq: 8 = 16.
    exact neq_16_8 Heq.
- assume Hcase: 0 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_10 : ~Adj17 0 10.
assume H: Adj17 0 10.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andER Hcase.
  assume Hjcases: 10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16.
  apply Hjcases.
  + assume Heq: 10 = 9.
    exact neq_10_9 Heq.
  + assume Heq: 10 = 14.
    exact neq_14_10 Heq.
  + assume Heq: 10 = 15.
    exact neq_15_10 Heq.
  + assume Heq: 10 = 16.
    exact neq_16_10 Heq.
- assume Hcase: 0 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_11 : ~Adj17 0 11.
assume H: Adj17 0 11.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andER Hcase.
  assume Hjcases: 11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16.
  apply Hjcases.
  + assume Heq: 11 = 9.
    exact neq_11_9 Heq.
  + assume Heq: 11 = 14.
    exact neq_14_11 Heq.
  + assume Heq: 11 = 15.
    exact neq_15_11 Heq.
  + assume Heq: 11 = 16.
    exact neq_16_11 Heq.
- assume Hcase: 0 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_12 : ~Adj17 0 12.
assume H: Adj17 0 12.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andER Hcase.
  assume Hjcases: 12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16.
  apply Hjcases.
  + assume Heq: 12 = 9.
    exact neq_12_9 Heq.
  + assume Heq: 12 = 14.
    exact neq_14_12 Heq.
  + assume Heq: 12 = 15.
    exact neq_15_12 Heq.
  + assume Heq: 12 = 16.
    exact neq_16_12 Heq.
- assume Hcase: 0 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_0_13 : ~Adj17 0 13.
assume H: Adj17 0 13.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andER Hcase.
  assume Hjcases: 13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16.
  apply Hjcases.
  + assume Heq: 13 = 9.
    exact neq_13_9 Heq.
  + assume Heq: 13 = 14.
    exact neq_14_13 Heq.
  + assume Heq: 13 = 15.
    exact neq_15_13 Heq.
  + assume Heq: 13 = 16.
    exact neq_16_13 Heq.
- assume Hcase: 0 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_not_1_0 : ~Adj17 1 0.
assume H: Adj17 1 0.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andER Hcase.
  assume Hjcases: 0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16.
  apply Hjcases.
  + assume Heq: 0 = 7.
    exact neq_7_0 Heq.
  + assume Heq: 0 = 11.
    exact neq_11_0 Heq.
  + assume Heq: 0 = 13.
    exact neq_13_0 Heq.
  + assume Heq: 0 = 16.
    exact neq_16_0 Heq.
- assume Hcase: 1 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_1 : ~Adj17 1 1.
assume H: Adj17 1 1.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andER Hcase.
  assume Hjcases: 1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16.
  apply Hjcases.
  + assume Heq: 1 = 7.
    exact neq_7_1 Heq.
  + assume Heq: 1 = 11.
    exact neq_11_1 Heq.
  + assume Heq: 1 = 13.
    exact neq_13_1 Heq.
  + assume Heq: 1 = 16.
    exact neq_16_1 Heq.
- assume Hcase: 1 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_2 : ~Adj17 1 2.
assume H: Adj17 1 2.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andER Hcase.
  assume Hjcases: 2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16.
  apply Hjcases.
  + assume Heq: 2 = 7.
    exact neq_7_2 Heq.
  + assume Heq: 2 = 11.
    exact neq_11_2 Heq.
  + assume Heq: 2 = 13.
    exact neq_13_2 Heq.
  + assume Heq: 2 = 16.
    exact neq_16_2 Heq.
- assume Hcase: 1 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_3 : ~Adj17 1 3.
assume H: Adj17 1 3.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andER Hcase.
  assume Hjcases: 3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16.
  apply Hjcases.
  + assume Heq: 3 = 7.
    exact neq_7_3 Heq.
  + assume Heq: 3 = 11.
    exact neq_11_3 Heq.
  + assume Heq: 3 = 13.
    exact neq_13_3 Heq.
  + assume Heq: 3 = 16.
    exact neq_16_3 Heq.
- assume Hcase: 1 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_4 : ~Adj17 1 4.
assume H: Adj17 1 4.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andER Hcase.
  assume Hjcases: 4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16.
  apply Hjcases.
  + assume Heq: 4 = 7.
    exact neq_7_4 Heq.
  + assume Heq: 4 = 11.
    exact neq_11_4 Heq.
  + assume Heq: 4 = 13.
    exact neq_13_4 Heq.
  + assume Heq: 4 = 16.
    exact neq_16_4 Heq.
- assume Hcase: 1 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_5 : ~Adj17 1 5.
assume H: Adj17 1 5.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andER Hcase.
  assume Hjcases: 5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16.
  apply Hjcases.
  + assume Heq: 5 = 7.
    exact neq_7_5 Heq.
  + assume Heq: 5 = 11.
    exact neq_11_5 Heq.
  + assume Heq: 5 = 13.
    exact neq_13_5 Heq.
  + assume Heq: 5 = 16.
    exact neq_16_5 Heq.
- assume Hcase: 1 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_6 : ~Adj17 1 6.
assume H: Adj17 1 6.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andER Hcase.
  assume Hjcases: 6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16.
  apply Hjcases.
  + assume Heq: 6 = 7.
    exact neq_7_6 Heq.
  + assume Heq: 6 = 11.
    exact neq_11_6 Heq.
  + assume Heq: 6 = 13.
    exact neq_13_6 Heq.
  + assume Heq: 6 = 16.
    exact neq_16_6 Heq.
- assume Hcase: 1 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_8 : ~Adj17 1 8.
assume H: Adj17 1 8.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andER Hcase.
  assume Hjcases: 8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16.
  apply Hjcases.
  + assume Heq: 8 = 7.
    exact neq_8_7 Heq.
  + assume Heq: 8 = 11.
    exact neq_11_8 Heq.
  + assume Heq: 8 = 13.
    exact neq_13_8 Heq.
  + assume Heq: 8 = 16.
    exact neq_16_8 Heq.
- assume Hcase: 1 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_9 : ~Adj17 1 9.
assume H: Adj17 1 9.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andER Hcase.
  assume Hjcases: 9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16.
  apply Hjcases.
  + assume Heq: 9 = 7.
    exact neq_9_7 Heq.
  + assume Heq: 9 = 11.
    exact neq_11_9 Heq.
  + assume Heq: 9 = 13.
    exact neq_13_9 Heq.
  + assume Heq: 9 = 16.
    exact neq_16_9 Heq.
- assume Hcase: 1 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_10 : ~Adj17 1 10.
assume H: Adj17 1 10.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andER Hcase.
  assume Hjcases: 10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16.
  apply Hjcases.
  + assume Heq: 10 = 7.
    exact neq_10_7 Heq.
  + assume Heq: 10 = 11.
    exact neq_11_10 Heq.
  + assume Heq: 10 = 13.
    exact neq_13_10 Heq.
  + assume Heq: 10 = 16.
    exact neq_16_10 Heq.
- assume Hcase: 1 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_12 : ~Adj17 1 12.
assume H: Adj17 1 12.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andER Hcase.
  assume Hjcases: 12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16.
  apply Hjcases.
  + assume Heq: 12 = 7.
    exact neq_12_7 Heq.
  + assume Heq: 12 = 11.
    exact neq_12_11 Heq.
  + assume Heq: 12 = 13.
    exact neq_13_12 Heq.
  + assume Heq: 12 = 16.
    exact neq_16_12 Heq.
- assume Hcase: 1 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_14 : ~Adj17 1 14.
assume H: Adj17 1 14.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andER Hcase.
  assume Hjcases: 14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16.
  apply Hjcases.
  + assume Heq: 14 = 7.
    exact neq_14_7 Heq.
  + assume Heq: 14 = 11.
    exact neq_14_11 Heq.
  + assume Heq: 14 = 13.
    exact neq_14_13 Heq.
  + assume Heq: 14 = 16.
    exact neq_16_14 Heq.
- assume Hcase: 1 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_1_15 : ~Adj17 1 15.
assume H: Adj17 1 15.
prove False.
apply H.
- assume Hcase: 1 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andER Hcase.
  assume Hjcases: 15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16.
  apply Hjcases.
  + assume Heq: 15 = 7.
    exact neq_15_7 Heq.
  + assume Heq: 15 = 11.
    exact neq_15_11 Heq.
  + assume Heq: 15 = 13.
    exact neq_15_13 Heq.
  + assume Heq: 15 = 16.
    exact neq_16_15 Heq.
- assume Hcase: 1 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_not_2_0 : ~Adj17 2 0.
assume H: Adj17 2 0.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andER Hcase.
  assume Hjcases: 0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15.
  apply Hjcases.
  + assume Heq: 0 = 8.
    exact neq_8_0 Heq.
  + assume Heq: 0 = 10.
    exact neq_10_0 Heq.
  + assume Heq: 0 = 12.
    exact neq_12_0 Heq.
  + assume Heq: 0 = 15.
    exact neq_15_0 Heq.
- assume Hcase: 2 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_1 : ~Adj17 2 1.
assume H: Adj17 2 1.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andER Hcase.
  assume Hjcases: 1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15.
  apply Hjcases.
  + assume Heq: 1 = 8.
    exact neq_8_1 Heq.
  + assume Heq: 1 = 10.
    exact neq_10_1 Heq.
  + assume Heq: 1 = 12.
    exact neq_12_1 Heq.
  + assume Heq: 1 = 15.
    exact neq_15_1 Heq.
- assume Hcase: 2 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_2 : ~Adj17 2 2.
assume H: Adj17 2 2.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andER Hcase.
  assume Hjcases: 2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15.
  apply Hjcases.
  + assume Heq: 2 = 8.
    exact neq_8_2 Heq.
  + assume Heq: 2 = 10.
    exact neq_10_2 Heq.
  + assume Heq: 2 = 12.
    exact neq_12_2 Heq.
  + assume Heq: 2 = 15.
    exact neq_15_2 Heq.
- assume Hcase: 2 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_3 : ~Adj17 2 3.
assume H: Adj17 2 3.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andER Hcase.
  assume Hjcases: 3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15.
  apply Hjcases.
  + assume Heq: 3 = 8.
    exact neq_8_3 Heq.
  + assume Heq: 3 = 10.
    exact neq_10_3 Heq.
  + assume Heq: 3 = 12.
    exact neq_12_3 Heq.
  + assume Heq: 3 = 15.
    exact neq_15_3 Heq.
- assume Hcase: 2 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_4 : ~Adj17 2 4.
assume H: Adj17 2 4.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andER Hcase.
  assume Hjcases: 4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15.
  apply Hjcases.
  + assume Heq: 4 = 8.
    exact neq_8_4 Heq.
  + assume Heq: 4 = 10.
    exact neq_10_4 Heq.
  + assume Heq: 4 = 12.
    exact neq_12_4 Heq.
  + assume Heq: 4 = 15.
    exact neq_15_4 Heq.
- assume Hcase: 2 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_5 : ~Adj17 2 5.
assume H: Adj17 2 5.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andER Hcase.
  assume Hjcases: 5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15.
  apply Hjcases.
  + assume Heq: 5 = 8.
    exact neq_8_5 Heq.
  + assume Heq: 5 = 10.
    exact neq_10_5 Heq.
  + assume Heq: 5 = 12.
    exact neq_12_5 Heq.
  + assume Heq: 5 = 15.
    exact neq_15_5 Heq.
- assume Hcase: 2 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_6 : ~Adj17 2 6.
assume H: Adj17 2 6.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andER Hcase.
  assume Hjcases: 6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15.
  apply Hjcases.
  + assume Heq: 6 = 8.
    exact neq_8_6 Heq.
  + assume Heq: 6 = 10.
    exact neq_10_6 Heq.
  + assume Heq: 6 = 12.
    exact neq_12_6 Heq.
  + assume Heq: 6 = 15.
    exact neq_15_6 Heq.
- assume Hcase: 2 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_7 : ~Adj17 2 7.
assume H: Adj17 2 7.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andER Hcase.
  assume Hjcases: 7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15.
  apply Hjcases.
  + assume Heq: 7 = 8.
    exact neq_8_7 Heq.
  + assume Heq: 7 = 10.
    exact neq_10_7 Heq.
  + assume Heq: 7 = 12.
    exact neq_12_7 Heq.
  + assume Heq: 7 = 15.
    exact neq_15_7 Heq.
- assume Hcase: 2 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_9 : ~Adj17 2 9.
assume H: Adj17 2 9.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andER Hcase.
  assume Hjcases: 9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15.
  apply Hjcases.
  + assume Heq: 9 = 8.
    exact neq_9_8 Heq.
  + assume Heq: 9 = 10.
    exact neq_10_9 Heq.
  + assume Heq: 9 = 12.
    exact neq_12_9 Heq.
  + assume Heq: 9 = 15.
    exact neq_15_9 Heq.
- assume Hcase: 2 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_11 : ~Adj17 2 11.
assume H: Adj17 2 11.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andER Hcase.
  assume Hjcases: 11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15.
  apply Hjcases.
  + assume Heq: 11 = 8.
    exact neq_11_8 Heq.
  + assume Heq: 11 = 10.
    exact neq_11_10 Heq.
  + assume Heq: 11 = 12.
    exact neq_12_11 Heq.
  + assume Heq: 11 = 15.
    exact neq_15_11 Heq.
- assume Hcase: 2 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_13 : ~Adj17 2 13.
assume H: Adj17 2 13.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andER Hcase.
  assume Hjcases: 13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15.
  apply Hjcases.
  + assume Heq: 13 = 8.
    exact neq_13_8 Heq.
  + assume Heq: 13 = 10.
    exact neq_13_10 Heq.
  + assume Heq: 13 = 12.
    exact neq_13_12 Heq.
  + assume Heq: 13 = 15.
    exact neq_15_13 Heq.
- assume Hcase: 2 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_14 : ~Adj17 2 14.
assume H: Adj17 2 14.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andER Hcase.
  assume Hjcases: 14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15.
  apply Hjcases.
  + assume Heq: 14 = 8.
    exact neq_14_8 Heq.
  + assume Heq: 14 = 10.
    exact neq_14_10 Heq.
  + assume Heq: 14 = 12.
    exact neq_14_12 Heq.
  + assume Heq: 14 = 15.
    exact neq_15_14 Heq.
- assume Hcase: 2 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_2_16 : ~Adj17 2 16.
assume H: Adj17 2 16.
prove False.
apply H.
- assume Hcase: 2 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andER Hcase.
  assume Hjcases: 16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15.
  apply Hjcases.
  + assume Heq: 16 = 8.
    exact neq_16_8 Heq.
  + assume Heq: 16 = 10.
    exact neq_16_10 Heq.
  + assume Heq: 16 = 12.
    exact neq_16_12 Heq.
  + assume Heq: 16 = 15.
    exact neq_16_15 Heq.
- assume Hcase: 2 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_not_3_0 : ~Adj17 3 0.
assume H: Adj17 3 0.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andER Hcase.
  assume Hjcases: 0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16.
  apply Hjcases.
  + assume Heq: 0 = 6.
    exact neq_6_0 Heq.
  + assume Heq: 0 = 8.
    exact neq_8_0 Heq.
  + assume Heq: 0 = 13.
    exact neq_13_0 Heq.
  + assume Heq: 0 = 15.
    exact neq_15_0 Heq.
  + assume Heq: 0 = 16.
    exact neq_16_0 Heq.
- assume Hcase: 3 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_1 : ~Adj17 3 1.
assume H: Adj17 3 1.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andER Hcase.
  assume Hjcases: 1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16.
  apply Hjcases.
  + assume Heq: 1 = 6.
    exact neq_6_1 Heq.
  + assume Heq: 1 = 8.
    exact neq_8_1 Heq.
  + assume Heq: 1 = 13.
    exact neq_13_1 Heq.
  + assume Heq: 1 = 15.
    exact neq_15_1 Heq.
  + assume Heq: 1 = 16.
    exact neq_16_1 Heq.
- assume Hcase: 3 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_2 : ~Adj17 3 2.
assume H: Adj17 3 2.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andER Hcase.
  assume Hjcases: 2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16.
  apply Hjcases.
  + assume Heq: 2 = 6.
    exact neq_6_2 Heq.
  + assume Heq: 2 = 8.
    exact neq_8_2 Heq.
  + assume Heq: 2 = 13.
    exact neq_13_2 Heq.
  + assume Heq: 2 = 15.
    exact neq_15_2 Heq.
  + assume Heq: 2 = 16.
    exact neq_16_2 Heq.
- assume Hcase: 3 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_3 : ~Adj17 3 3.
assume H: Adj17 3 3.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andER Hcase.
  assume Hjcases: 3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16.
  apply Hjcases.
  + assume Heq: 3 = 6.
    exact neq_6_3 Heq.
  + assume Heq: 3 = 8.
    exact neq_8_3 Heq.
  + assume Heq: 3 = 13.
    exact neq_13_3 Heq.
  + assume Heq: 3 = 15.
    exact neq_15_3 Heq.
  + assume Heq: 3 = 16.
    exact neq_16_3 Heq.
- assume Hcase: 3 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_4 : ~Adj17 3 4.
assume H: Adj17 3 4.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andER Hcase.
  assume Hjcases: 4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16.
  apply Hjcases.
  + assume Heq: 4 = 6.
    exact neq_6_4 Heq.
  + assume Heq: 4 = 8.
    exact neq_8_4 Heq.
  + assume Heq: 4 = 13.
    exact neq_13_4 Heq.
  + assume Heq: 4 = 15.
    exact neq_15_4 Heq.
  + assume Heq: 4 = 16.
    exact neq_16_4 Heq.
- assume Hcase: 3 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_5 : ~Adj17 3 5.
assume H: Adj17 3 5.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andER Hcase.
  assume Hjcases: 5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16.
  apply Hjcases.
  + assume Heq: 5 = 6.
    exact neq_6_5 Heq.
  + assume Heq: 5 = 8.
    exact neq_8_5 Heq.
  + assume Heq: 5 = 13.
    exact neq_13_5 Heq.
  + assume Heq: 5 = 15.
    exact neq_15_5 Heq.
  + assume Heq: 5 = 16.
    exact neq_16_5 Heq.
- assume Hcase: 3 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_7 : ~Adj17 3 7.
assume H: Adj17 3 7.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andER Hcase.
  assume Hjcases: 7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16.
  apply Hjcases.
  + assume Heq: 7 = 6.
    exact neq_7_6 Heq.
  + assume Heq: 7 = 8.
    exact neq_8_7 Heq.
  + assume Heq: 7 = 13.
    exact neq_13_7 Heq.
  + assume Heq: 7 = 15.
    exact neq_15_7 Heq.
  + assume Heq: 7 = 16.
    exact neq_16_7 Heq.
- assume Hcase: 3 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_9 : ~Adj17 3 9.
assume H: Adj17 3 9.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andER Hcase.
  assume Hjcases: 9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16.
  apply Hjcases.
  + assume Heq: 9 = 6.
    exact neq_9_6 Heq.
  + assume Heq: 9 = 8.
    exact neq_9_8 Heq.
  + assume Heq: 9 = 13.
    exact neq_13_9 Heq.
  + assume Heq: 9 = 15.
    exact neq_15_9 Heq.
  + assume Heq: 9 = 16.
    exact neq_16_9 Heq.
- assume Hcase: 3 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_10 : ~Adj17 3 10.
assume H: Adj17 3 10.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andER Hcase.
  assume Hjcases: 10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16.
  apply Hjcases.
  + assume Heq: 10 = 6.
    exact neq_10_6 Heq.
  + assume Heq: 10 = 8.
    exact neq_10_8 Heq.
  + assume Heq: 10 = 13.
    exact neq_13_10 Heq.
  + assume Heq: 10 = 15.
    exact neq_15_10 Heq.
  + assume Heq: 10 = 16.
    exact neq_16_10 Heq.
- assume Hcase: 3 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_11 : ~Adj17 3 11.
assume H: Adj17 3 11.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andER Hcase.
  assume Hjcases: 11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16.
  apply Hjcases.
  + assume Heq: 11 = 6.
    exact neq_11_6 Heq.
  + assume Heq: 11 = 8.
    exact neq_11_8 Heq.
  + assume Heq: 11 = 13.
    exact neq_13_11 Heq.
  + assume Heq: 11 = 15.
    exact neq_15_11 Heq.
  + assume Heq: 11 = 16.
    exact neq_16_11 Heq.
- assume Hcase: 3 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_12 : ~Adj17 3 12.
assume H: Adj17 3 12.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andER Hcase.
  assume Hjcases: 12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16.
  apply Hjcases.
  + assume Heq: 12 = 6.
    exact neq_12_6 Heq.
  + assume Heq: 12 = 8.
    exact neq_12_8 Heq.
  + assume Heq: 12 = 13.
    exact neq_13_12 Heq.
  + assume Heq: 12 = 15.
    exact neq_15_12 Heq.
  + assume Heq: 12 = 16.
    exact neq_16_12 Heq.
- assume Hcase: 3 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_3_14 : ~Adj17 3 14.
assume H: Adj17 3 14.
prove False.
apply H.
- assume Hcase: 3 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andER Hcase.
  assume Hjcases: 14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16.
  apply Hjcases.
  + assume Heq: 14 = 6.
    exact neq_14_6 Heq.
  + assume Heq: 14 = 8.
    exact neq_14_8 Heq.
  + assume Heq: 14 = 13.
    exact neq_14_13 Heq.
  + assume Heq: 14 = 15.
    exact neq_15_14 Heq.
  + assume Heq: 14 = 16.
    exact neq_16_14 Heq.
- assume Hcase: 3 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_not_4_0 : ~Adj17 4 0.
assume H: Adj17 4 0.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andER Hcase.
  assume Hjcases: 0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16.
  apply Hjcases.
  + assume Heq: 0 = 5.
    exact neq_5_0 Heq.
  + assume Heq: 0 = 7.
    exact neq_7_0 Heq.
  + assume Heq: 0 = 12.
    exact neq_12_0 Heq.
  + assume Heq: 0 = 14.
    exact neq_14_0 Heq.
  + assume Heq: 0 = 16.
    exact neq_16_0 Heq.
- assume Hcase: 4 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_1 : ~Adj17 4 1.
assume H: Adj17 4 1.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andER Hcase.
  assume Hjcases: 1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16.
  apply Hjcases.
  + assume Heq: 1 = 5.
    exact neq_5_1 Heq.
  + assume Heq: 1 = 7.
    exact neq_7_1 Heq.
  + assume Heq: 1 = 12.
    exact neq_12_1 Heq.
  + assume Heq: 1 = 14.
    exact neq_14_1 Heq.
  + assume Heq: 1 = 16.
    exact neq_16_1 Heq.
- assume Hcase: 4 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_2 : ~Adj17 4 2.
assume H: Adj17 4 2.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andER Hcase.
  assume Hjcases: 2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16.
  apply Hjcases.
  + assume Heq: 2 = 5.
    exact neq_5_2 Heq.
  + assume Heq: 2 = 7.
    exact neq_7_2 Heq.
  + assume Heq: 2 = 12.
    exact neq_12_2 Heq.
  + assume Heq: 2 = 14.
    exact neq_14_2 Heq.
  + assume Heq: 2 = 16.
    exact neq_16_2 Heq.
- assume Hcase: 4 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_3 : ~Adj17 4 3.
assume H: Adj17 4 3.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andER Hcase.
  assume Hjcases: 3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16.
  apply Hjcases.
  + assume Heq: 3 = 5.
    exact neq_5_3 Heq.
  + assume Heq: 3 = 7.
    exact neq_7_3 Heq.
  + assume Heq: 3 = 12.
    exact neq_12_3 Heq.
  + assume Heq: 3 = 14.
    exact neq_14_3 Heq.
  + assume Heq: 3 = 16.
    exact neq_16_3 Heq.
- assume Hcase: 4 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_4 : ~Adj17 4 4.
assume H: Adj17 4 4.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andER Hcase.
  assume Hjcases: 4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16.
  apply Hjcases.
  + assume Heq: 4 = 5.
    exact neq_5_4 Heq.
  + assume Heq: 4 = 7.
    exact neq_7_4 Heq.
  + assume Heq: 4 = 12.
    exact neq_12_4 Heq.
  + assume Heq: 4 = 14.
    exact neq_14_4 Heq.
  + assume Heq: 4 = 16.
    exact neq_16_4 Heq.
- assume Hcase: 4 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_6 : ~Adj17 4 6.
assume H: Adj17 4 6.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andER Hcase.
  assume Hjcases: 6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16.
  apply Hjcases.
  + assume Heq: 6 = 5.
    exact neq_6_5 Heq.
  + assume Heq: 6 = 7.
    exact neq_7_6 Heq.
  + assume Heq: 6 = 12.
    exact neq_12_6 Heq.
  + assume Heq: 6 = 14.
    exact neq_14_6 Heq.
  + assume Heq: 6 = 16.
    exact neq_16_6 Heq.
- assume Hcase: 4 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_8 : ~Adj17 4 8.
assume H: Adj17 4 8.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andER Hcase.
  assume Hjcases: 8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16.
  apply Hjcases.
  + assume Heq: 8 = 5.
    exact neq_8_5 Heq.
  + assume Heq: 8 = 7.
    exact neq_8_7 Heq.
  + assume Heq: 8 = 12.
    exact neq_12_8 Heq.
  + assume Heq: 8 = 14.
    exact neq_14_8 Heq.
  + assume Heq: 8 = 16.
    exact neq_16_8 Heq.
- assume Hcase: 4 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_9 : ~Adj17 4 9.
assume H: Adj17 4 9.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andER Hcase.
  assume Hjcases: 9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16.
  apply Hjcases.
  + assume Heq: 9 = 5.
    exact neq_9_5 Heq.
  + assume Heq: 9 = 7.
    exact neq_9_7 Heq.
  + assume Heq: 9 = 12.
    exact neq_12_9 Heq.
  + assume Heq: 9 = 14.
    exact neq_14_9 Heq.
  + assume Heq: 9 = 16.
    exact neq_16_9 Heq.
- assume Hcase: 4 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_10 : ~Adj17 4 10.
assume H: Adj17 4 10.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andER Hcase.
  assume Hjcases: 10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16.
  apply Hjcases.
  + assume Heq: 10 = 5.
    exact neq_10_5 Heq.
  + assume Heq: 10 = 7.
    exact neq_10_7 Heq.
  + assume Heq: 10 = 12.
    exact neq_12_10 Heq.
  + assume Heq: 10 = 14.
    exact neq_14_10 Heq.
  + assume Heq: 10 = 16.
    exact neq_16_10 Heq.
- assume Hcase: 4 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_11 : ~Adj17 4 11.
assume H: Adj17 4 11.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andER Hcase.
  assume Hjcases: 11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16.
  apply Hjcases.
  + assume Heq: 11 = 5.
    exact neq_11_5 Heq.
  + assume Heq: 11 = 7.
    exact neq_11_7 Heq.
  + assume Heq: 11 = 12.
    exact neq_12_11 Heq.
  + assume Heq: 11 = 14.
    exact neq_14_11 Heq.
  + assume Heq: 11 = 16.
    exact neq_16_11 Heq.
- assume Hcase: 4 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_13 : ~Adj17 4 13.
assume H: Adj17 4 13.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andER Hcase.
  assume Hjcases: 13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16.
  apply Hjcases.
  + assume Heq: 13 = 5.
    exact neq_13_5 Heq.
  + assume Heq: 13 = 7.
    exact neq_13_7 Heq.
  + assume Heq: 13 = 12.
    exact neq_13_12 Heq.
  + assume Heq: 13 = 14.
    exact neq_14_13 Heq.
  + assume Heq: 13 = 16.
    exact neq_16_13 Heq.
- assume Hcase: 4 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_4_15 : ~Adj17 4 15.
assume H: Adj17 4 15.
prove False.
apply H.
- assume Hcase: 4 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andER Hcase.
  assume Hjcases: 15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16.
  apply Hjcases.
  + assume Heq: 15 = 5.
    exact neq_15_5 Heq.
  + assume Heq: 15 = 7.
    exact neq_15_7 Heq.
  + assume Heq: 15 = 12.
    exact neq_15_12 Heq.
  + assume Heq: 15 = 14.
    exact neq_15_14 Heq.
  + assume Heq: 15 = 16.
    exact neq_16_15 Heq.
- assume Hcase: 4 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_not_5_0 : ~Adj17 5 0.
assume H: Adj17 5 0.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andER Hcase.
  assume Hjcases: 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13.
  apply Hjcases.
  + assume Heq: 0 = 4.
    exact neq_4_0 Heq.
  + assume Heq: 0 = 9.
    exact neq_9_0 Heq.
  + assume Heq: 0 = 10.
    exact neq_10_0 Heq.
  + assume Heq: 0 = 11.
    exact neq_11_0 Heq.
  + assume Heq: 0 = 13.
    exact neq_13_0 Heq.
- assume Hcase: 5 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_1 : ~Adj17 5 1.
assume H: Adj17 5 1.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andER Hcase.
  assume Hjcases: 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13.
  apply Hjcases.
  + assume Heq: 1 = 4.
    exact neq_4_1 Heq.
  + assume Heq: 1 = 9.
    exact neq_9_1 Heq.
  + assume Heq: 1 = 10.
    exact neq_10_1 Heq.
  + assume Heq: 1 = 11.
    exact neq_11_1 Heq.
  + assume Heq: 1 = 13.
    exact neq_13_1 Heq.
- assume Hcase: 5 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_2 : ~Adj17 5 2.
assume H: Adj17 5 2.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andER Hcase.
  assume Hjcases: 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13.
  apply Hjcases.
  + assume Heq: 2 = 4.
    exact neq_4_2 Heq.
  + assume Heq: 2 = 9.
    exact neq_9_2 Heq.
  + assume Heq: 2 = 10.
    exact neq_10_2 Heq.
  + assume Heq: 2 = 11.
    exact neq_11_2 Heq.
  + assume Heq: 2 = 13.
    exact neq_13_2 Heq.
- assume Hcase: 5 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_3 : ~Adj17 5 3.
assume H: Adj17 5 3.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andER Hcase.
  assume Hjcases: 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13.
  apply Hjcases.
  + assume Heq: 3 = 4.
    exact neq_4_3 Heq.
  + assume Heq: 3 = 9.
    exact neq_9_3 Heq.
  + assume Heq: 3 = 10.
    exact neq_10_3 Heq.
  + assume Heq: 3 = 11.
    exact neq_11_3 Heq.
  + assume Heq: 3 = 13.
    exact neq_13_3 Heq.
- assume Hcase: 5 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_5 : ~Adj17 5 5.
assume H: Adj17 5 5.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andER Hcase.
  assume Hjcases: 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13.
  apply Hjcases.
  + assume Heq: 5 = 4.
    exact neq_5_4 Heq.
  + assume Heq: 5 = 9.
    exact neq_9_5 Heq.
  + assume Heq: 5 = 10.
    exact neq_10_5 Heq.
  + assume Heq: 5 = 11.
    exact neq_11_5 Heq.
  + assume Heq: 5 = 13.
    exact neq_13_5 Heq.
- assume Hcase: 5 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_6 : ~Adj17 5 6.
assume H: Adj17 5 6.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andER Hcase.
  assume Hjcases: 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13.
  apply Hjcases.
  + assume Heq: 6 = 4.
    exact neq_6_4 Heq.
  + assume Heq: 6 = 9.
    exact neq_9_6 Heq.
  + assume Heq: 6 = 10.
    exact neq_10_6 Heq.
  + assume Heq: 6 = 11.
    exact neq_11_6 Heq.
  + assume Heq: 6 = 13.
    exact neq_13_6 Heq.
- assume Hcase: 5 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_7 : ~Adj17 5 7.
assume H: Adj17 5 7.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andER Hcase.
  assume Hjcases: 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13.
  apply Hjcases.
  + assume Heq: 7 = 4.
    exact neq_7_4 Heq.
  + assume Heq: 7 = 9.
    exact neq_9_7 Heq.
  + assume Heq: 7 = 10.
    exact neq_10_7 Heq.
  + assume Heq: 7 = 11.
    exact neq_11_7 Heq.
  + assume Heq: 7 = 13.
    exact neq_13_7 Heq.
- assume Hcase: 5 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_8 : ~Adj17 5 8.
assume H: Adj17 5 8.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andER Hcase.
  assume Hjcases: 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13.
  apply Hjcases.
  + assume Heq: 8 = 4.
    exact neq_8_4 Heq.
  + assume Heq: 8 = 9.
    exact neq_9_8 Heq.
  + assume Heq: 8 = 10.
    exact neq_10_8 Heq.
  + assume Heq: 8 = 11.
    exact neq_11_8 Heq.
  + assume Heq: 8 = 13.
    exact neq_13_8 Heq.
- assume Hcase: 5 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_12 : ~Adj17 5 12.
assume H: Adj17 5 12.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andER Hcase.
  assume Hjcases: 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13.
  apply Hjcases.
  + assume Heq: 12 = 4.
    exact neq_12_4 Heq.
  + assume Heq: 12 = 9.
    exact neq_12_9 Heq.
  + assume Heq: 12 = 10.
    exact neq_12_10 Heq.
  + assume Heq: 12 = 11.
    exact neq_12_11 Heq.
  + assume Heq: 12 = 13.
    exact neq_13_12 Heq.
- assume Hcase: 5 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_14 : ~Adj17 5 14.
assume H: Adj17 5 14.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andER Hcase.
  assume Hjcases: 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13.
  apply Hjcases.
  + assume Heq: 14 = 4.
    exact neq_14_4 Heq.
  + assume Heq: 14 = 9.
    exact neq_14_9 Heq.
  + assume Heq: 14 = 10.
    exact neq_14_10 Heq.
  + assume Heq: 14 = 11.
    exact neq_14_11 Heq.
  + assume Heq: 14 = 13.
    exact neq_14_13 Heq.
- assume Hcase: 5 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_15 : ~Adj17 5 15.
assume H: Adj17 5 15.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andER Hcase.
  assume Hjcases: 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13.
  apply Hjcases.
  + assume Heq: 15 = 4.
    exact neq_15_4 Heq.
  + assume Heq: 15 = 9.
    exact neq_15_9 Heq.
  + assume Heq: 15 = 10.
    exact neq_15_10 Heq.
  + assume Heq: 15 = 11.
    exact neq_15_11 Heq.
  + assume Heq: 15 = 13.
    exact neq_15_13 Heq.
- assume Hcase: 5 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_5_16 : ~Adj17 5 16.
assume H: Adj17 5 16.
prove False.
apply H.
- assume Hcase: 5 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andER Hcase.
  assume Hjcases: 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13.
  apply Hjcases.
  + assume Heq: 16 = 4.
    exact neq_16_4 Heq.
  + assume Heq: 16 = 9.
    exact neq_16_9 Heq.
  + assume Heq: 16 = 10.
    exact neq_16_10 Heq.
  + assume Heq: 16 = 11.
    exact neq_16_11 Heq.
  + assume Heq: 16 = 13.
    exact neq_16_13 Heq.
- assume Hcase: 5 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_not_6_0 : ~Adj17 6 0.
assume H: Adj17 6 0.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andER Hcase.
  assume Hjcases: 0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14.
  apply Hjcases.
  + assume Heq: 0 = 3.
    exact neq_3_0 Heq.
  + assume Heq: 0 = 10.
    exact neq_10_0 Heq.
  + assume Heq: 0 = 11.
    exact neq_11_0 Heq.
  + assume Heq: 0 = 12.
    exact neq_12_0 Heq.
  + assume Heq: 0 = 14.
    exact neq_14_0 Heq.
- assume Hcase: 6 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_1 : ~Adj17 6 1.
assume H: Adj17 6 1.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andER Hcase.
  assume Hjcases: 1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14.
  apply Hjcases.
  + assume Heq: 1 = 3.
    exact neq_3_1 Heq.
  + assume Heq: 1 = 10.
    exact neq_10_1 Heq.
  + assume Heq: 1 = 11.
    exact neq_11_1 Heq.
  + assume Heq: 1 = 12.
    exact neq_12_1 Heq.
  + assume Heq: 1 = 14.
    exact neq_14_1 Heq.
- assume Hcase: 6 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_2 : ~Adj17 6 2.
assume H: Adj17 6 2.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andER Hcase.
  assume Hjcases: 2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14.
  apply Hjcases.
  + assume Heq: 2 = 3.
    exact neq_3_2 Heq.
  + assume Heq: 2 = 10.
    exact neq_10_2 Heq.
  + assume Heq: 2 = 11.
    exact neq_11_2 Heq.
  + assume Heq: 2 = 12.
    exact neq_12_2 Heq.
  + assume Heq: 2 = 14.
    exact neq_14_2 Heq.
- assume Hcase: 6 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_4 : ~Adj17 6 4.
assume H: Adj17 6 4.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andER Hcase.
  assume Hjcases: 4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14.
  apply Hjcases.
  + assume Heq: 4 = 3.
    exact neq_4_3 Heq.
  + assume Heq: 4 = 10.
    exact neq_10_4 Heq.
  + assume Heq: 4 = 11.
    exact neq_11_4 Heq.
  + assume Heq: 4 = 12.
    exact neq_12_4 Heq.
  + assume Heq: 4 = 14.
    exact neq_14_4 Heq.
- assume Hcase: 6 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_5 : ~Adj17 6 5.
assume H: Adj17 6 5.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andER Hcase.
  assume Hjcases: 5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14.
  apply Hjcases.
  + assume Heq: 5 = 3.
    exact neq_5_3 Heq.
  + assume Heq: 5 = 10.
    exact neq_10_5 Heq.
  + assume Heq: 5 = 11.
    exact neq_11_5 Heq.
  + assume Heq: 5 = 12.
    exact neq_12_5 Heq.
  + assume Heq: 5 = 14.
    exact neq_14_5 Heq.
- assume Hcase: 6 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_6 : ~Adj17 6 6.
assume H: Adj17 6 6.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andER Hcase.
  assume Hjcases: 6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14.
  apply Hjcases.
  + assume Heq: 6 = 3.
    exact neq_6_3 Heq.
  + assume Heq: 6 = 10.
    exact neq_10_6 Heq.
  + assume Heq: 6 = 11.
    exact neq_11_6 Heq.
  + assume Heq: 6 = 12.
    exact neq_12_6 Heq.
  + assume Heq: 6 = 14.
    exact neq_14_6 Heq.
- assume Hcase: 6 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_7 : ~Adj17 6 7.
assume H: Adj17 6 7.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andER Hcase.
  assume Hjcases: 7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14.
  apply Hjcases.
  + assume Heq: 7 = 3.
    exact neq_7_3 Heq.
  + assume Heq: 7 = 10.
    exact neq_10_7 Heq.
  + assume Heq: 7 = 11.
    exact neq_11_7 Heq.
  + assume Heq: 7 = 12.
    exact neq_12_7 Heq.
  + assume Heq: 7 = 14.
    exact neq_14_7 Heq.
- assume Hcase: 6 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_8 : ~Adj17 6 8.
assume H: Adj17 6 8.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andER Hcase.
  assume Hjcases: 8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14.
  apply Hjcases.
  + assume Heq: 8 = 3.
    exact neq_8_3 Heq.
  + assume Heq: 8 = 10.
    exact neq_10_8 Heq.
  + assume Heq: 8 = 11.
    exact neq_11_8 Heq.
  + assume Heq: 8 = 12.
    exact neq_12_8 Heq.
  + assume Heq: 8 = 14.
    exact neq_14_8 Heq.
- assume Hcase: 6 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_9 : ~Adj17 6 9.
assume H: Adj17 6 9.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andER Hcase.
  assume Hjcases: 9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14.
  apply Hjcases.
  + assume Heq: 9 = 3.
    exact neq_9_3 Heq.
  + assume Heq: 9 = 10.
    exact neq_10_9 Heq.
  + assume Heq: 9 = 11.
    exact neq_11_9 Heq.
  + assume Heq: 9 = 12.
    exact neq_12_9 Heq.
  + assume Heq: 9 = 14.
    exact neq_14_9 Heq.
- assume Hcase: 6 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_13 : ~Adj17 6 13.
assume H: Adj17 6 13.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andER Hcase.
  assume Hjcases: 13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14.
  apply Hjcases.
  + assume Heq: 13 = 3.
    exact neq_13_3 Heq.
  + assume Heq: 13 = 10.
    exact neq_13_10 Heq.
  + assume Heq: 13 = 11.
    exact neq_13_11 Heq.
  + assume Heq: 13 = 12.
    exact neq_13_12 Heq.
  + assume Heq: 13 = 14.
    exact neq_14_13 Heq.
- assume Hcase: 6 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_15 : ~Adj17 6 15.
assume H: Adj17 6 15.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andER Hcase.
  assume Hjcases: 15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14.
  apply Hjcases.
  + assume Heq: 15 = 3.
    exact neq_15_3 Heq.
  + assume Heq: 15 = 10.
    exact neq_15_10 Heq.
  + assume Heq: 15 = 11.
    exact neq_15_11 Heq.
  + assume Heq: 15 = 12.
    exact neq_15_12 Heq.
  + assume Heq: 15 = 14.
    exact neq_15_14 Heq.
- assume Hcase: 6 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_6_16 : ~Adj17 6 16.
assume H: Adj17 6 16.
prove False.
apply H.
- assume Hcase: 6 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andER Hcase.
  assume Hjcases: 16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14.
  apply Hjcases.
  + assume Heq: 16 = 3.
    exact neq_16_3 Heq.
  + assume Heq: 16 = 10.
    exact neq_16_10 Heq.
  + assume Heq: 16 = 11.
    exact neq_16_11 Heq.
  + assume Heq: 16 = 12.
    exact neq_16_12 Heq.
  + assume Heq: 16 = 14.
    exact neq_16_14 Heq.
- assume Hcase: 6 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_not_7_0 : ~Adj17 7 0.
assume H: Adj17 7 0.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andER Hcase.
  assume Hjcases: 0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15.
  apply Hjcases.
  + assume Heq: 0 = 1.
    exact neq_1_0 Heq.
  + assume Heq: 0 = 4.
    exact neq_4_0 Heq.
  + assume Heq: 0 = 9.
    exact neq_9_0 Heq.
  + assume Heq: 0 = 10.
    exact neq_10_0 Heq.
  + assume Heq: 0 = 15.
    exact neq_15_0 Heq.
- assume Hcase: 7 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_2 : ~Adj17 7 2.
assume H: Adj17 7 2.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andER Hcase.
  assume Hjcases: 2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15.
  apply Hjcases.
  + assume Heq: 2 = 1.
    exact neq_2_1 Heq.
  + assume Heq: 2 = 4.
    exact neq_4_2 Heq.
  + assume Heq: 2 = 9.
    exact neq_9_2 Heq.
  + assume Heq: 2 = 10.
    exact neq_10_2 Heq.
  + assume Heq: 2 = 15.
    exact neq_15_2 Heq.
- assume Hcase: 7 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_3 : ~Adj17 7 3.
assume H: Adj17 7 3.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andER Hcase.
  assume Hjcases: 3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15.
  apply Hjcases.
  + assume Heq: 3 = 1.
    exact neq_3_1 Heq.
  + assume Heq: 3 = 4.
    exact neq_4_3 Heq.
  + assume Heq: 3 = 9.
    exact neq_9_3 Heq.
  + assume Heq: 3 = 10.
    exact neq_10_3 Heq.
  + assume Heq: 3 = 15.
    exact neq_15_3 Heq.
- assume Hcase: 7 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_5 : ~Adj17 7 5.
assume H: Adj17 7 5.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andER Hcase.
  assume Hjcases: 5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15.
  apply Hjcases.
  + assume Heq: 5 = 1.
    exact neq_5_1 Heq.
  + assume Heq: 5 = 4.
    exact neq_5_4 Heq.
  + assume Heq: 5 = 9.
    exact neq_9_5 Heq.
  + assume Heq: 5 = 10.
    exact neq_10_5 Heq.
  + assume Heq: 5 = 15.
    exact neq_15_5 Heq.
- assume Hcase: 7 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_6 : ~Adj17 7 6.
assume H: Adj17 7 6.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andER Hcase.
  assume Hjcases: 6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15.
  apply Hjcases.
  + assume Heq: 6 = 1.
    exact neq_6_1 Heq.
  + assume Heq: 6 = 4.
    exact neq_6_4 Heq.
  + assume Heq: 6 = 9.
    exact neq_9_6 Heq.
  + assume Heq: 6 = 10.
    exact neq_10_6 Heq.
  + assume Heq: 6 = 15.
    exact neq_15_6 Heq.
- assume Hcase: 7 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_7 : ~Adj17 7 7.
assume H: Adj17 7 7.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andER Hcase.
  assume Hjcases: 7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15.
  apply Hjcases.
  + assume Heq: 7 = 1.
    exact neq_7_1 Heq.
  + assume Heq: 7 = 4.
    exact neq_7_4 Heq.
  + assume Heq: 7 = 9.
    exact neq_9_7 Heq.
  + assume Heq: 7 = 10.
    exact neq_10_7 Heq.
  + assume Heq: 7 = 15.
    exact neq_15_7 Heq.
- assume Hcase: 7 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_8 : ~Adj17 7 8.
assume H: Adj17 7 8.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andER Hcase.
  assume Hjcases: 8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15.
  apply Hjcases.
  + assume Heq: 8 = 1.
    exact neq_8_1 Heq.
  + assume Heq: 8 = 4.
    exact neq_8_4 Heq.
  + assume Heq: 8 = 9.
    exact neq_9_8 Heq.
  + assume Heq: 8 = 10.
    exact neq_10_8 Heq.
  + assume Heq: 8 = 15.
    exact neq_15_8 Heq.
- assume Hcase: 7 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_11 : ~Adj17 7 11.
assume H: Adj17 7 11.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andER Hcase.
  assume Hjcases: 11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15.
  apply Hjcases.
  + assume Heq: 11 = 1.
    exact neq_11_1 Heq.
  + assume Heq: 11 = 4.
    exact neq_11_4 Heq.
  + assume Heq: 11 = 9.
    exact neq_11_9 Heq.
  + assume Heq: 11 = 10.
    exact neq_11_10 Heq.
  + assume Heq: 11 = 15.
    exact neq_15_11 Heq.
- assume Hcase: 7 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_12 : ~Adj17 7 12.
assume H: Adj17 7 12.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andER Hcase.
  assume Hjcases: 12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15.
  apply Hjcases.
  + assume Heq: 12 = 1.
    exact neq_12_1 Heq.
  + assume Heq: 12 = 4.
    exact neq_12_4 Heq.
  + assume Heq: 12 = 9.
    exact neq_12_9 Heq.
  + assume Heq: 12 = 10.
    exact neq_12_10 Heq.
  + assume Heq: 12 = 15.
    exact neq_15_12 Heq.
- assume Hcase: 7 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_13 : ~Adj17 7 13.
assume H: Adj17 7 13.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andER Hcase.
  assume Hjcases: 13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15.
  apply Hjcases.
  + assume Heq: 13 = 1.
    exact neq_13_1 Heq.
  + assume Heq: 13 = 4.
    exact neq_13_4 Heq.
  + assume Heq: 13 = 9.
    exact neq_13_9 Heq.
  + assume Heq: 13 = 10.
    exact neq_13_10 Heq.
  + assume Heq: 13 = 15.
    exact neq_15_13 Heq.
- assume Hcase: 7 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_14 : ~Adj17 7 14.
assume H: Adj17 7 14.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andER Hcase.
  assume Hjcases: 14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15.
  apply Hjcases.
  + assume Heq: 14 = 1.
    exact neq_14_1 Heq.
  + assume Heq: 14 = 4.
    exact neq_14_4 Heq.
  + assume Heq: 14 = 9.
    exact neq_14_9 Heq.
  + assume Heq: 14 = 10.
    exact neq_14_10 Heq.
  + assume Heq: 14 = 15.
    exact neq_15_14 Heq.
- assume Hcase: 7 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_7_16 : ~Adj17 7 16.
assume H: Adj17 7 16.
prove False.
apply H.
- assume Hcase: 7 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andER Hcase.
  assume Hjcases: 16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15.
  apply Hjcases.
  + assume Heq: 16 = 1.
    exact neq_16_1 Heq.
  + assume Heq: 16 = 4.
    exact neq_16_4 Heq.
  + assume Heq: 16 = 9.
    exact neq_16_9 Heq.
  + assume Heq: 16 = 10.
    exact neq_16_10 Heq.
  + assume Heq: 16 = 15.
    exact neq_16_15 Heq.
- assume Hcase: 7 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_not_8_0 : ~Adj17 8 0.
assume H: Adj17 8 0.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andER Hcase.
  assume Hjcases: 0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14.
  apply Hjcases.
  + assume Heq: 0 = 2.
    exact neq_2_0 Heq.
  + assume Heq: 0 = 3.
    exact neq_3_0 Heq.
  + assume Heq: 0 = 9.
    exact neq_9_0 Heq.
  + assume Heq: 0 = 11.
    exact neq_11_0 Heq.
  + assume Heq: 0 = 14.
    exact neq_14_0 Heq.
- assume Hcase: 8 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_1 : ~Adj17 8 1.
assume H: Adj17 8 1.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andER Hcase.
  assume Hjcases: 1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14.
  apply Hjcases.
  + assume Heq: 1 = 2.
    exact neq_2_1 Heq.
  + assume Heq: 1 = 3.
    exact neq_3_1 Heq.
  + assume Heq: 1 = 9.
    exact neq_9_1 Heq.
  + assume Heq: 1 = 11.
    exact neq_11_1 Heq.
  + assume Heq: 1 = 14.
    exact neq_14_1 Heq.
- assume Hcase: 8 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_4 : ~Adj17 8 4.
assume H: Adj17 8 4.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andER Hcase.
  assume Hjcases: 4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14.
  apply Hjcases.
  + assume Heq: 4 = 2.
    exact neq_4_2 Heq.
  + assume Heq: 4 = 3.
    exact neq_4_3 Heq.
  + assume Heq: 4 = 9.
    exact neq_9_4 Heq.
  + assume Heq: 4 = 11.
    exact neq_11_4 Heq.
  + assume Heq: 4 = 14.
    exact neq_14_4 Heq.
- assume Hcase: 8 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_5 : ~Adj17 8 5.
assume H: Adj17 8 5.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andER Hcase.
  assume Hjcases: 5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14.
  apply Hjcases.
  + assume Heq: 5 = 2.
    exact neq_5_2 Heq.
  + assume Heq: 5 = 3.
    exact neq_5_3 Heq.
  + assume Heq: 5 = 9.
    exact neq_9_5 Heq.
  + assume Heq: 5 = 11.
    exact neq_11_5 Heq.
  + assume Heq: 5 = 14.
    exact neq_14_5 Heq.
- assume Hcase: 8 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_6 : ~Adj17 8 6.
assume H: Adj17 8 6.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andER Hcase.
  assume Hjcases: 6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14.
  apply Hjcases.
  + assume Heq: 6 = 2.
    exact neq_6_2 Heq.
  + assume Heq: 6 = 3.
    exact neq_6_3 Heq.
  + assume Heq: 6 = 9.
    exact neq_9_6 Heq.
  + assume Heq: 6 = 11.
    exact neq_11_6 Heq.
  + assume Heq: 6 = 14.
    exact neq_14_6 Heq.
- assume Hcase: 8 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_7 : ~Adj17 8 7.
assume H: Adj17 8 7.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andER Hcase.
  assume Hjcases: 7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14.
  apply Hjcases.
  + assume Heq: 7 = 2.
    exact neq_7_2 Heq.
  + assume Heq: 7 = 3.
    exact neq_7_3 Heq.
  + assume Heq: 7 = 9.
    exact neq_9_7 Heq.
  + assume Heq: 7 = 11.
    exact neq_11_7 Heq.
  + assume Heq: 7 = 14.
    exact neq_14_7 Heq.
- assume Hcase: 8 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_8 : ~Adj17 8 8.
assume H: Adj17 8 8.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andER Hcase.
  assume Hjcases: 8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14.
  apply Hjcases.
  + assume Heq: 8 = 2.
    exact neq_8_2 Heq.
  + assume Heq: 8 = 3.
    exact neq_8_3 Heq.
  + assume Heq: 8 = 9.
    exact neq_9_8 Heq.
  + assume Heq: 8 = 11.
    exact neq_11_8 Heq.
  + assume Heq: 8 = 14.
    exact neq_14_8 Heq.
- assume Hcase: 8 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_10 : ~Adj17 8 10.
assume H: Adj17 8 10.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andER Hcase.
  assume Hjcases: 10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14.
  apply Hjcases.
  + assume Heq: 10 = 2.
    exact neq_10_2 Heq.
  + assume Heq: 10 = 3.
    exact neq_10_3 Heq.
  + assume Heq: 10 = 9.
    exact neq_10_9 Heq.
  + assume Heq: 10 = 11.
    exact neq_11_10 Heq.
  + assume Heq: 10 = 14.
    exact neq_14_10 Heq.
- assume Hcase: 8 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_12 : ~Adj17 8 12.
assume H: Adj17 8 12.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andER Hcase.
  assume Hjcases: 12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14.
  apply Hjcases.
  + assume Heq: 12 = 2.
    exact neq_12_2 Heq.
  + assume Heq: 12 = 3.
    exact neq_12_3 Heq.
  + assume Heq: 12 = 9.
    exact neq_12_9 Heq.
  + assume Heq: 12 = 11.
    exact neq_12_11 Heq.
  + assume Heq: 12 = 14.
    exact neq_14_12 Heq.
- assume Hcase: 8 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_13 : ~Adj17 8 13.
assume H: Adj17 8 13.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andER Hcase.
  assume Hjcases: 13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14.
  apply Hjcases.
  + assume Heq: 13 = 2.
    exact neq_13_2 Heq.
  + assume Heq: 13 = 3.
    exact neq_13_3 Heq.
  + assume Heq: 13 = 9.
    exact neq_13_9 Heq.
  + assume Heq: 13 = 11.
    exact neq_13_11 Heq.
  + assume Heq: 13 = 14.
    exact neq_14_13 Heq.
- assume Hcase: 8 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_15 : ~Adj17 8 15.
assume H: Adj17 8 15.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andER Hcase.
  assume Hjcases: 15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14.
  apply Hjcases.
  + assume Heq: 15 = 2.
    exact neq_15_2 Heq.
  + assume Heq: 15 = 3.
    exact neq_15_3 Heq.
  + assume Heq: 15 = 9.
    exact neq_15_9 Heq.
  + assume Heq: 15 = 11.
    exact neq_15_11 Heq.
  + assume Heq: 15 = 14.
    exact neq_15_14 Heq.
- assume Hcase: 8 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_8_16 : ~Adj17 8 16.
assume H: Adj17 8 16.
prove False.
apply H.
- assume Hcase: 8 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andER Hcase.
  assume Hjcases: 16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14.
  apply Hjcases.
  + assume Heq: 16 = 2.
    exact neq_16_2 Heq.
  + assume Heq: 16 = 3.
    exact neq_16_3 Heq.
  + assume Heq: 16 = 9.
    exact neq_16_9 Heq.
  + assume Heq: 16 = 11.
    exact neq_16_11 Heq.
  + assume Heq: 16 = 14.
    exact neq_16_14 Heq.
- assume Hcase: 8 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_not_9_1 : ~Adj17 9 1.
assume H: Adj17 9 1.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andER Hcase.
  assume Hjcases: 1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12.
  apply Hjcases.
  + assume Heq: 1 = 0.
    exact neq_1_0 Heq.
  + assume Heq: 1 = 5.
    exact neq_5_1 Heq.
  + assume Heq: 1 = 7.
    exact neq_7_1 Heq.
  + assume Heq: 1 = 8.
    exact neq_8_1 Heq.
  + assume Heq: 1 = 12.
    exact neq_12_1 Heq.
- assume Hcase: 9 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_2 : ~Adj17 9 2.
assume H: Adj17 9 2.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andER Hcase.
  assume Hjcases: 2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12.
  apply Hjcases.
  + assume Heq: 2 = 0.
    exact neq_2_0 Heq.
  + assume Heq: 2 = 5.
    exact neq_5_2 Heq.
  + assume Heq: 2 = 7.
    exact neq_7_2 Heq.
  + assume Heq: 2 = 8.
    exact neq_8_2 Heq.
  + assume Heq: 2 = 12.
    exact neq_12_2 Heq.
- assume Hcase: 9 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_3 : ~Adj17 9 3.
assume H: Adj17 9 3.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andER Hcase.
  assume Hjcases: 3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12.
  apply Hjcases.
  + assume Heq: 3 = 0.
    exact neq_3_0 Heq.
  + assume Heq: 3 = 5.
    exact neq_5_3 Heq.
  + assume Heq: 3 = 7.
    exact neq_7_3 Heq.
  + assume Heq: 3 = 8.
    exact neq_8_3 Heq.
  + assume Heq: 3 = 12.
    exact neq_12_3 Heq.
- assume Hcase: 9 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_4 : ~Adj17 9 4.
assume H: Adj17 9 4.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andER Hcase.
  assume Hjcases: 4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12.
  apply Hjcases.
  + assume Heq: 4 = 0.
    exact neq_4_0 Heq.
  + assume Heq: 4 = 5.
    exact neq_5_4 Heq.
  + assume Heq: 4 = 7.
    exact neq_7_4 Heq.
  + assume Heq: 4 = 8.
    exact neq_8_4 Heq.
  + assume Heq: 4 = 12.
    exact neq_12_4 Heq.
- assume Hcase: 9 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_6 : ~Adj17 9 6.
assume H: Adj17 9 6.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andER Hcase.
  assume Hjcases: 6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12.
  apply Hjcases.
  + assume Heq: 6 = 0.
    exact neq_6_0 Heq.
  + assume Heq: 6 = 5.
    exact neq_6_5 Heq.
  + assume Heq: 6 = 7.
    exact neq_7_6 Heq.
  + assume Heq: 6 = 8.
    exact neq_8_6 Heq.
  + assume Heq: 6 = 12.
    exact neq_12_6 Heq.
- assume Hcase: 9 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_9 : ~Adj17 9 9.
assume H: Adj17 9 9.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andER Hcase.
  assume Hjcases: 9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12.
  apply Hjcases.
  + assume Heq: 9 = 0.
    exact neq_9_0 Heq.
  + assume Heq: 9 = 5.
    exact neq_9_5 Heq.
  + assume Heq: 9 = 7.
    exact neq_9_7 Heq.
  + assume Heq: 9 = 8.
    exact neq_9_8 Heq.
  + assume Heq: 9 = 12.
    exact neq_12_9 Heq.
- assume Hcase: 9 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_10 : ~Adj17 9 10.
assume H: Adj17 9 10.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andER Hcase.
  assume Hjcases: 10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12.
  apply Hjcases.
  + assume Heq: 10 = 0.
    exact neq_10_0 Heq.
  + assume Heq: 10 = 5.
    exact neq_10_5 Heq.
  + assume Heq: 10 = 7.
    exact neq_10_7 Heq.
  + assume Heq: 10 = 8.
    exact neq_10_8 Heq.
  + assume Heq: 10 = 12.
    exact neq_12_10 Heq.
- assume Hcase: 9 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_11 : ~Adj17 9 11.
assume H: Adj17 9 11.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andER Hcase.
  assume Hjcases: 11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12.
  apply Hjcases.
  + assume Heq: 11 = 0.
    exact neq_11_0 Heq.
  + assume Heq: 11 = 5.
    exact neq_11_5 Heq.
  + assume Heq: 11 = 7.
    exact neq_11_7 Heq.
  + assume Heq: 11 = 8.
    exact neq_11_8 Heq.
  + assume Heq: 11 = 12.
    exact neq_12_11 Heq.
- assume Hcase: 9 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_13 : ~Adj17 9 13.
assume H: Adj17 9 13.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andER Hcase.
  assume Hjcases: 13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12.
  apply Hjcases.
  + assume Heq: 13 = 0.
    exact neq_13_0 Heq.
  + assume Heq: 13 = 5.
    exact neq_13_5 Heq.
  + assume Heq: 13 = 7.
    exact neq_13_7 Heq.
  + assume Heq: 13 = 8.
    exact neq_13_8 Heq.
  + assume Heq: 13 = 12.
    exact neq_13_12 Heq.
- assume Hcase: 9 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_14 : ~Adj17 9 14.
assume H: Adj17 9 14.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andER Hcase.
  assume Hjcases: 14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12.
  apply Hjcases.
  + assume Heq: 14 = 0.
    exact neq_14_0 Heq.
  + assume Heq: 14 = 5.
    exact neq_14_5 Heq.
  + assume Heq: 14 = 7.
    exact neq_14_7 Heq.
  + assume Heq: 14 = 8.
    exact neq_14_8 Heq.
  + assume Heq: 14 = 12.
    exact neq_14_12 Heq.
- assume Hcase: 9 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_15 : ~Adj17 9 15.
assume H: Adj17 9 15.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andER Hcase.
  assume Hjcases: 15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12.
  apply Hjcases.
  + assume Heq: 15 = 0.
    exact neq_15_0 Heq.
  + assume Heq: 15 = 5.
    exact neq_15_5 Heq.
  + assume Heq: 15 = 7.
    exact neq_15_7 Heq.
  + assume Heq: 15 = 8.
    exact neq_15_8 Heq.
  + assume Heq: 15 = 12.
    exact neq_15_12 Heq.
- assume Hcase: 9 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_9_16 : ~Adj17 9 16.
assume H: Adj17 9 16.
prove False.
apply H.
- assume Hcase: 9 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andER Hcase.
  assume Hjcases: 16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12.
  apply Hjcases.
  + assume Heq: 16 = 0.
    exact neq_16_0 Heq.
  + assume Heq: 16 = 5.
    exact neq_16_5 Heq.
  + assume Heq: 16 = 7.
    exact neq_16_7 Heq.
  + assume Heq: 16 = 8.
    exact neq_16_8 Heq.
  + assume Heq: 16 = 12.
    exact neq_16_12 Heq.
- assume Hcase: 9 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_not_10_0 : ~Adj17 10 0.
assume H: Adj17 10 0.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andER Hcase.
  assume Hjcases: 0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16.
  apply Hjcases.
  + assume Heq: 0 = 2.
    exact neq_2_0 Heq.
  + assume Heq: 0 = 5.
    exact neq_5_0 Heq.
  + assume Heq: 0 = 6.
    exact neq_6_0 Heq.
  + assume Heq: 0 = 7.
    exact neq_7_0 Heq.
  + assume Heq: 0 = 16.
    exact neq_16_0 Heq.
- assume Hcase: 10 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_1 : ~Adj17 10 1.
assume H: Adj17 10 1.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andER Hcase.
  assume Hjcases: 1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16.
  apply Hjcases.
  + assume Heq: 1 = 2.
    exact neq_2_1 Heq.
  + assume Heq: 1 = 5.
    exact neq_5_1 Heq.
  + assume Heq: 1 = 6.
    exact neq_6_1 Heq.
  + assume Heq: 1 = 7.
    exact neq_7_1 Heq.
  + assume Heq: 1 = 16.
    exact neq_16_1 Heq.
- assume Hcase: 10 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_3 : ~Adj17 10 3.
assume H: Adj17 10 3.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andER Hcase.
  assume Hjcases: 3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16.
  apply Hjcases.
  + assume Heq: 3 = 2.
    exact neq_3_2 Heq.
  + assume Heq: 3 = 5.
    exact neq_5_3 Heq.
  + assume Heq: 3 = 6.
    exact neq_6_3 Heq.
  + assume Heq: 3 = 7.
    exact neq_7_3 Heq.
  + assume Heq: 3 = 16.
    exact neq_16_3 Heq.
- assume Hcase: 10 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_4 : ~Adj17 10 4.
assume H: Adj17 10 4.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andER Hcase.
  assume Hjcases: 4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16.
  apply Hjcases.
  + assume Heq: 4 = 2.
    exact neq_4_2 Heq.
  + assume Heq: 4 = 5.
    exact neq_5_4 Heq.
  + assume Heq: 4 = 6.
    exact neq_6_4 Heq.
  + assume Heq: 4 = 7.
    exact neq_7_4 Heq.
  + assume Heq: 4 = 16.
    exact neq_16_4 Heq.
- assume Hcase: 10 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_8 : ~Adj17 10 8.
assume H: Adj17 10 8.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andER Hcase.
  assume Hjcases: 8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16.
  apply Hjcases.
  + assume Heq: 8 = 2.
    exact neq_8_2 Heq.
  + assume Heq: 8 = 5.
    exact neq_8_5 Heq.
  + assume Heq: 8 = 6.
    exact neq_8_6 Heq.
  + assume Heq: 8 = 7.
    exact neq_8_7 Heq.
  + assume Heq: 8 = 16.
    exact neq_16_8 Heq.
- assume Hcase: 10 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_9 : ~Adj17 10 9.
assume H: Adj17 10 9.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andER Hcase.
  assume Hjcases: 9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16.
  apply Hjcases.
  + assume Heq: 9 = 2.
    exact neq_9_2 Heq.
  + assume Heq: 9 = 5.
    exact neq_9_5 Heq.
  + assume Heq: 9 = 6.
    exact neq_9_6 Heq.
  + assume Heq: 9 = 7.
    exact neq_9_7 Heq.
  + assume Heq: 9 = 16.
    exact neq_16_9 Heq.
- assume Hcase: 10 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_10 : ~Adj17 10 10.
assume H: Adj17 10 10.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andER Hcase.
  assume Hjcases: 10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16.
  apply Hjcases.
  + assume Heq: 10 = 2.
    exact neq_10_2 Heq.
  + assume Heq: 10 = 5.
    exact neq_10_5 Heq.
  + assume Heq: 10 = 6.
    exact neq_10_6 Heq.
  + assume Heq: 10 = 7.
    exact neq_10_7 Heq.
  + assume Heq: 10 = 16.
    exact neq_16_10 Heq.
- assume Hcase: 10 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_11 : ~Adj17 10 11.
assume H: Adj17 10 11.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andER Hcase.
  assume Hjcases: 11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16.
  apply Hjcases.
  + assume Heq: 11 = 2.
    exact neq_11_2 Heq.
  + assume Heq: 11 = 5.
    exact neq_11_5 Heq.
  + assume Heq: 11 = 6.
    exact neq_11_6 Heq.
  + assume Heq: 11 = 7.
    exact neq_11_7 Heq.
  + assume Heq: 11 = 16.
    exact neq_16_11 Heq.
- assume Hcase: 10 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_12 : ~Adj17 10 12.
assume H: Adj17 10 12.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andER Hcase.
  assume Hjcases: 12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16.
  apply Hjcases.
  + assume Heq: 12 = 2.
    exact neq_12_2 Heq.
  + assume Heq: 12 = 5.
    exact neq_12_5 Heq.
  + assume Heq: 12 = 6.
    exact neq_12_6 Heq.
  + assume Heq: 12 = 7.
    exact neq_12_7 Heq.
  + assume Heq: 12 = 16.
    exact neq_16_12 Heq.
- assume Hcase: 10 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_13 : ~Adj17 10 13.
assume H: Adj17 10 13.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andER Hcase.
  assume Hjcases: 13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16.
  apply Hjcases.
  + assume Heq: 13 = 2.
    exact neq_13_2 Heq.
  + assume Heq: 13 = 5.
    exact neq_13_5 Heq.
  + assume Heq: 13 = 6.
    exact neq_13_6 Heq.
  + assume Heq: 13 = 7.
    exact neq_13_7 Heq.
  + assume Heq: 13 = 16.
    exact neq_16_13 Heq.
- assume Hcase: 10 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_14 : ~Adj17 10 14.
assume H: Adj17 10 14.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andER Hcase.
  assume Hjcases: 14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16.
  apply Hjcases.
  + assume Heq: 14 = 2.
    exact neq_14_2 Heq.
  + assume Heq: 14 = 5.
    exact neq_14_5 Heq.
  + assume Heq: 14 = 6.
    exact neq_14_6 Heq.
  + assume Heq: 14 = 7.
    exact neq_14_7 Heq.
  + assume Heq: 14 = 16.
    exact neq_16_14 Heq.
- assume Hcase: 10 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_10_15 : ~Adj17 10 15.
assume H: Adj17 10 15.
prove False.
apply H.
- assume Hcase: 10 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andER Hcase.
  assume Hjcases: 15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16.
  apply Hjcases.
  + assume Heq: 15 = 2.
    exact neq_15_2 Heq.
  + assume Heq: 15 = 5.
    exact neq_15_5 Heq.
  + assume Heq: 15 = 6.
    exact neq_15_6 Heq.
  + assume Heq: 15 = 7.
    exact neq_15_7 Heq.
  + assume Heq: 15 = 16.
    exact neq_16_15 Heq.
- assume Hcase: 10 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_not_11_0 : ~Adj17 11 0.
assume H: Adj17 11 0.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andER Hcase.
  assume Hjcases: 0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15.
  apply Hjcases.
  + assume Heq: 0 = 1.
    exact neq_1_0 Heq.
  + assume Heq: 0 = 5.
    exact neq_5_0 Heq.
  + assume Heq: 0 = 6.
    exact neq_6_0 Heq.
  + assume Heq: 0 = 8.
    exact neq_8_0 Heq.
  + assume Heq: 0 = 15.
    exact neq_15_0 Heq.
- assume Hcase: 11 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_2 : ~Adj17 11 2.
assume H: Adj17 11 2.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andER Hcase.
  assume Hjcases: 2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15.
  apply Hjcases.
  + assume Heq: 2 = 1.
    exact neq_2_1 Heq.
  + assume Heq: 2 = 5.
    exact neq_5_2 Heq.
  + assume Heq: 2 = 6.
    exact neq_6_2 Heq.
  + assume Heq: 2 = 8.
    exact neq_8_2 Heq.
  + assume Heq: 2 = 15.
    exact neq_15_2 Heq.
- assume Hcase: 11 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_3 : ~Adj17 11 3.
assume H: Adj17 11 3.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andER Hcase.
  assume Hjcases: 3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15.
  apply Hjcases.
  + assume Heq: 3 = 1.
    exact neq_3_1 Heq.
  + assume Heq: 3 = 5.
    exact neq_5_3 Heq.
  + assume Heq: 3 = 6.
    exact neq_6_3 Heq.
  + assume Heq: 3 = 8.
    exact neq_8_3 Heq.
  + assume Heq: 3 = 15.
    exact neq_15_3 Heq.
- assume Hcase: 11 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_4 : ~Adj17 11 4.
assume H: Adj17 11 4.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andER Hcase.
  assume Hjcases: 4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15.
  apply Hjcases.
  + assume Heq: 4 = 1.
    exact neq_4_1 Heq.
  + assume Heq: 4 = 5.
    exact neq_5_4 Heq.
  + assume Heq: 4 = 6.
    exact neq_6_4 Heq.
  + assume Heq: 4 = 8.
    exact neq_8_4 Heq.
  + assume Heq: 4 = 15.
    exact neq_15_4 Heq.
- assume Hcase: 11 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_7 : ~Adj17 11 7.
assume H: Adj17 11 7.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andER Hcase.
  assume Hjcases: 7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15.
  apply Hjcases.
  + assume Heq: 7 = 1.
    exact neq_7_1 Heq.
  + assume Heq: 7 = 5.
    exact neq_7_5 Heq.
  + assume Heq: 7 = 6.
    exact neq_7_6 Heq.
  + assume Heq: 7 = 8.
    exact neq_8_7 Heq.
  + assume Heq: 7 = 15.
    exact neq_15_7 Heq.
- assume Hcase: 11 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_9 : ~Adj17 11 9.
assume H: Adj17 11 9.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andER Hcase.
  assume Hjcases: 9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15.
  apply Hjcases.
  + assume Heq: 9 = 1.
    exact neq_9_1 Heq.
  + assume Heq: 9 = 5.
    exact neq_9_5 Heq.
  + assume Heq: 9 = 6.
    exact neq_9_6 Heq.
  + assume Heq: 9 = 8.
    exact neq_9_8 Heq.
  + assume Heq: 9 = 15.
    exact neq_15_9 Heq.
- assume Hcase: 11 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_10 : ~Adj17 11 10.
assume H: Adj17 11 10.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andER Hcase.
  assume Hjcases: 10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15.
  apply Hjcases.
  + assume Heq: 10 = 1.
    exact neq_10_1 Heq.
  + assume Heq: 10 = 5.
    exact neq_10_5 Heq.
  + assume Heq: 10 = 6.
    exact neq_10_6 Heq.
  + assume Heq: 10 = 8.
    exact neq_10_8 Heq.
  + assume Heq: 10 = 15.
    exact neq_15_10 Heq.
- assume Hcase: 11 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_11 : ~Adj17 11 11.
assume H: Adj17 11 11.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andER Hcase.
  assume Hjcases: 11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15.
  apply Hjcases.
  + assume Heq: 11 = 1.
    exact neq_11_1 Heq.
  + assume Heq: 11 = 5.
    exact neq_11_5 Heq.
  + assume Heq: 11 = 6.
    exact neq_11_6 Heq.
  + assume Heq: 11 = 8.
    exact neq_11_8 Heq.
  + assume Heq: 11 = 15.
    exact neq_15_11 Heq.
- assume Hcase: 11 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_12 : ~Adj17 11 12.
assume H: Adj17 11 12.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andER Hcase.
  assume Hjcases: 12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15.
  apply Hjcases.
  + assume Heq: 12 = 1.
    exact neq_12_1 Heq.
  + assume Heq: 12 = 5.
    exact neq_12_5 Heq.
  + assume Heq: 12 = 6.
    exact neq_12_6 Heq.
  + assume Heq: 12 = 8.
    exact neq_12_8 Heq.
  + assume Heq: 12 = 15.
    exact neq_15_12 Heq.
- assume Hcase: 11 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_13 : ~Adj17 11 13.
assume H: Adj17 11 13.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andER Hcase.
  assume Hjcases: 13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15.
  apply Hjcases.
  + assume Heq: 13 = 1.
    exact neq_13_1 Heq.
  + assume Heq: 13 = 5.
    exact neq_13_5 Heq.
  + assume Heq: 13 = 6.
    exact neq_13_6 Heq.
  + assume Heq: 13 = 8.
    exact neq_13_8 Heq.
  + assume Heq: 13 = 15.
    exact neq_15_13 Heq.
- assume Hcase: 11 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_14 : ~Adj17 11 14.
assume H: Adj17 11 14.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andER Hcase.
  assume Hjcases: 14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15.
  apply Hjcases.
  + assume Heq: 14 = 1.
    exact neq_14_1 Heq.
  + assume Heq: 14 = 5.
    exact neq_14_5 Heq.
  + assume Heq: 14 = 6.
    exact neq_14_6 Heq.
  + assume Heq: 14 = 8.
    exact neq_14_8 Heq.
  + assume Heq: 14 = 15.
    exact neq_15_14 Heq.
- assume Hcase: 11 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_11_16 : ~Adj17 11 16.
assume H: Adj17 11 16.
prove False.
apply H.
- assume Hcase: 11 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andER Hcase.
  assume Hjcases: 16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15.
  apply Hjcases.
  + assume Heq: 16 = 1.
    exact neq_16_1 Heq.
  + assume Heq: 16 = 5.
    exact neq_16_5 Heq.
  + assume Heq: 16 = 6.
    exact neq_16_6 Heq.
  + assume Heq: 16 = 8.
    exact neq_16_8 Heq.
  + assume Heq: 16 = 15.
    exact neq_16_15 Heq.
- assume Hcase: 11 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_not_12_0 : ~Adj17 12 0.
assume H: Adj17 12 0.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andER Hcase.
  assume Hjcases: 0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13.
  apply Hjcases.
  + assume Heq: 0 = 2.
    exact neq_2_0 Heq.
  + assume Heq: 0 = 4.
    exact neq_4_0 Heq.
  + assume Heq: 0 = 6.
    exact neq_6_0 Heq.
  + assume Heq: 0 = 9.
    exact neq_9_0 Heq.
  + assume Heq: 0 = 13.
    exact neq_13_0 Heq.
- assume Hcase: 12 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_1 : ~Adj17 12 1.
assume H: Adj17 12 1.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andER Hcase.
  assume Hjcases: 1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13.
  apply Hjcases.
  + assume Heq: 1 = 2.
    exact neq_2_1 Heq.
  + assume Heq: 1 = 4.
    exact neq_4_1 Heq.
  + assume Heq: 1 = 6.
    exact neq_6_1 Heq.
  + assume Heq: 1 = 9.
    exact neq_9_1 Heq.
  + assume Heq: 1 = 13.
    exact neq_13_1 Heq.
- assume Hcase: 12 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_3 : ~Adj17 12 3.
assume H: Adj17 12 3.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andER Hcase.
  assume Hjcases: 3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13.
  apply Hjcases.
  + assume Heq: 3 = 2.
    exact neq_3_2 Heq.
  + assume Heq: 3 = 4.
    exact neq_4_3 Heq.
  + assume Heq: 3 = 6.
    exact neq_6_3 Heq.
  + assume Heq: 3 = 9.
    exact neq_9_3 Heq.
  + assume Heq: 3 = 13.
    exact neq_13_3 Heq.
- assume Hcase: 12 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_5 : ~Adj17 12 5.
assume H: Adj17 12 5.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andER Hcase.
  assume Hjcases: 5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13.
  apply Hjcases.
  + assume Heq: 5 = 2.
    exact neq_5_2 Heq.
  + assume Heq: 5 = 4.
    exact neq_5_4 Heq.
  + assume Heq: 5 = 6.
    exact neq_6_5 Heq.
  + assume Heq: 5 = 9.
    exact neq_9_5 Heq.
  + assume Heq: 5 = 13.
    exact neq_13_5 Heq.
- assume Hcase: 12 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_7 : ~Adj17 12 7.
assume H: Adj17 12 7.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andER Hcase.
  assume Hjcases: 7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13.
  apply Hjcases.
  + assume Heq: 7 = 2.
    exact neq_7_2 Heq.
  + assume Heq: 7 = 4.
    exact neq_7_4 Heq.
  + assume Heq: 7 = 6.
    exact neq_7_6 Heq.
  + assume Heq: 7 = 9.
    exact neq_9_7 Heq.
  + assume Heq: 7 = 13.
    exact neq_13_7 Heq.
- assume Hcase: 12 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_8 : ~Adj17 12 8.
assume H: Adj17 12 8.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andER Hcase.
  assume Hjcases: 8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13.
  apply Hjcases.
  + assume Heq: 8 = 2.
    exact neq_8_2 Heq.
  + assume Heq: 8 = 4.
    exact neq_8_4 Heq.
  + assume Heq: 8 = 6.
    exact neq_8_6 Heq.
  + assume Heq: 8 = 9.
    exact neq_9_8 Heq.
  + assume Heq: 8 = 13.
    exact neq_13_8 Heq.
- assume Hcase: 12 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_10 : ~Adj17 12 10.
assume H: Adj17 12 10.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andER Hcase.
  assume Hjcases: 10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13.
  apply Hjcases.
  + assume Heq: 10 = 2.
    exact neq_10_2 Heq.
  + assume Heq: 10 = 4.
    exact neq_10_4 Heq.
  + assume Heq: 10 = 6.
    exact neq_10_6 Heq.
  + assume Heq: 10 = 9.
    exact neq_10_9 Heq.
  + assume Heq: 10 = 13.
    exact neq_13_10 Heq.
- assume Hcase: 12 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_11 : ~Adj17 12 11.
assume H: Adj17 12 11.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andER Hcase.
  assume Hjcases: 11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13.
  apply Hjcases.
  + assume Heq: 11 = 2.
    exact neq_11_2 Heq.
  + assume Heq: 11 = 4.
    exact neq_11_4 Heq.
  + assume Heq: 11 = 6.
    exact neq_11_6 Heq.
  + assume Heq: 11 = 9.
    exact neq_11_9 Heq.
  + assume Heq: 11 = 13.
    exact neq_13_11 Heq.
- assume Hcase: 12 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_12 : ~Adj17 12 12.
assume H: Adj17 12 12.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andER Hcase.
  assume Hjcases: 12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13.
  apply Hjcases.
  + assume Heq: 12 = 2.
    exact neq_12_2 Heq.
  + assume Heq: 12 = 4.
    exact neq_12_4 Heq.
  + assume Heq: 12 = 6.
    exact neq_12_6 Heq.
  + assume Heq: 12 = 9.
    exact neq_12_9 Heq.
  + assume Heq: 12 = 13.
    exact neq_13_12 Heq.
- assume Hcase: 12 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_14 : ~Adj17 12 14.
assume H: Adj17 12 14.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andER Hcase.
  assume Hjcases: 14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13.
  apply Hjcases.
  + assume Heq: 14 = 2.
    exact neq_14_2 Heq.
  + assume Heq: 14 = 4.
    exact neq_14_4 Heq.
  + assume Heq: 14 = 6.
    exact neq_14_6 Heq.
  + assume Heq: 14 = 9.
    exact neq_14_9 Heq.
  + assume Heq: 14 = 13.
    exact neq_14_13 Heq.
- assume Hcase: 12 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_15 : ~Adj17 12 15.
assume H: Adj17 12 15.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andER Hcase.
  assume Hjcases: 15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13.
  apply Hjcases.
  + assume Heq: 15 = 2.
    exact neq_15_2 Heq.
  + assume Heq: 15 = 4.
    exact neq_15_4 Heq.
  + assume Heq: 15 = 6.
    exact neq_15_6 Heq.
  + assume Heq: 15 = 9.
    exact neq_15_9 Heq.
  + assume Heq: 15 = 13.
    exact neq_15_13 Heq.
- assume Hcase: 12 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_12_16 : ~Adj17 12 16.
assume H: Adj17 12 16.
prove False.
apply H.
- assume Hcase: 12 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andER Hcase.
  assume Hjcases: 16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13.
  apply Hjcases.
  + assume Heq: 16 = 2.
    exact neq_16_2 Heq.
  + assume Heq: 16 = 4.
    exact neq_16_4 Heq.
  + assume Heq: 16 = 6.
    exact neq_16_6 Heq.
  + assume Heq: 16 = 9.
    exact neq_16_9 Heq.
  + assume Heq: 16 = 13.
    exact neq_16_13 Heq.
- assume Hcase: 12 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_not_13_0 : ~Adj17 13 0.
assume H: Adj17 13 0.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (0 = 9 \/ 0 = 14 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (0 = 7 \/ 0 = 11 \/ 0 = 13 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (0 = 8 \/ 0 = 10 \/ 0 = 12 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (0 = 6 \/ 0 = 8 \/ 0 = 13 \/ 0 = 15 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (0 = 5 \/ 0 = 7 \/ 0 = 12 \/ 0 = 14 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 11 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (0 = 3 \/ 0 = 10 \/ 0 = 11 \/ 0 = 12 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (0 = 1 \/ 0 = 4 \/ 0 = 9 \/ 0 = 10 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (0 = 2 \/ 0 = 3 \/ 0 = 9 \/ 0 = 11 \/ 0 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (0 = 0 \/ 0 = 5 \/ 0 = 7 \/ 0 = 8 \/ 0 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (0 = 2 \/ 0 = 5 \/ 0 = 6 \/ 0 = 7 \/ 0 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (0 = 1 \/ 0 = 5 \/ 0 = 6 \/ 0 = 8 \/ 0 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (0 = 2 \/ 0 = 4 \/ 0 = 6 \/ 0 = 9 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14).
  apply andER Hcase.
  assume Hjcases: 0 = 1 \/ 0 = 3 \/ 0 = 5 \/ 0 = 12 \/ 0 = 14.
  apply Hjcases.
  + assume Heq: 0 = 1.
    exact neq_1_0 Heq.
  + assume Heq: 0 = 3.
    exact neq_3_0 Heq.
  + assume Heq: 0 = 5.
    exact neq_5_0 Heq.
  + assume Heq: 0 = 12.
    exact neq_12_0 Heq.
  + assume Heq: 0 = 14.
    exact neq_14_0 Heq.
- assume Hcase: 13 = 14 /\ (0 = 0 \/ 0 = 4 \/ 0 = 6 \/ 0 = 8 \/ 0 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (0 = 0 \/ 0 = 2 \/ 0 = 3 \/ 0 = 7 \/ 0 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (0 = 0 \/ 0 = 1 \/ 0 = 3 \/ 0 = 4 \/ 0 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_2 : ~Adj17 13 2.
assume H: Adj17 13 2.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andER Hcase.
  assume Hjcases: 2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14.
  apply Hjcases.
  + assume Heq: 2 = 1.
    exact neq_2_1 Heq.
  + assume Heq: 2 = 3.
    exact neq_3_2 Heq.
  + assume Heq: 2 = 5.
    exact neq_5_2 Heq.
  + assume Heq: 2 = 12.
    exact neq_12_2 Heq.
  + assume Heq: 2 = 14.
    exact neq_14_2 Heq.
- assume Hcase: 13 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_4 : ~Adj17 13 4.
assume H: Adj17 13 4.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andER Hcase.
  assume Hjcases: 4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14.
  apply Hjcases.
  + assume Heq: 4 = 1.
    exact neq_4_1 Heq.
  + assume Heq: 4 = 3.
    exact neq_4_3 Heq.
  + assume Heq: 4 = 5.
    exact neq_5_4 Heq.
  + assume Heq: 4 = 12.
    exact neq_12_4 Heq.
  + assume Heq: 4 = 14.
    exact neq_14_4 Heq.
- assume Hcase: 13 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_6 : ~Adj17 13 6.
assume H: Adj17 13 6.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andER Hcase.
  assume Hjcases: 6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14.
  apply Hjcases.
  + assume Heq: 6 = 1.
    exact neq_6_1 Heq.
  + assume Heq: 6 = 3.
    exact neq_6_3 Heq.
  + assume Heq: 6 = 5.
    exact neq_6_5 Heq.
  + assume Heq: 6 = 12.
    exact neq_12_6 Heq.
  + assume Heq: 6 = 14.
    exact neq_14_6 Heq.
- assume Hcase: 13 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_7 : ~Adj17 13 7.
assume H: Adj17 13 7.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andER Hcase.
  assume Hjcases: 7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14.
  apply Hjcases.
  + assume Heq: 7 = 1.
    exact neq_7_1 Heq.
  + assume Heq: 7 = 3.
    exact neq_7_3 Heq.
  + assume Heq: 7 = 5.
    exact neq_7_5 Heq.
  + assume Heq: 7 = 12.
    exact neq_12_7 Heq.
  + assume Heq: 7 = 14.
    exact neq_14_7 Heq.
- assume Hcase: 13 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_8 : ~Adj17 13 8.
assume H: Adj17 13 8.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andER Hcase.
  assume Hjcases: 8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14.
  apply Hjcases.
  + assume Heq: 8 = 1.
    exact neq_8_1 Heq.
  + assume Heq: 8 = 3.
    exact neq_8_3 Heq.
  + assume Heq: 8 = 5.
    exact neq_8_5 Heq.
  + assume Heq: 8 = 12.
    exact neq_12_8 Heq.
  + assume Heq: 8 = 14.
    exact neq_14_8 Heq.
- assume Hcase: 13 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_9 : ~Adj17 13 9.
assume H: Adj17 13 9.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andER Hcase.
  assume Hjcases: 9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14.
  apply Hjcases.
  + assume Heq: 9 = 1.
    exact neq_9_1 Heq.
  + assume Heq: 9 = 3.
    exact neq_9_3 Heq.
  + assume Heq: 9 = 5.
    exact neq_9_5 Heq.
  + assume Heq: 9 = 12.
    exact neq_12_9 Heq.
  + assume Heq: 9 = 14.
    exact neq_14_9 Heq.
- assume Hcase: 13 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_10 : ~Adj17 13 10.
assume H: Adj17 13 10.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andER Hcase.
  assume Hjcases: 10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14.
  apply Hjcases.
  + assume Heq: 10 = 1.
    exact neq_10_1 Heq.
  + assume Heq: 10 = 3.
    exact neq_10_3 Heq.
  + assume Heq: 10 = 5.
    exact neq_10_5 Heq.
  + assume Heq: 10 = 12.
    exact neq_12_10 Heq.
  + assume Heq: 10 = 14.
    exact neq_14_10 Heq.
- assume Hcase: 13 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_11 : ~Adj17 13 11.
assume H: Adj17 13 11.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andER Hcase.
  assume Hjcases: 11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14.
  apply Hjcases.
  + assume Heq: 11 = 1.
    exact neq_11_1 Heq.
  + assume Heq: 11 = 3.
    exact neq_11_3 Heq.
  + assume Heq: 11 = 5.
    exact neq_11_5 Heq.
  + assume Heq: 11 = 12.
    exact neq_12_11 Heq.
  + assume Heq: 11 = 14.
    exact neq_14_11 Heq.
- assume Hcase: 13 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_13 : ~Adj17 13 13.
assume H: Adj17 13 13.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andER Hcase.
  assume Hjcases: 13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14.
  apply Hjcases.
  + assume Heq: 13 = 1.
    exact neq_13_1 Heq.
  + assume Heq: 13 = 3.
    exact neq_13_3 Heq.
  + assume Heq: 13 = 5.
    exact neq_13_5 Heq.
  + assume Heq: 13 = 12.
    exact neq_13_12 Heq.
  + assume Heq: 13 = 14.
    exact neq_14_13 Heq.
- assume Hcase: 13 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_15 : ~Adj17 13 15.
assume H: Adj17 13 15.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andER Hcase.
  assume Hjcases: 15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14.
  apply Hjcases.
  + assume Heq: 15 = 1.
    exact neq_15_1 Heq.
  + assume Heq: 15 = 3.
    exact neq_15_3 Heq.
  + assume Heq: 15 = 5.
    exact neq_15_5 Heq.
  + assume Heq: 15 = 12.
    exact neq_15_12 Heq.
  + assume Heq: 15 = 14.
    exact neq_15_14 Heq.
- assume Hcase: 13 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_13_16 : ~Adj17 13 16.
assume H: Adj17 13 16.
prove False.
apply H.
- assume Hcase: 13 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andER Hcase.
  assume Hjcases: 16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14.
  apply Hjcases.
  + assume Heq: 16 = 1.
    exact neq_16_1 Heq.
  + assume Heq: 16 = 3.
    exact neq_16_3 Heq.
  + assume Heq: 16 = 5.
    exact neq_16_5 Heq.
  + assume Heq: 16 = 12.
    exact neq_16_12 Heq.
  + assume Heq: 16 = 14.
    exact neq_16_14 Heq.
- assume Hcase: 13 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_not_14_1 : ~Adj17 14 1.
assume H: Adj17 14 1.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andER Hcase.
  assume Hjcases: 1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13.
  apply Hjcases.
  + assume Heq: 1 = 0.
    exact neq_1_0 Heq.
  + assume Heq: 1 = 4.
    exact neq_4_1 Heq.
  + assume Heq: 1 = 6.
    exact neq_6_1 Heq.
  + assume Heq: 1 = 8.
    exact neq_8_1 Heq.
  + assume Heq: 1 = 13.
    exact neq_13_1 Heq.
- assume Hcase: 14 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_2 : ~Adj17 14 2.
assume H: Adj17 14 2.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andER Hcase.
  assume Hjcases: 2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13.
  apply Hjcases.
  + assume Heq: 2 = 0.
    exact neq_2_0 Heq.
  + assume Heq: 2 = 4.
    exact neq_4_2 Heq.
  + assume Heq: 2 = 6.
    exact neq_6_2 Heq.
  + assume Heq: 2 = 8.
    exact neq_8_2 Heq.
  + assume Heq: 2 = 13.
    exact neq_13_2 Heq.
- assume Hcase: 14 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_3 : ~Adj17 14 3.
assume H: Adj17 14 3.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (3 = 9 \/ 3 = 14 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (3 = 7 \/ 3 = 11 \/ 3 = 13 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (3 = 8 \/ 3 = 10 \/ 3 = 12 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (3 = 6 \/ 3 = 8 \/ 3 = 13 \/ 3 = 15 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (3 = 5 \/ 3 = 7 \/ 3 = 12 \/ 3 = 14 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 11 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (3 = 3 \/ 3 = 10 \/ 3 = 11 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (3 = 1 \/ 3 = 4 \/ 3 = 9 \/ 3 = 10 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (3 = 2 \/ 3 = 3 \/ 3 = 9 \/ 3 = 11 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (3 = 0 \/ 3 = 5 \/ 3 = 7 \/ 3 = 8 \/ 3 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (3 = 2 \/ 3 = 5 \/ 3 = 6 \/ 3 = 7 \/ 3 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (3 = 1 \/ 3 = 5 \/ 3 = 6 \/ 3 = 8 \/ 3 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (3 = 2 \/ 3 = 4 \/ 3 = 6 \/ 3 = 9 \/ 3 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (3 = 1 \/ 3 = 3 \/ 3 = 5 \/ 3 = 12 \/ 3 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13).
  apply andER Hcase.
  assume Hjcases: 3 = 0 \/ 3 = 4 \/ 3 = 6 \/ 3 = 8 \/ 3 = 13.
  apply Hjcases.
  + assume Heq: 3 = 0.
    exact neq_3_0 Heq.
  + assume Heq: 3 = 4.
    exact neq_4_3 Heq.
  + assume Heq: 3 = 6.
    exact neq_6_3 Heq.
  + assume Heq: 3 = 8.
    exact neq_8_3 Heq.
  + assume Heq: 3 = 13.
    exact neq_13_3 Heq.
- assume Hcase: 14 = 15 /\ (3 = 0 \/ 3 = 2 \/ 3 = 3 \/ 3 = 7 \/ 3 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (3 = 0 \/ 3 = 1 \/ 3 = 3 \/ 3 = 4 \/ 3 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_5 : ~Adj17 14 5.
assume H: Adj17 14 5.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andER Hcase.
  assume Hjcases: 5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13.
  apply Hjcases.
  + assume Heq: 5 = 0.
    exact neq_5_0 Heq.
  + assume Heq: 5 = 4.
    exact neq_5_4 Heq.
  + assume Heq: 5 = 6.
    exact neq_6_5 Heq.
  + assume Heq: 5 = 8.
    exact neq_8_5 Heq.
  + assume Heq: 5 = 13.
    exact neq_13_5 Heq.
- assume Hcase: 14 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_7 : ~Adj17 14 7.
assume H: Adj17 14 7.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andER Hcase.
  assume Hjcases: 7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13.
  apply Hjcases.
  + assume Heq: 7 = 0.
    exact neq_7_0 Heq.
  + assume Heq: 7 = 4.
    exact neq_7_4 Heq.
  + assume Heq: 7 = 6.
    exact neq_7_6 Heq.
  + assume Heq: 7 = 8.
    exact neq_8_7 Heq.
  + assume Heq: 7 = 13.
    exact neq_13_7 Heq.
- assume Hcase: 14 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_9 : ~Adj17 14 9.
assume H: Adj17 14 9.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andER Hcase.
  assume Hjcases: 9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13.
  apply Hjcases.
  + assume Heq: 9 = 0.
    exact neq_9_0 Heq.
  + assume Heq: 9 = 4.
    exact neq_9_4 Heq.
  + assume Heq: 9 = 6.
    exact neq_9_6 Heq.
  + assume Heq: 9 = 8.
    exact neq_9_8 Heq.
  + assume Heq: 9 = 13.
    exact neq_13_9 Heq.
- assume Hcase: 14 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_10 : ~Adj17 14 10.
assume H: Adj17 14 10.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andER Hcase.
  assume Hjcases: 10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13.
  apply Hjcases.
  + assume Heq: 10 = 0.
    exact neq_10_0 Heq.
  + assume Heq: 10 = 4.
    exact neq_10_4 Heq.
  + assume Heq: 10 = 6.
    exact neq_10_6 Heq.
  + assume Heq: 10 = 8.
    exact neq_10_8 Heq.
  + assume Heq: 10 = 13.
    exact neq_13_10 Heq.
- assume Hcase: 14 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_11 : ~Adj17 14 11.
assume H: Adj17 14 11.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andER Hcase.
  assume Hjcases: 11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13.
  apply Hjcases.
  + assume Heq: 11 = 0.
    exact neq_11_0 Heq.
  + assume Heq: 11 = 4.
    exact neq_11_4 Heq.
  + assume Heq: 11 = 6.
    exact neq_11_6 Heq.
  + assume Heq: 11 = 8.
    exact neq_11_8 Heq.
  + assume Heq: 11 = 13.
    exact neq_13_11 Heq.
- assume Hcase: 14 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_12 : ~Adj17 14 12.
assume H: Adj17 14 12.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andER Hcase.
  assume Hjcases: 12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13.
  apply Hjcases.
  + assume Heq: 12 = 0.
    exact neq_12_0 Heq.
  + assume Heq: 12 = 4.
    exact neq_12_4 Heq.
  + assume Heq: 12 = 6.
    exact neq_12_6 Heq.
  + assume Heq: 12 = 8.
    exact neq_12_8 Heq.
  + assume Heq: 12 = 13.
    exact neq_13_12 Heq.
- assume Hcase: 14 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_14 : ~Adj17 14 14.
assume H: Adj17 14 14.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andER Hcase.
  assume Hjcases: 14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13.
  apply Hjcases.
  + assume Heq: 14 = 0.
    exact neq_14_0 Heq.
  + assume Heq: 14 = 4.
    exact neq_14_4 Heq.
  + assume Heq: 14 = 6.
    exact neq_14_6 Heq.
  + assume Heq: 14 = 8.
    exact neq_14_8 Heq.
  + assume Heq: 14 = 13.
    exact neq_14_13 Heq.
- assume Hcase: 14 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_15 : ~Adj17 14 15.
assume H: Adj17 14 15.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andER Hcase.
  assume Hjcases: 15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13.
  apply Hjcases.
  + assume Heq: 15 = 0.
    exact neq_15_0 Heq.
  + assume Heq: 15 = 4.
    exact neq_15_4 Heq.
  + assume Heq: 15 = 6.
    exact neq_15_6 Heq.
  + assume Heq: 15 = 8.
    exact neq_15_8 Heq.
  + assume Heq: 15 = 13.
    exact neq_15_13 Heq.
- assume Hcase: 14 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_14_16 : ~Adj17 14 16.
assume H: Adj17 14 16.
prove False.
apply H.
- assume Hcase: 14 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andER Hcase.
  assume Hjcases: 16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13.
  apply Hjcases.
  + assume Heq: 16 = 0.
    exact neq_16_0 Heq.
  + assume Heq: 16 = 4.
    exact neq_16_4 Heq.
  + assume Heq: 16 = 6.
    exact neq_16_6 Heq.
  + assume Heq: 16 = 8.
    exact neq_16_8 Heq.
  + assume Heq: 16 = 13.
    exact neq_16_13 Heq.
- assume Hcase: 14 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_not_15_1 : ~Adj17 15 1.
assume H: Adj17 15 1.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply andER Hcase.
  assume Hjcases: 1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11.
  apply Hjcases.
  + assume Heq: 1 = 0.
    exact neq_1_0 Heq.
  + assume Heq: 1 = 2.
    exact neq_2_1 Heq.
  + assume Heq: 1 = 3.
    exact neq_3_1 Heq.
  + assume Heq: 1 = 7.
    exact neq_7_1 Heq.
  + assume Heq: 1 = 11.
    exact neq_11_1 Heq.
- assume Hcase: 15 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_4 : ~Adj17 15 4.
assume H: Adj17 15 4.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (4 = 9 \/ 4 = 14 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (4 = 7 \/ 4 = 11 \/ 4 = 13 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (4 = 8 \/ 4 = 10 \/ 4 = 12 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (4 = 6 \/ 4 = 8 \/ 4 = 13 \/ 4 = 15 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (4 = 5 \/ 4 = 7 \/ 4 = 12 \/ 4 = 14 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 11 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (4 = 3 \/ 4 = 10 \/ 4 = 11 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (4 = 1 \/ 4 = 4 \/ 4 = 9 \/ 4 = 10 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (4 = 2 \/ 4 = 3 \/ 4 = 9 \/ 4 = 11 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (4 = 0 \/ 4 = 5 \/ 4 = 7 \/ 4 = 8 \/ 4 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (4 = 2 \/ 4 = 5 \/ 4 = 6 \/ 4 = 7 \/ 4 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (4 = 1 \/ 4 = 5 \/ 4 = 6 \/ 4 = 8 \/ 4 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (4 = 2 \/ 4 = 4 \/ 4 = 6 \/ 4 = 9 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (4 = 1 \/ 4 = 3 \/ 4 = 5 \/ 4 = 12 \/ 4 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (4 = 0 \/ 4 = 4 \/ 4 = 6 \/ 4 = 8 \/ 4 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11).
  apply andER Hcase.
  assume Hjcases: 4 = 0 \/ 4 = 2 \/ 4 = 3 \/ 4 = 7 \/ 4 = 11.
  apply Hjcases.
  + assume Heq: 4 = 0.
    exact neq_4_0 Heq.
  + assume Heq: 4 = 2.
    exact neq_4_2 Heq.
  + assume Heq: 4 = 3.
    exact neq_4_3 Heq.
  + assume Heq: 4 = 7.
    exact neq_7_4 Heq.
  + assume Heq: 4 = 11.
    exact neq_11_4 Heq.
- assume Hcase: 15 = 16 /\ (4 = 0 \/ 4 = 1 \/ 4 = 3 \/ 4 = 4 \/ 4 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_5 : ~Adj17 15 5.
assume H: Adj17 15 5.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andER Hcase.
  assume Hjcases: 5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11.
  apply Hjcases.
  + assume Heq: 5 = 0.
    exact neq_5_0 Heq.
  + assume Heq: 5 = 2.
    exact neq_5_2 Heq.
  + assume Heq: 5 = 3.
    exact neq_5_3 Heq.
  + assume Heq: 5 = 7.
    exact neq_7_5 Heq.
  + assume Heq: 5 = 11.
    exact neq_11_5 Heq.
- assume Hcase: 15 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_6 : ~Adj17 15 6.
assume H: Adj17 15 6.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andER Hcase.
  assume Hjcases: 6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11.
  apply Hjcases.
  + assume Heq: 6 = 0.
    exact neq_6_0 Heq.
  + assume Heq: 6 = 2.
    exact neq_6_2 Heq.
  + assume Heq: 6 = 3.
    exact neq_6_3 Heq.
  + assume Heq: 6 = 7.
    exact neq_7_6 Heq.
  + assume Heq: 6 = 11.
    exact neq_11_6 Heq.
- assume Hcase: 15 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_8 : ~Adj17 15 8.
assume H: Adj17 15 8.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andER Hcase.
  assume Hjcases: 8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11.
  apply Hjcases.
  + assume Heq: 8 = 0.
    exact neq_8_0 Heq.
  + assume Heq: 8 = 2.
    exact neq_8_2 Heq.
  + assume Heq: 8 = 3.
    exact neq_8_3 Heq.
  + assume Heq: 8 = 7.
    exact neq_8_7 Heq.
  + assume Heq: 8 = 11.
    exact neq_11_8 Heq.
- assume Hcase: 15 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_9 : ~Adj17 15 9.
assume H: Adj17 15 9.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andER Hcase.
  assume Hjcases: 9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11.
  apply Hjcases.
  + assume Heq: 9 = 0.
    exact neq_9_0 Heq.
  + assume Heq: 9 = 2.
    exact neq_9_2 Heq.
  + assume Heq: 9 = 3.
    exact neq_9_3 Heq.
  + assume Heq: 9 = 7.
    exact neq_9_7 Heq.
  + assume Heq: 9 = 11.
    exact neq_11_9 Heq.
- assume Hcase: 15 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_10 : ~Adj17 15 10.
assume H: Adj17 15 10.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (10 = 9 \/ 10 = 14 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (10 = 7 \/ 10 = 11 \/ 10 = 13 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (10 = 8 \/ 10 = 10 \/ 10 = 12 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (10 = 6 \/ 10 = 8 \/ 10 = 13 \/ 10 = 15 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (10 = 5 \/ 10 = 7 \/ 10 = 12 \/ 10 = 14 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 11 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (10 = 3 \/ 10 = 10 \/ 10 = 11 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (10 = 1 \/ 10 = 4 \/ 10 = 9 \/ 10 = 10 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (10 = 2 \/ 10 = 3 \/ 10 = 9 \/ 10 = 11 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (10 = 0 \/ 10 = 5 \/ 10 = 7 \/ 10 = 8 \/ 10 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (10 = 2 \/ 10 = 5 \/ 10 = 6 \/ 10 = 7 \/ 10 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (10 = 1 \/ 10 = 5 \/ 10 = 6 \/ 10 = 8 \/ 10 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (10 = 2 \/ 10 = 4 \/ 10 = 6 \/ 10 = 9 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (10 = 1 \/ 10 = 3 \/ 10 = 5 \/ 10 = 12 \/ 10 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (10 = 0 \/ 10 = 4 \/ 10 = 6 \/ 10 = 8 \/ 10 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11).
  apply andER Hcase.
  assume Hjcases: 10 = 0 \/ 10 = 2 \/ 10 = 3 \/ 10 = 7 \/ 10 = 11.
  apply Hjcases.
  + assume Heq: 10 = 0.
    exact neq_10_0 Heq.
  + assume Heq: 10 = 2.
    exact neq_10_2 Heq.
  + assume Heq: 10 = 3.
    exact neq_10_3 Heq.
  + assume Heq: 10 = 7.
    exact neq_10_7 Heq.
  + assume Heq: 10 = 11.
    exact neq_11_10 Heq.
- assume Hcase: 15 = 16 /\ (10 = 0 \/ 10 = 1 \/ 10 = 3 \/ 10 = 4 \/ 10 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_12 : ~Adj17 15 12.
assume H: Adj17 15 12.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andER Hcase.
  assume Hjcases: 12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11.
  apply Hjcases.
  + assume Heq: 12 = 0.
    exact neq_12_0 Heq.
  + assume Heq: 12 = 2.
    exact neq_12_2 Heq.
  + assume Heq: 12 = 3.
    exact neq_12_3 Heq.
  + assume Heq: 12 = 7.
    exact neq_12_7 Heq.
  + assume Heq: 12 = 11.
    exact neq_12_11 Heq.
- assume Hcase: 15 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_13 : ~Adj17 15 13.
assume H: Adj17 15 13.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andER Hcase.
  assume Hjcases: 13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11.
  apply Hjcases.
  + assume Heq: 13 = 0.
    exact neq_13_0 Heq.
  + assume Heq: 13 = 2.
    exact neq_13_2 Heq.
  + assume Heq: 13 = 3.
    exact neq_13_3 Heq.
  + assume Heq: 13 = 7.
    exact neq_13_7 Heq.
  + assume Heq: 13 = 11.
    exact neq_13_11 Heq.
- assume Hcase: 15 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_14 : ~Adj17 15 14.
assume H: Adj17 15 14.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andER Hcase.
  assume Hjcases: 14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11.
  apply Hjcases.
  + assume Heq: 14 = 0.
    exact neq_14_0 Heq.
  + assume Heq: 14 = 2.
    exact neq_14_2 Heq.
  + assume Heq: 14 = 3.
    exact neq_14_3 Heq.
  + assume Heq: 14 = 7.
    exact neq_14_7 Heq.
  + assume Heq: 14 = 11.
    exact neq_14_11 Heq.
- assume Hcase: 15 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_15 : ~Adj17 15 15.
assume H: Adj17 15 15.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andER Hcase.
  assume Hjcases: 15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11.
  apply Hjcases.
  + assume Heq: 15 = 0.
    exact neq_15_0 Heq.
  + assume Heq: 15 = 2.
    exact neq_15_2 Heq.
  + assume Heq: 15 = 3.
    exact neq_15_3 Heq.
  + assume Heq: 15 = 7.
    exact neq_15_7 Heq.
  + assume Heq: 15 = 11.
    exact neq_15_11 Heq.
- assume Hcase: 15 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_15_16 : ~Adj17 15 16.
assume H: Adj17 15 16.
prove False.
apply H.
- assume Hcase: 15 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andER Hcase.
  assume Hjcases: 16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11.
  apply Hjcases.
  + assume Heq: 16 = 0.
    exact neq_16_0 Heq.
  + assume Heq: 16 = 2.
    exact neq_16_2 Heq.
  + assume Heq: 16 = 3.
    exact neq_16_3 Heq.
  + assume Heq: 16 = 7.
    exact neq_16_7 Heq.
  + assume Heq: 16 = 11.
    exact neq_16_11 Heq.
- assume Hcase: 15 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_not_16_2 : ~Adj17 16 2.
assume H: Adj17 16 2.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (2 = 9 \/ 2 = 14 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (2 = 7 \/ 2 = 11 \/ 2 = 13 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (2 = 8 \/ 2 = 10 \/ 2 = 12 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (2 = 6 \/ 2 = 8 \/ 2 = 13 \/ 2 = 15 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (2 = 5 \/ 2 = 7 \/ 2 = 12 \/ 2 = 14 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 11 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (2 = 3 \/ 2 = 10 \/ 2 = 11 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (2 = 1 \/ 2 = 4 \/ 2 = 9 \/ 2 = 10 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (2 = 2 \/ 2 = 3 \/ 2 = 9 \/ 2 = 11 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (2 = 0 \/ 2 = 5 \/ 2 = 7 \/ 2 = 8 \/ 2 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (2 = 2 \/ 2 = 5 \/ 2 = 6 \/ 2 = 7 \/ 2 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (2 = 1 \/ 2 = 5 \/ 2 = 6 \/ 2 = 8 \/ 2 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (2 = 2 \/ 2 = 4 \/ 2 = 6 \/ 2 = 9 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (2 = 1 \/ 2 = 3 \/ 2 = 5 \/ 2 = 12 \/ 2 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (2 = 0 \/ 2 = 4 \/ 2 = 6 \/ 2 = 8 \/ 2 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (2 = 0 \/ 2 = 2 \/ 2 = 3 \/ 2 = 7 \/ 2 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10).
  apply andER Hcase.
  assume Hjcases: 2 = 0 \/ 2 = 1 \/ 2 = 3 \/ 2 = 4 \/ 2 = 10.
  apply Hjcases.
  + assume Heq: 2 = 0.
    exact neq_2_0 Heq.
  + assume Heq: 2 = 1.
    exact neq_2_1 Heq.
  + assume Heq: 2 = 3.
    exact neq_3_2 Heq.
  + assume Heq: 2 = 4.
    exact neq_4_2 Heq.
  + assume Heq: 2 = 10.
    exact neq_10_2 Heq.
Qed.

Theorem Adj17_not_16_5 : ~Adj17 16 5.
assume H: Adj17 16 5.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (5 = 9 \/ 5 = 14 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (5 = 7 \/ 5 = 11 \/ 5 = 13 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (5 = 8 \/ 5 = 10 \/ 5 = 12 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (5 = 6 \/ 5 = 8 \/ 5 = 13 \/ 5 = 15 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (5 = 5 \/ 5 = 7 \/ 5 = 12 \/ 5 = 14 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 11 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (5 = 3 \/ 5 = 10 \/ 5 = 11 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (5 = 1 \/ 5 = 4 \/ 5 = 9 \/ 5 = 10 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (5 = 2 \/ 5 = 3 \/ 5 = 9 \/ 5 = 11 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (5 = 0 \/ 5 = 5 \/ 5 = 7 \/ 5 = 8 \/ 5 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (5 = 2 \/ 5 = 5 \/ 5 = 6 \/ 5 = 7 \/ 5 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (5 = 1 \/ 5 = 5 \/ 5 = 6 \/ 5 = 8 \/ 5 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (5 = 2 \/ 5 = 4 \/ 5 = 6 \/ 5 = 9 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (5 = 1 \/ 5 = 3 \/ 5 = 5 \/ 5 = 12 \/ 5 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (5 = 0 \/ 5 = 4 \/ 5 = 6 \/ 5 = 8 \/ 5 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (5 = 0 \/ 5 = 2 \/ 5 = 3 \/ 5 = 7 \/ 5 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10).
  apply andER Hcase.
  assume Hjcases: 5 = 0 \/ 5 = 1 \/ 5 = 3 \/ 5 = 4 \/ 5 = 10.
  apply Hjcases.
  + assume Heq: 5 = 0.
    exact neq_5_0 Heq.
  + assume Heq: 5 = 1.
    exact neq_5_1 Heq.
  + assume Heq: 5 = 3.
    exact neq_5_3 Heq.
  + assume Heq: 5 = 4.
    exact neq_5_4 Heq.
  + assume Heq: 5 = 10.
    exact neq_10_5 Heq.
Qed.

Theorem Adj17_not_16_6 : ~Adj17 16 6.
assume H: Adj17 16 6.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (6 = 9 \/ 6 = 14 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (6 = 7 \/ 6 = 11 \/ 6 = 13 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (6 = 8 \/ 6 = 10 \/ 6 = 12 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (6 = 6 \/ 6 = 8 \/ 6 = 13 \/ 6 = 15 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (6 = 5 \/ 6 = 7 \/ 6 = 12 \/ 6 = 14 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 11 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (6 = 3 \/ 6 = 10 \/ 6 = 11 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (6 = 1 \/ 6 = 4 \/ 6 = 9 \/ 6 = 10 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (6 = 2 \/ 6 = 3 \/ 6 = 9 \/ 6 = 11 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (6 = 0 \/ 6 = 5 \/ 6 = 7 \/ 6 = 8 \/ 6 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (6 = 2 \/ 6 = 5 \/ 6 = 6 \/ 6 = 7 \/ 6 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (6 = 1 \/ 6 = 5 \/ 6 = 6 \/ 6 = 8 \/ 6 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (6 = 2 \/ 6 = 4 \/ 6 = 6 \/ 6 = 9 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (6 = 1 \/ 6 = 3 \/ 6 = 5 \/ 6 = 12 \/ 6 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (6 = 0 \/ 6 = 4 \/ 6 = 6 \/ 6 = 8 \/ 6 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (6 = 0 \/ 6 = 2 \/ 6 = 3 \/ 6 = 7 \/ 6 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10).
  apply andER Hcase.
  assume Hjcases: 6 = 0 \/ 6 = 1 \/ 6 = 3 \/ 6 = 4 \/ 6 = 10.
  apply Hjcases.
  + assume Heq: 6 = 0.
    exact neq_6_0 Heq.
  + assume Heq: 6 = 1.
    exact neq_6_1 Heq.
  + assume Heq: 6 = 3.
    exact neq_6_3 Heq.
  + assume Heq: 6 = 4.
    exact neq_6_4 Heq.
  + assume Heq: 6 = 10.
    exact neq_10_6 Heq.
Qed.

Theorem Adj17_not_16_7 : ~Adj17 16 7.
assume H: Adj17 16 7.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (7 = 9 \/ 7 = 14 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (7 = 7 \/ 7 = 11 \/ 7 = 13 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (7 = 8 \/ 7 = 10 \/ 7 = 12 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (7 = 6 \/ 7 = 8 \/ 7 = 13 \/ 7 = 15 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (7 = 5 \/ 7 = 7 \/ 7 = 12 \/ 7 = 14 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 11 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (7 = 3 \/ 7 = 10 \/ 7 = 11 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (7 = 1 \/ 7 = 4 \/ 7 = 9 \/ 7 = 10 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (7 = 2 \/ 7 = 3 \/ 7 = 9 \/ 7 = 11 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (7 = 0 \/ 7 = 5 \/ 7 = 7 \/ 7 = 8 \/ 7 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (7 = 2 \/ 7 = 5 \/ 7 = 6 \/ 7 = 7 \/ 7 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (7 = 1 \/ 7 = 5 \/ 7 = 6 \/ 7 = 8 \/ 7 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (7 = 2 \/ 7 = 4 \/ 7 = 6 \/ 7 = 9 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (7 = 1 \/ 7 = 3 \/ 7 = 5 \/ 7 = 12 \/ 7 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (7 = 0 \/ 7 = 4 \/ 7 = 6 \/ 7 = 8 \/ 7 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (7 = 0 \/ 7 = 2 \/ 7 = 3 \/ 7 = 7 \/ 7 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10).
  apply andER Hcase.
  assume Hjcases: 7 = 0 \/ 7 = 1 \/ 7 = 3 \/ 7 = 4 \/ 7 = 10.
  apply Hjcases.
  + assume Heq: 7 = 0.
    exact neq_7_0 Heq.
  + assume Heq: 7 = 1.
    exact neq_7_1 Heq.
  + assume Heq: 7 = 3.
    exact neq_7_3 Heq.
  + assume Heq: 7 = 4.
    exact neq_7_4 Heq.
  + assume Heq: 7 = 10.
    exact neq_10_7 Heq.
Qed.

Theorem Adj17_not_16_8 : ~Adj17 16 8.
assume H: Adj17 16 8.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (8 = 9 \/ 8 = 14 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (8 = 7 \/ 8 = 11 \/ 8 = 13 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (8 = 8 \/ 8 = 10 \/ 8 = 12 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (8 = 6 \/ 8 = 8 \/ 8 = 13 \/ 8 = 15 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (8 = 5 \/ 8 = 7 \/ 8 = 12 \/ 8 = 14 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 11 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (8 = 3 \/ 8 = 10 \/ 8 = 11 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (8 = 1 \/ 8 = 4 \/ 8 = 9 \/ 8 = 10 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (8 = 2 \/ 8 = 3 \/ 8 = 9 \/ 8 = 11 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (8 = 0 \/ 8 = 5 \/ 8 = 7 \/ 8 = 8 \/ 8 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (8 = 2 \/ 8 = 5 \/ 8 = 6 \/ 8 = 7 \/ 8 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (8 = 1 \/ 8 = 5 \/ 8 = 6 \/ 8 = 8 \/ 8 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (8 = 2 \/ 8 = 4 \/ 8 = 6 \/ 8 = 9 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (8 = 1 \/ 8 = 3 \/ 8 = 5 \/ 8 = 12 \/ 8 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (8 = 0 \/ 8 = 4 \/ 8 = 6 \/ 8 = 8 \/ 8 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (8 = 0 \/ 8 = 2 \/ 8 = 3 \/ 8 = 7 \/ 8 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10).
  apply andER Hcase.
  assume Hjcases: 8 = 0 \/ 8 = 1 \/ 8 = 3 \/ 8 = 4 \/ 8 = 10.
  apply Hjcases.
  + assume Heq: 8 = 0.
    exact neq_8_0 Heq.
  + assume Heq: 8 = 1.
    exact neq_8_1 Heq.
  + assume Heq: 8 = 3.
    exact neq_8_3 Heq.
  + assume Heq: 8 = 4.
    exact neq_8_4 Heq.
  + assume Heq: 8 = 10.
    exact neq_10_8 Heq.
Qed.

Theorem Adj17_not_16_9 : ~Adj17 16 9.
assume H: Adj17 16 9.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (9 = 9 \/ 9 = 14 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (9 = 7 \/ 9 = 11 \/ 9 = 13 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (9 = 8 \/ 9 = 10 \/ 9 = 12 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (9 = 6 \/ 9 = 8 \/ 9 = 13 \/ 9 = 15 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (9 = 5 \/ 9 = 7 \/ 9 = 12 \/ 9 = 14 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 11 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (9 = 3 \/ 9 = 10 \/ 9 = 11 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (9 = 1 \/ 9 = 4 \/ 9 = 9 \/ 9 = 10 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (9 = 2 \/ 9 = 3 \/ 9 = 9 \/ 9 = 11 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (9 = 0 \/ 9 = 5 \/ 9 = 7 \/ 9 = 8 \/ 9 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (9 = 2 \/ 9 = 5 \/ 9 = 6 \/ 9 = 7 \/ 9 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (9 = 1 \/ 9 = 5 \/ 9 = 6 \/ 9 = 8 \/ 9 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (9 = 2 \/ 9 = 4 \/ 9 = 6 \/ 9 = 9 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (9 = 1 \/ 9 = 3 \/ 9 = 5 \/ 9 = 12 \/ 9 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (9 = 0 \/ 9 = 4 \/ 9 = 6 \/ 9 = 8 \/ 9 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (9 = 0 \/ 9 = 2 \/ 9 = 3 \/ 9 = 7 \/ 9 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10).
  apply andER Hcase.
  assume Hjcases: 9 = 0 \/ 9 = 1 \/ 9 = 3 \/ 9 = 4 \/ 9 = 10.
  apply Hjcases.
  + assume Heq: 9 = 0.
    exact neq_9_0 Heq.
  + assume Heq: 9 = 1.
    exact neq_9_1 Heq.
  + assume Heq: 9 = 3.
    exact neq_9_3 Heq.
  + assume Heq: 9 = 4.
    exact neq_9_4 Heq.
  + assume Heq: 9 = 10.
    exact neq_10_9 Heq.
Qed.

Theorem Adj17_not_16_11 : ~Adj17 16 11.
assume H: Adj17 16 11.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (11 = 9 \/ 11 = 14 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (11 = 7 \/ 11 = 11 \/ 11 = 13 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (11 = 8 \/ 11 = 10 \/ 11 = 12 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (11 = 6 \/ 11 = 8 \/ 11 = 13 \/ 11 = 15 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (11 = 5 \/ 11 = 7 \/ 11 = 12 \/ 11 = 14 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 11 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (11 = 3 \/ 11 = 10 \/ 11 = 11 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (11 = 1 \/ 11 = 4 \/ 11 = 9 \/ 11 = 10 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (11 = 2 \/ 11 = 3 \/ 11 = 9 \/ 11 = 11 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (11 = 0 \/ 11 = 5 \/ 11 = 7 \/ 11 = 8 \/ 11 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (11 = 2 \/ 11 = 5 \/ 11 = 6 \/ 11 = 7 \/ 11 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (11 = 1 \/ 11 = 5 \/ 11 = 6 \/ 11 = 8 \/ 11 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (11 = 2 \/ 11 = 4 \/ 11 = 6 \/ 11 = 9 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (11 = 1 \/ 11 = 3 \/ 11 = 5 \/ 11 = 12 \/ 11 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (11 = 0 \/ 11 = 4 \/ 11 = 6 \/ 11 = 8 \/ 11 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (11 = 0 \/ 11 = 2 \/ 11 = 3 \/ 11 = 7 \/ 11 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10).
  apply andER Hcase.
  assume Hjcases: 11 = 0 \/ 11 = 1 \/ 11 = 3 \/ 11 = 4 \/ 11 = 10.
  apply Hjcases.
  + assume Heq: 11 = 0.
    exact neq_11_0 Heq.
  + assume Heq: 11 = 1.
    exact neq_11_1 Heq.
  + assume Heq: 11 = 3.
    exact neq_11_3 Heq.
  + assume Heq: 11 = 4.
    exact neq_11_4 Heq.
  + assume Heq: 11 = 10.
    exact neq_11_10 Heq.
Qed.

Theorem Adj17_not_16_12 : ~Adj17 16 12.
assume H: Adj17 16 12.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (12 = 9 \/ 12 = 14 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (12 = 7 \/ 12 = 11 \/ 12 = 13 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (12 = 8 \/ 12 = 10 \/ 12 = 12 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (12 = 6 \/ 12 = 8 \/ 12 = 13 \/ 12 = 15 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (12 = 5 \/ 12 = 7 \/ 12 = 12 \/ 12 = 14 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 11 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (12 = 3 \/ 12 = 10 \/ 12 = 11 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (12 = 1 \/ 12 = 4 \/ 12 = 9 \/ 12 = 10 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (12 = 2 \/ 12 = 3 \/ 12 = 9 \/ 12 = 11 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (12 = 0 \/ 12 = 5 \/ 12 = 7 \/ 12 = 8 \/ 12 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (12 = 2 \/ 12 = 5 \/ 12 = 6 \/ 12 = 7 \/ 12 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (12 = 1 \/ 12 = 5 \/ 12 = 6 \/ 12 = 8 \/ 12 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (12 = 2 \/ 12 = 4 \/ 12 = 6 \/ 12 = 9 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (12 = 1 \/ 12 = 3 \/ 12 = 5 \/ 12 = 12 \/ 12 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (12 = 0 \/ 12 = 4 \/ 12 = 6 \/ 12 = 8 \/ 12 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (12 = 0 \/ 12 = 2 \/ 12 = 3 \/ 12 = 7 \/ 12 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10).
  apply andER Hcase.
  assume Hjcases: 12 = 0 \/ 12 = 1 \/ 12 = 3 \/ 12 = 4 \/ 12 = 10.
  apply Hjcases.
  + assume Heq: 12 = 0.
    exact neq_12_0 Heq.
  + assume Heq: 12 = 1.
    exact neq_12_1 Heq.
  + assume Heq: 12 = 3.
    exact neq_12_3 Heq.
  + assume Heq: 12 = 4.
    exact neq_12_4 Heq.
  + assume Heq: 12 = 10.
    exact neq_12_10 Heq.
Qed.

Theorem Adj17_not_16_13 : ~Adj17 16 13.
assume H: Adj17 16 13.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (13 = 9 \/ 13 = 14 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (13 = 7 \/ 13 = 11 \/ 13 = 13 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (13 = 8 \/ 13 = 10 \/ 13 = 12 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (13 = 6 \/ 13 = 8 \/ 13 = 13 \/ 13 = 15 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (13 = 5 \/ 13 = 7 \/ 13 = 12 \/ 13 = 14 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 11 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (13 = 3 \/ 13 = 10 \/ 13 = 11 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (13 = 1 \/ 13 = 4 \/ 13 = 9 \/ 13 = 10 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (13 = 2 \/ 13 = 3 \/ 13 = 9 \/ 13 = 11 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (13 = 0 \/ 13 = 5 \/ 13 = 7 \/ 13 = 8 \/ 13 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (13 = 2 \/ 13 = 5 \/ 13 = 6 \/ 13 = 7 \/ 13 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (13 = 1 \/ 13 = 5 \/ 13 = 6 \/ 13 = 8 \/ 13 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (13 = 2 \/ 13 = 4 \/ 13 = 6 \/ 13 = 9 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (13 = 1 \/ 13 = 3 \/ 13 = 5 \/ 13 = 12 \/ 13 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (13 = 0 \/ 13 = 4 \/ 13 = 6 \/ 13 = 8 \/ 13 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (13 = 0 \/ 13 = 2 \/ 13 = 3 \/ 13 = 7 \/ 13 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10).
  apply andER Hcase.
  assume Hjcases: 13 = 0 \/ 13 = 1 \/ 13 = 3 \/ 13 = 4 \/ 13 = 10.
  apply Hjcases.
  + assume Heq: 13 = 0.
    exact neq_13_0 Heq.
  + assume Heq: 13 = 1.
    exact neq_13_1 Heq.
  + assume Heq: 13 = 3.
    exact neq_13_3 Heq.
  + assume Heq: 13 = 4.
    exact neq_13_4 Heq.
  + assume Heq: 13 = 10.
    exact neq_13_10 Heq.
Qed.

Theorem Adj17_not_16_14 : ~Adj17 16 14.
assume H: Adj17 16 14.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (14 = 9 \/ 14 = 14 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (14 = 7 \/ 14 = 11 \/ 14 = 13 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (14 = 8 \/ 14 = 10 \/ 14 = 12 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (14 = 6 \/ 14 = 8 \/ 14 = 13 \/ 14 = 15 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (14 = 5 \/ 14 = 7 \/ 14 = 12 \/ 14 = 14 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 11 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (14 = 3 \/ 14 = 10 \/ 14 = 11 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (14 = 1 \/ 14 = 4 \/ 14 = 9 \/ 14 = 10 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (14 = 2 \/ 14 = 3 \/ 14 = 9 \/ 14 = 11 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (14 = 0 \/ 14 = 5 \/ 14 = 7 \/ 14 = 8 \/ 14 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (14 = 2 \/ 14 = 5 \/ 14 = 6 \/ 14 = 7 \/ 14 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (14 = 1 \/ 14 = 5 \/ 14 = 6 \/ 14 = 8 \/ 14 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (14 = 2 \/ 14 = 4 \/ 14 = 6 \/ 14 = 9 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (14 = 1 \/ 14 = 3 \/ 14 = 5 \/ 14 = 12 \/ 14 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (14 = 0 \/ 14 = 4 \/ 14 = 6 \/ 14 = 8 \/ 14 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (14 = 0 \/ 14 = 2 \/ 14 = 3 \/ 14 = 7 \/ 14 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10).
  apply andER Hcase.
  assume Hjcases: 14 = 0 \/ 14 = 1 \/ 14 = 3 \/ 14 = 4 \/ 14 = 10.
  apply Hjcases.
  + assume Heq: 14 = 0.
    exact neq_14_0 Heq.
  + assume Heq: 14 = 1.
    exact neq_14_1 Heq.
  + assume Heq: 14 = 3.
    exact neq_14_3 Heq.
  + assume Heq: 14 = 4.
    exact neq_14_4 Heq.
  + assume Heq: 14 = 10.
    exact neq_14_10 Heq.
Qed.

Theorem Adj17_not_16_15 : ~Adj17 16 15.
assume H: Adj17 16 15.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (15 = 9 \/ 15 = 14 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (15 = 7 \/ 15 = 11 \/ 15 = 13 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (15 = 8 \/ 15 = 10 \/ 15 = 12 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (15 = 6 \/ 15 = 8 \/ 15 = 13 \/ 15 = 15 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (15 = 5 \/ 15 = 7 \/ 15 = 12 \/ 15 = 14 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 11 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (15 = 3 \/ 15 = 10 \/ 15 = 11 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (15 = 1 \/ 15 = 4 \/ 15 = 9 \/ 15 = 10 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (15 = 2 \/ 15 = 3 \/ 15 = 9 \/ 15 = 11 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (15 = 0 \/ 15 = 5 \/ 15 = 7 \/ 15 = 8 \/ 15 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (15 = 2 \/ 15 = 5 \/ 15 = 6 \/ 15 = 7 \/ 15 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (15 = 1 \/ 15 = 5 \/ 15 = 6 \/ 15 = 8 \/ 15 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (15 = 2 \/ 15 = 4 \/ 15 = 6 \/ 15 = 9 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (15 = 1 \/ 15 = 3 \/ 15 = 5 \/ 15 = 12 \/ 15 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (15 = 0 \/ 15 = 4 \/ 15 = 6 \/ 15 = 8 \/ 15 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (15 = 0 \/ 15 = 2 \/ 15 = 3 \/ 15 = 7 \/ 15 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10).
  apply andER Hcase.
  assume Hjcases: 15 = 0 \/ 15 = 1 \/ 15 = 3 \/ 15 = 4 \/ 15 = 10.
  apply Hjcases.
  + assume Heq: 15 = 0.
    exact neq_15_0 Heq.
  + assume Heq: 15 = 1.
    exact neq_15_1 Heq.
  + assume Heq: 15 = 3.
    exact neq_15_3 Heq.
  + assume Heq: 15 = 4.
    exact neq_15_4 Heq.
  + assume Heq: 15 = 10.
    exact neq_15_10 Heq.
Qed.

Theorem Adj17_not_16_16 : ~Adj17 16 16.
assume H: Adj17 16 16.
prove False.
apply H.
- assume Hcase: 16 = 0 /\ (16 = 9 \/ 16 = 14 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (16 = 7 \/ 16 = 11 \/ 16 = 13 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (16 = 8 \/ 16 = 10 \/ 16 = 12 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (16 = 6 \/ 16 = 8 \/ 16 = 13 \/ 16 = 15 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (16 = 5 \/ 16 = 7 \/ 16 = 12 \/ 16 = 14 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 11 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (16 = 3 \/ 16 = 10 \/ 16 = 11 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (16 = 1 \/ 16 = 4 \/ 16 = 9 \/ 16 = 10 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (16 = 2 \/ 16 = 3 \/ 16 = 9 \/ 16 = 11 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (16 = 0 \/ 16 = 5 \/ 16 = 7 \/ 16 = 8 \/ 16 = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (16 = 2 \/ 16 = 5 \/ 16 = 6 \/ 16 = 7 \/ 16 = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (16 = 1 \/ 16 = 5 \/ 16 = 6 \/ 16 = 8 \/ 16 = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (16 = 2 \/ 16 = 4 \/ 16 = 6 \/ 16 = 9 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (16 = 1 \/ 16 = 3 \/ 16 = 5 \/ 16 = 12 \/ 16 = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (16 = 0 \/ 16 = 4 \/ 16 = 6 \/ 16 = 8 \/ 16 = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (16 = 0 \/ 16 = 2 \/ 16 = 3 \/ 16 = 7 \/ 16 = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10).
  apply andER Hcase.
  assume Hjcases: 16 = 0 \/ 16 = 1 \/ 16 = 3 \/ 16 = 4 \/ 16 = 10.
  apply Hjcases.
  + assume Heq: 16 = 0.
    exact neq_16_0 Heq.
  + assume Heq: 16 = 1.
    exact neq_16_1 Heq.
  + assume Heq: 16 = 3.
    exact neq_16_3 Heq.
  + assume Heq: 16 = 4.
    exact neq_16_4 Heq.
  + assume Heq: 16 = 10.
    exact neq_16_10 Heq.
Qed.

Theorem Adj17_cases_0 : forall j, Adj17 0 j -> j = 9 \/ j = 14 \/ j = 15 \/ j = 16.
let j.
assume H: Adj17 0 j.
apply H.
- assume Hcase: 0 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andER Hcase.
  assume Hjcases: j = 9 \/ j = 14 \/ j = 15 \/ j = 16.
  apply Hjcases.
  + assume Heq: j = 9.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 14.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 15.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 16.
    apply orIR.
    exact Heq.
- assume Hcase: 0 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 0 = 1.
  apply FalseE.
  exact neq_1_0 Heq.
- assume Hcase: 0 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 0 = 2.
  apply FalseE.
  exact neq_2_0 Heq.
- assume Hcase: 0 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 0 = 3.
  apply FalseE.
  exact neq_3_0 Heq.
- assume Hcase: 0 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 0 = 4.
  apply FalseE.
  exact neq_4_0 Heq.
- assume Hcase: 0 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 0 = 5.
  apply FalseE.
  exact neq_5_0 Heq.
- assume Hcase: 0 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 0 = 6.
  apply FalseE.
  exact neq_6_0 Heq.
- assume Hcase: 0 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 0 = 7.
  apply FalseE.
  exact neq_7_0 Heq.
- assume Hcase: 0 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 0 = 8.
  apply FalseE.
  exact neq_8_0 Heq.
- assume Hcase: 0 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 0 = 9.
  apply FalseE.
  exact neq_9_0 Heq.
- assume Hcase: 0 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 0 = 10.
  apply FalseE.
  exact neq_10_0 Heq.
- assume Hcase: 0 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 0 = 11.
  apply FalseE.
  exact neq_11_0 Heq.
- assume Hcase: 0 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 0 = 12.
  apply FalseE.
  exact neq_12_0 Heq.
- assume Hcase: 0 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 0 = 13.
  apply FalseE.
  exact neq_13_0 Heq.
- assume Hcase: 0 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 0 = 14.
  apply FalseE.
  exact neq_14_0 Heq.
- assume Hcase: 0 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 0 = 15.
  apply FalseE.
  exact neq_15_0 Heq.
- assume Hcase: 0 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 0 = 16.
  apply FalseE.
  exact neq_16_0 Heq.
Qed.

Theorem Adj17_cases_1 : forall j, Adj17 1 j -> j = 7 \/ j = 11 \/ j = 13 \/ j = 16.
let j.
assume H: Adj17 1 j.
apply H.
- assume Hcase: 1 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 1 = 0.
  apply FalseE.
  exact neq_1_0 Heq.
- assume Hcase: 1 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andER Hcase.
  assume Hjcases: j = 7 \/ j = 11 \/ j = 13 \/ j = 16.
  apply Hjcases.
  + assume Heq: j = 7.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 11.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 13.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 16.
    apply orIR.
    exact Heq.
- assume Hcase: 1 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 1 = 2.
  apply FalseE.
  exact neq_2_1 Heq.
- assume Hcase: 1 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 1 = 3.
  apply FalseE.
  exact neq_3_1 Heq.
- assume Hcase: 1 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 1 = 4.
  apply FalseE.
  exact neq_4_1 Heq.
- assume Hcase: 1 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 1 = 5.
  apply FalseE.
  exact neq_5_1 Heq.
- assume Hcase: 1 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 1 = 6.
  apply FalseE.
  exact neq_6_1 Heq.
- assume Hcase: 1 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 1 = 7.
  apply FalseE.
  exact neq_7_1 Heq.
- assume Hcase: 1 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 1 = 8.
  apply FalseE.
  exact neq_8_1 Heq.
- assume Hcase: 1 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 1 = 9.
  apply FalseE.
  exact neq_9_1 Heq.
- assume Hcase: 1 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 1 = 10.
  apply FalseE.
  exact neq_10_1 Heq.
- assume Hcase: 1 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 1 = 11.
  apply FalseE.
  exact neq_11_1 Heq.
- assume Hcase: 1 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 1 = 12.
  apply FalseE.
  exact neq_12_1 Heq.
- assume Hcase: 1 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 1 = 13.
  apply FalseE.
  exact neq_13_1 Heq.
- assume Hcase: 1 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 1 = 14.
  apply FalseE.
  exact neq_14_1 Heq.
- assume Hcase: 1 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 1 = 15.
  apply FalseE.
  exact neq_15_1 Heq.
- assume Hcase: 1 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 1 = 16.
  apply FalseE.
  exact neq_16_1 Heq.
Qed.

Theorem Adj17_cases_2 : forall j, Adj17 2 j -> j = 8 \/ j = 10 \/ j = 12 \/ j = 15.
let j.
assume H: Adj17 2 j.
apply H.
- assume Hcase: 2 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 2 = 0.
  apply FalseE.
  exact neq_2_0 Heq.
- assume Hcase: 2 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 2 = 1.
  apply FalseE.
  exact neq_2_1 Heq.
- assume Hcase: 2 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andER Hcase.
  assume Hjcases: j = 8 \/ j = 10 \/ j = 12 \/ j = 15.
  apply Hjcases.
  + assume Heq: j = 8.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 10.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 12.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 15.
    apply orIR.
    exact Heq.
- assume Hcase: 2 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 2 = 3.
  apply FalseE.
  exact neq_3_2 Heq.
- assume Hcase: 2 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 2 = 4.
  apply FalseE.
  exact neq_4_2 Heq.
- assume Hcase: 2 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 2 = 5.
  apply FalseE.
  exact neq_5_2 Heq.
- assume Hcase: 2 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 2 = 6.
  apply FalseE.
  exact neq_6_2 Heq.
- assume Hcase: 2 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 2 = 7.
  apply FalseE.
  exact neq_7_2 Heq.
- assume Hcase: 2 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 2 = 8.
  apply FalseE.
  exact neq_8_2 Heq.
- assume Hcase: 2 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 2 = 9.
  apply FalseE.
  exact neq_9_2 Heq.
- assume Hcase: 2 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 2 = 10.
  apply FalseE.
  exact neq_10_2 Heq.
- assume Hcase: 2 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 2 = 11.
  apply FalseE.
  exact neq_11_2 Heq.
- assume Hcase: 2 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 2 = 12.
  apply FalseE.
  exact neq_12_2 Heq.
- assume Hcase: 2 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 2 = 13.
  apply FalseE.
  exact neq_13_2 Heq.
- assume Hcase: 2 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 2 = 14.
  apply FalseE.
  exact neq_14_2 Heq.
- assume Hcase: 2 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 2 = 15.
  apply FalseE.
  exact neq_15_2 Heq.
- assume Hcase: 2 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 2 = 16.
  apply FalseE.
  exact neq_16_2 Heq.
Qed.

Theorem Adj17_cases_3 : forall j, Adj17 3 j -> j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16.
let j.
assume H: Adj17 3 j.
apply H.
- assume Hcase: 3 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 3 = 0.
  apply FalseE.
  exact neq_3_0 Heq.
- assume Hcase: 3 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 3 = 1.
  apply FalseE.
  exact neq_3_1 Heq.
- assume Hcase: 3 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 3 = 2.
  apply FalseE.
  exact neq_3_2 Heq.
- assume Hcase: 3 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andER Hcase.
  assume Hjcases: j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16.
  apply Hjcases.
  + assume Heq: j = 6.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 8.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 13.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 15.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 16.
    apply orIR.
    exact Heq.
- assume Hcase: 3 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 3 = 4.
  apply FalseE.
  exact neq_4_3 Heq.
- assume Hcase: 3 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 3 = 5.
  apply FalseE.
  exact neq_5_3 Heq.
- assume Hcase: 3 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 3 = 6.
  apply FalseE.
  exact neq_6_3 Heq.
- assume Hcase: 3 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 3 = 7.
  apply FalseE.
  exact neq_7_3 Heq.
- assume Hcase: 3 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 3 = 8.
  apply FalseE.
  exact neq_8_3 Heq.
- assume Hcase: 3 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 3 = 9.
  apply FalseE.
  exact neq_9_3 Heq.
- assume Hcase: 3 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 3 = 10.
  apply FalseE.
  exact neq_10_3 Heq.
- assume Hcase: 3 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 3 = 11.
  apply FalseE.
  exact neq_11_3 Heq.
- assume Hcase: 3 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 3 = 12.
  apply FalseE.
  exact neq_12_3 Heq.
- assume Hcase: 3 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 3 = 13.
  apply FalseE.
  exact neq_13_3 Heq.
- assume Hcase: 3 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 3 = 14.
  apply FalseE.
  exact neq_14_3 Heq.
- assume Hcase: 3 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 3 = 15.
  apply FalseE.
  exact neq_15_3 Heq.
- assume Hcase: 3 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 3 = 16.
  apply FalseE.
  exact neq_16_3 Heq.
Qed.

Theorem Adj17_cases_4 : forall j, Adj17 4 j -> j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16.
let j.
assume H: Adj17 4 j.
apply H.
- assume Hcase: 4 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 4 = 0.
  apply FalseE.
  exact neq_4_0 Heq.
- assume Hcase: 4 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 4 = 1.
  apply FalseE.
  exact neq_4_1 Heq.
- assume Hcase: 4 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 4 = 2.
  apply FalseE.
  exact neq_4_2 Heq.
- assume Hcase: 4 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 4 = 3.
  apply FalseE.
  exact neq_4_3 Heq.
- assume Hcase: 4 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andER Hcase.
  assume Hjcases: j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16.
  apply Hjcases.
  + assume Heq: j = 5.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 7.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 12.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 14.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 16.
    apply orIR.
    exact Heq.
- assume Hcase: 4 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 4 = 5.
  apply FalseE.
  exact neq_5_4 Heq.
- assume Hcase: 4 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 4 = 6.
  apply FalseE.
  exact neq_6_4 Heq.
- assume Hcase: 4 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 4 = 7.
  apply FalseE.
  exact neq_7_4 Heq.
- assume Hcase: 4 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 4 = 8.
  apply FalseE.
  exact neq_8_4 Heq.
- assume Hcase: 4 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 4 = 9.
  apply FalseE.
  exact neq_9_4 Heq.
- assume Hcase: 4 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 4 = 10.
  apply FalseE.
  exact neq_10_4 Heq.
- assume Hcase: 4 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 4 = 11.
  apply FalseE.
  exact neq_11_4 Heq.
- assume Hcase: 4 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 4 = 12.
  apply FalseE.
  exact neq_12_4 Heq.
- assume Hcase: 4 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 4 = 13.
  apply FalseE.
  exact neq_13_4 Heq.
- assume Hcase: 4 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 4 = 14.
  apply FalseE.
  exact neq_14_4 Heq.
- assume Hcase: 4 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 4 = 15.
  apply FalseE.
  exact neq_15_4 Heq.
- assume Hcase: 4 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 4 = 16.
  apply FalseE.
  exact neq_16_4 Heq.
Qed.

Theorem Adj17_cases_5 : forall j, Adj17 5 j -> j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13.
let j.
assume H: Adj17 5 j.
apply H.
- assume Hcase: 5 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 5 = 0.
  apply FalseE.
  exact neq_5_0 Heq.
- assume Hcase: 5 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 5 = 1.
  apply FalseE.
  exact neq_5_1 Heq.
- assume Hcase: 5 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 5 = 2.
  apply FalseE.
  exact neq_5_2 Heq.
- assume Hcase: 5 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 5 = 3.
  apply FalseE.
  exact neq_5_3 Heq.
- assume Hcase: 5 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 5 = 4.
  apply FalseE.
  exact neq_5_4 Heq.
- assume Hcase: 5 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andER Hcase.
  assume Hjcases: j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13.
  apply Hjcases.
  + assume Heq: j = 4.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 9.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 10.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 11.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 13.
    apply orIR.
    exact Heq.
- assume Hcase: 5 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 5 = 6.
  apply FalseE.
  exact neq_6_5 Heq.
- assume Hcase: 5 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 5 = 7.
  apply FalseE.
  exact neq_7_5 Heq.
- assume Hcase: 5 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 5 = 8.
  apply FalseE.
  exact neq_8_5 Heq.
- assume Hcase: 5 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 5 = 9.
  apply FalseE.
  exact neq_9_5 Heq.
- assume Hcase: 5 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 5 = 10.
  apply FalseE.
  exact neq_10_5 Heq.
- assume Hcase: 5 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 5 = 11.
  apply FalseE.
  exact neq_11_5 Heq.
- assume Hcase: 5 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 5 = 12.
  apply FalseE.
  exact neq_12_5 Heq.
- assume Hcase: 5 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 5 = 13.
  apply FalseE.
  exact neq_13_5 Heq.
- assume Hcase: 5 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 5 = 14.
  apply FalseE.
  exact neq_14_5 Heq.
- assume Hcase: 5 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 5 = 15.
  apply FalseE.
  exact neq_15_5 Heq.
- assume Hcase: 5 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 5 = 16.
  apply FalseE.
  exact neq_16_5 Heq.
Qed.

Theorem Adj17_cases_6 : forall j, Adj17 6 j -> j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14.
let j.
assume H: Adj17 6 j.
apply H.
- assume Hcase: 6 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 6 = 0.
  apply FalseE.
  exact neq_6_0 Heq.
- assume Hcase: 6 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 6 = 1.
  apply FalseE.
  exact neq_6_1 Heq.
- assume Hcase: 6 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 6 = 2.
  apply FalseE.
  exact neq_6_2 Heq.
- assume Hcase: 6 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 6 = 3.
  apply FalseE.
  exact neq_6_3 Heq.
- assume Hcase: 6 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 6 = 4.
  apply FalseE.
  exact neq_6_4 Heq.
- assume Hcase: 6 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 6 = 5.
  apply FalseE.
  exact neq_6_5 Heq.
- assume Hcase: 6 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andER Hcase.
  assume Hjcases: j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14.
  apply Hjcases.
  + assume Heq: j = 3.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 10.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 11.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 12.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 14.
    apply orIR.
    exact Heq.
- assume Hcase: 6 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 6 = 7.
  apply FalseE.
  exact neq_7_6 Heq.
- assume Hcase: 6 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 6 = 8.
  apply FalseE.
  exact neq_8_6 Heq.
- assume Hcase: 6 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 6 = 9.
  apply FalseE.
  exact neq_9_6 Heq.
- assume Hcase: 6 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 6 = 10.
  apply FalseE.
  exact neq_10_6 Heq.
- assume Hcase: 6 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 6 = 11.
  apply FalseE.
  exact neq_11_6 Heq.
- assume Hcase: 6 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 6 = 12.
  apply FalseE.
  exact neq_12_6 Heq.
- assume Hcase: 6 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 6 = 13.
  apply FalseE.
  exact neq_13_6 Heq.
- assume Hcase: 6 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 6 = 14.
  apply FalseE.
  exact neq_14_6 Heq.
- assume Hcase: 6 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 6 = 15.
  apply FalseE.
  exact neq_15_6 Heq.
- assume Hcase: 6 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 6 = 16.
  apply FalseE.
  exact neq_16_6 Heq.
Qed.

Theorem Adj17_cases_7 : forall j, Adj17 7 j -> j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15.
let j.
assume H: Adj17 7 j.
apply H.
- assume Hcase: 7 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 7 = 0.
  apply FalseE.
  exact neq_7_0 Heq.
- assume Hcase: 7 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 7 = 1.
  apply FalseE.
  exact neq_7_1 Heq.
- assume Hcase: 7 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 7 = 2.
  apply FalseE.
  exact neq_7_2 Heq.
- assume Hcase: 7 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 7 = 3.
  apply FalseE.
  exact neq_7_3 Heq.
- assume Hcase: 7 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 7 = 4.
  apply FalseE.
  exact neq_7_4 Heq.
- assume Hcase: 7 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 7 = 5.
  apply FalseE.
  exact neq_7_5 Heq.
- assume Hcase: 7 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 7 = 6.
  apply FalseE.
  exact neq_7_6 Heq.
- assume Hcase: 7 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andER Hcase.
  assume Hjcases: j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15.
  apply Hjcases.
  + assume Heq: j = 1.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 4.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 9.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 10.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 15.
    apply orIR.
    exact Heq.
- assume Hcase: 7 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 7 = 8.
  apply FalseE.
  exact neq_8_7 Heq.
- assume Hcase: 7 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 7 = 9.
  apply FalseE.
  exact neq_9_7 Heq.
- assume Hcase: 7 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 7 = 10.
  apply FalseE.
  exact neq_10_7 Heq.
- assume Hcase: 7 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 7 = 11.
  apply FalseE.
  exact neq_11_7 Heq.
- assume Hcase: 7 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 7 = 12.
  apply FalseE.
  exact neq_12_7 Heq.
- assume Hcase: 7 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 7 = 13.
  apply FalseE.
  exact neq_13_7 Heq.
- assume Hcase: 7 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 7 = 14.
  apply FalseE.
  exact neq_14_7 Heq.
- assume Hcase: 7 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 7 = 15.
  apply FalseE.
  exact neq_15_7 Heq.
- assume Hcase: 7 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 7 = 16.
  apply FalseE.
  exact neq_16_7 Heq.
Qed.

Theorem Adj17_cases_8 : forall j, Adj17 8 j -> j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14.
let j.
assume H: Adj17 8 j.
apply H.
- assume Hcase: 8 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 8 = 0.
  apply FalseE.
  exact neq_8_0 Heq.
- assume Hcase: 8 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 8 = 1.
  apply FalseE.
  exact neq_8_1 Heq.
- assume Hcase: 8 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 8 = 2.
  apply FalseE.
  exact neq_8_2 Heq.
- assume Hcase: 8 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 8 = 3.
  apply FalseE.
  exact neq_8_3 Heq.
- assume Hcase: 8 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 8 = 4.
  apply FalseE.
  exact neq_8_4 Heq.
- assume Hcase: 8 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 8 = 5.
  apply FalseE.
  exact neq_8_5 Heq.
- assume Hcase: 8 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 8 = 6.
  apply FalseE.
  exact neq_8_6 Heq.
- assume Hcase: 8 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 8 = 7.
  apply FalseE.
  exact neq_8_7 Heq.
- assume Hcase: 8 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andER Hcase.
  assume Hjcases: j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14.
  apply Hjcases.
  + assume Heq: j = 2.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 3.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 9.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 11.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 14.
    apply orIR.
    exact Heq.
- assume Hcase: 8 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 8 = 9.
  apply FalseE.
  exact neq_9_8 Heq.
- assume Hcase: 8 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 8 = 10.
  apply FalseE.
  exact neq_10_8 Heq.
- assume Hcase: 8 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 8 = 11.
  apply FalseE.
  exact neq_11_8 Heq.
- assume Hcase: 8 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 8 = 12.
  apply FalseE.
  exact neq_12_8 Heq.
- assume Hcase: 8 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 8 = 13.
  apply FalseE.
  exact neq_13_8 Heq.
- assume Hcase: 8 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 8 = 14.
  apply FalseE.
  exact neq_14_8 Heq.
- assume Hcase: 8 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 8 = 15.
  apply FalseE.
  exact neq_15_8 Heq.
- assume Hcase: 8 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 8 = 16.
  apply FalseE.
  exact neq_16_8 Heq.
Qed.

Theorem Adj17_cases_9 : forall j, Adj17 9 j -> j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12.
let j.
assume H: Adj17 9 j.
apply H.
- assume Hcase: 9 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 9 = 0.
  apply FalseE.
  exact neq_9_0 Heq.
- assume Hcase: 9 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 9 = 1.
  apply FalseE.
  exact neq_9_1 Heq.
- assume Hcase: 9 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 9 = 2.
  apply FalseE.
  exact neq_9_2 Heq.
- assume Hcase: 9 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 9 = 3.
  apply FalseE.
  exact neq_9_3 Heq.
- assume Hcase: 9 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 9 = 4.
  apply FalseE.
  exact neq_9_4 Heq.
- assume Hcase: 9 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 9 = 5.
  apply FalseE.
  exact neq_9_5 Heq.
- assume Hcase: 9 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 9 = 6.
  apply FalseE.
  exact neq_9_6 Heq.
- assume Hcase: 9 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 9 = 7.
  apply FalseE.
  exact neq_9_7 Heq.
- assume Hcase: 9 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 9 = 8.
  apply FalseE.
  exact neq_9_8 Heq.
- assume Hcase: 9 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andER Hcase.
  assume Hjcases: j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12.
  apply Hjcases.
  + assume Heq: j = 0.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 5.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 7.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 8.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 12.
    apply orIR.
    exact Heq.
- assume Hcase: 9 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 9 = 10.
  apply FalseE.
  exact neq_10_9 Heq.
- assume Hcase: 9 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 9 = 11.
  apply FalseE.
  exact neq_11_9 Heq.
- assume Hcase: 9 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 9 = 12.
  apply FalseE.
  exact neq_12_9 Heq.
- assume Hcase: 9 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 9 = 13.
  apply FalseE.
  exact neq_13_9 Heq.
- assume Hcase: 9 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 9 = 14.
  apply FalseE.
  exact neq_14_9 Heq.
- assume Hcase: 9 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 9 = 15.
  apply FalseE.
  exact neq_15_9 Heq.
- assume Hcase: 9 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 9 = 16.
  apply FalseE.
  exact neq_16_9 Heq.
Qed.

Theorem Adj17_cases_10 : forall j, Adj17 10 j -> j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16.
let j.
assume H: Adj17 10 j.
apply H.
- assume Hcase: 10 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 10 = 0.
  apply FalseE.
  exact neq_10_0 Heq.
- assume Hcase: 10 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 10 = 1.
  apply FalseE.
  exact neq_10_1 Heq.
- assume Hcase: 10 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 10 = 2.
  apply FalseE.
  exact neq_10_2 Heq.
- assume Hcase: 10 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 10 = 3.
  apply FalseE.
  exact neq_10_3 Heq.
- assume Hcase: 10 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 10 = 4.
  apply FalseE.
  exact neq_10_4 Heq.
- assume Hcase: 10 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 10 = 5.
  apply FalseE.
  exact neq_10_5 Heq.
- assume Hcase: 10 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 10 = 6.
  apply FalseE.
  exact neq_10_6 Heq.
- assume Hcase: 10 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 10 = 7.
  apply FalseE.
  exact neq_10_7 Heq.
- assume Hcase: 10 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 10 = 8.
  apply FalseE.
  exact neq_10_8 Heq.
- assume Hcase: 10 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 10 = 9.
  apply FalseE.
  exact neq_10_9 Heq.
- assume Hcase: 10 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andER Hcase.
  assume Hjcases: j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16.
  apply Hjcases.
  + assume Heq: j = 2.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 5.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 6.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 7.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 16.
    apply orIR.
    exact Heq.
- assume Hcase: 10 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 10 = 11.
  apply FalseE.
  exact neq_11_10 Heq.
- assume Hcase: 10 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 10 = 12.
  apply FalseE.
  exact neq_12_10 Heq.
- assume Hcase: 10 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 10 = 13.
  apply FalseE.
  exact neq_13_10 Heq.
- assume Hcase: 10 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 10 = 14.
  apply FalseE.
  exact neq_14_10 Heq.
- assume Hcase: 10 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 10 = 15.
  apply FalseE.
  exact neq_15_10 Heq.
- assume Hcase: 10 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 10 = 16.
  apply FalseE.
  exact neq_16_10 Heq.
Qed.

Theorem Adj17_cases_11 : forall j, Adj17 11 j -> j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15.
let j.
assume H: Adj17 11 j.
apply H.
- assume Hcase: 11 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 11 = 0.
  apply FalseE.
  exact neq_11_0 Heq.
- assume Hcase: 11 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 11 = 1.
  apply FalseE.
  exact neq_11_1 Heq.
- assume Hcase: 11 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 11 = 2.
  apply FalseE.
  exact neq_11_2 Heq.
- assume Hcase: 11 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 11 = 3.
  apply FalseE.
  exact neq_11_3 Heq.
- assume Hcase: 11 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 11 = 4.
  apply FalseE.
  exact neq_11_4 Heq.
- assume Hcase: 11 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 11 = 5.
  apply FalseE.
  exact neq_11_5 Heq.
- assume Hcase: 11 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 11 = 6.
  apply FalseE.
  exact neq_11_6 Heq.
- assume Hcase: 11 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 11 = 7.
  apply FalseE.
  exact neq_11_7 Heq.
- assume Hcase: 11 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 11 = 8.
  apply FalseE.
  exact neq_11_8 Heq.
- assume Hcase: 11 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 11 = 9.
  apply FalseE.
  exact neq_11_9 Heq.
- assume Hcase: 11 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 11 = 10.
  apply FalseE.
  exact neq_11_10 Heq.
- assume Hcase: 11 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andER Hcase.
  assume Hjcases: j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15.
  apply Hjcases.
  + assume Heq: j = 1.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 5.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 6.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 8.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 15.
    apply orIR.
    exact Heq.
- assume Hcase: 11 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 11 = 12.
  apply FalseE.
  exact neq_12_11 Heq.
- assume Hcase: 11 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 11 = 13.
  apply FalseE.
  exact neq_13_11 Heq.
- assume Hcase: 11 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 11 = 14.
  apply FalseE.
  exact neq_14_11 Heq.
- assume Hcase: 11 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 11 = 15.
  apply FalseE.
  exact neq_15_11 Heq.
- assume Hcase: 11 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 11 = 16.
  apply FalseE.
  exact neq_16_11 Heq.
Qed.

Theorem Adj17_cases_12 : forall j, Adj17 12 j -> j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13.
let j.
assume H: Adj17 12 j.
apply H.
- assume Hcase: 12 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 12 = 0.
  apply FalseE.
  exact neq_12_0 Heq.
- assume Hcase: 12 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 12 = 1.
  apply FalseE.
  exact neq_12_1 Heq.
- assume Hcase: 12 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 12 = 2.
  apply FalseE.
  exact neq_12_2 Heq.
- assume Hcase: 12 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 12 = 3.
  apply FalseE.
  exact neq_12_3 Heq.
- assume Hcase: 12 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 12 = 4.
  apply FalseE.
  exact neq_12_4 Heq.
- assume Hcase: 12 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 12 = 5.
  apply FalseE.
  exact neq_12_5 Heq.
- assume Hcase: 12 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 12 = 6.
  apply FalseE.
  exact neq_12_6 Heq.
- assume Hcase: 12 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 12 = 7.
  apply FalseE.
  exact neq_12_7 Heq.
- assume Hcase: 12 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 12 = 8.
  apply FalseE.
  exact neq_12_8 Heq.
- assume Hcase: 12 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 12 = 9.
  apply FalseE.
  exact neq_12_9 Heq.
- assume Hcase: 12 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 12 = 10.
  apply FalseE.
  exact neq_12_10 Heq.
- assume Hcase: 12 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 12 = 11.
  apply FalseE.
  exact neq_12_11 Heq.
- assume Hcase: 12 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andER Hcase.
  assume Hjcases: j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13.
  apply Hjcases.
  + assume Heq: j = 2.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 4.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 6.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 9.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 13.
    apply orIR.
    exact Heq.
- assume Hcase: 12 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 12 = 13.
  apply FalseE.
  exact neq_13_12 Heq.
- assume Hcase: 12 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 12 = 14.
  apply FalseE.
  exact neq_14_12 Heq.
- assume Hcase: 12 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 12 = 15.
  apply FalseE.
  exact neq_15_12 Heq.
- assume Hcase: 12 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 12 = 16.
  apply FalseE.
  exact neq_16_12 Heq.
Qed.

Theorem Adj17_cases_13 : forall j, Adj17 13 j -> j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14.
let j.
assume H: Adj17 13 j.
apply H.
- assume Hcase: 13 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 13 = 0.
  apply FalseE.
  exact neq_13_0 Heq.
- assume Hcase: 13 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 13 = 1.
  apply FalseE.
  exact neq_13_1 Heq.
- assume Hcase: 13 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 13 = 2.
  apply FalseE.
  exact neq_13_2 Heq.
- assume Hcase: 13 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 13 = 3.
  apply FalseE.
  exact neq_13_3 Heq.
- assume Hcase: 13 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 13 = 4.
  apply FalseE.
  exact neq_13_4 Heq.
- assume Hcase: 13 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 13 = 5.
  apply FalseE.
  exact neq_13_5 Heq.
- assume Hcase: 13 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 13 = 6.
  apply FalseE.
  exact neq_13_6 Heq.
- assume Hcase: 13 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 13 = 7.
  apply FalseE.
  exact neq_13_7 Heq.
- assume Hcase: 13 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 13 = 8.
  apply FalseE.
  exact neq_13_8 Heq.
- assume Hcase: 13 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 13 = 9.
  apply FalseE.
  exact neq_13_9 Heq.
- assume Hcase: 13 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 13 = 10.
  apply FalseE.
  exact neq_13_10 Heq.
- assume Hcase: 13 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 13 = 11.
  apply FalseE.
  exact neq_13_11 Heq.
- assume Hcase: 13 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 13 = 12.
  apply FalseE.
  exact neq_13_12 Heq.
- assume Hcase: 13 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andER Hcase.
  assume Hjcases: j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14.
  apply Hjcases.
  + assume Heq: j = 1.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 3.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 5.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 12.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 14.
    apply orIR.
    exact Heq.
- assume Hcase: 13 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 13 = 14.
  apply FalseE.
  exact neq_14_13 Heq.
- assume Hcase: 13 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 13 = 15.
  apply FalseE.
  exact neq_15_13 Heq.
- assume Hcase: 13 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 13 = 16.
  apply FalseE.
  exact neq_16_13 Heq.
Qed.

Theorem Adj17_cases_14 : forall j, Adj17 14 j -> j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13.
let j.
assume H: Adj17 14 j.
apply H.
- assume Hcase: 14 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 14 = 0.
  apply FalseE.
  exact neq_14_0 Heq.
- assume Hcase: 14 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 14 = 1.
  apply FalseE.
  exact neq_14_1 Heq.
- assume Hcase: 14 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 14 = 2.
  apply FalseE.
  exact neq_14_2 Heq.
- assume Hcase: 14 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 14 = 3.
  apply FalseE.
  exact neq_14_3 Heq.
- assume Hcase: 14 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 14 = 4.
  apply FalseE.
  exact neq_14_4 Heq.
- assume Hcase: 14 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 14 = 5.
  apply FalseE.
  exact neq_14_5 Heq.
- assume Hcase: 14 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 14 = 6.
  apply FalseE.
  exact neq_14_6 Heq.
- assume Hcase: 14 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 14 = 7.
  apply FalseE.
  exact neq_14_7 Heq.
- assume Hcase: 14 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 14 = 8.
  apply FalseE.
  exact neq_14_8 Heq.
- assume Hcase: 14 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 14 = 9.
  apply FalseE.
  exact neq_14_9 Heq.
- assume Hcase: 14 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 14 = 10.
  apply FalseE.
  exact neq_14_10 Heq.
- assume Hcase: 14 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 14 = 11.
  apply FalseE.
  exact neq_14_11 Heq.
- assume Hcase: 14 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 14 = 12.
  apply FalseE.
  exact neq_14_12 Heq.
- assume Hcase: 14 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 14 = 13.
  apply FalseE.
  exact neq_14_13 Heq.
- assume Hcase: 14 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andER Hcase.
  assume Hjcases: j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13.
  apply Hjcases.
  + assume Heq: j = 0.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 4.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 6.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 8.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 13.
    apply orIR.
    exact Heq.
- assume Hcase: 14 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 14 = 15.
  apply FalseE.
  exact neq_15_14 Heq.
- assume Hcase: 14 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 14 = 16.
  apply FalseE.
  exact neq_16_14 Heq.
Qed.

Theorem Adj17_cases_15 : forall j, Adj17 15 j -> j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11.
let j.
assume H: Adj17 15 j.
apply H.
- assume Hcase: 15 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 15 = 0.
  apply FalseE.
  exact neq_15_0 Heq.
- assume Hcase: 15 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 15 = 1.
  apply FalseE.
  exact neq_15_1 Heq.
- assume Hcase: 15 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 15 = 2.
  apply FalseE.
  exact neq_15_2 Heq.
- assume Hcase: 15 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 15 = 3.
  apply FalseE.
  exact neq_15_3 Heq.
- assume Hcase: 15 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 15 = 4.
  apply FalseE.
  exact neq_15_4 Heq.
- assume Hcase: 15 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 15 = 5.
  apply FalseE.
  exact neq_15_5 Heq.
- assume Hcase: 15 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 15 = 6.
  apply FalseE.
  exact neq_15_6 Heq.
- assume Hcase: 15 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 15 = 7.
  apply FalseE.
  exact neq_15_7 Heq.
- assume Hcase: 15 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 15 = 8.
  apply FalseE.
  exact neq_15_8 Heq.
- assume Hcase: 15 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 15 = 9.
  apply FalseE.
  exact neq_15_9 Heq.
- assume Hcase: 15 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 15 = 10.
  apply FalseE.
  exact neq_15_10 Heq.
- assume Hcase: 15 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 15 = 11.
  apply FalseE.
  exact neq_15_11 Heq.
- assume Hcase: 15 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 15 = 12.
  apply FalseE.
  exact neq_15_12 Heq.
- assume Hcase: 15 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 15 = 13.
  apply FalseE.
  exact neq_15_13 Heq.
- assume Hcase: 15 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 15 = 14.
  apply FalseE.
  exact neq_15_14 Heq.
- assume Hcase: 15 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andER Hcase.
  assume Hjcases: j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11.
  apply Hjcases.
  + assume Heq: j = 0.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 2.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 3.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 7.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 11.
    apply orIR.
    exact Heq.
- assume Hcase: 15 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andEL Hcase.
  assume Heq: 15 = 16.
  apply FalseE.
  exact neq_16_15 Heq.
Qed.

Theorem Adj17_cases_16 : forall j, Adj17 16 j -> j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10.
let j.
assume H: Adj17 16 j.
apply H.
- assume Hcase: 16 = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 16 = 0.
  apply FalseE.
  exact neq_16_0 Heq.
- assume Hcase: 16 = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 16 = 1.
  apply FalseE.
  exact neq_16_1 Heq.
- assume Hcase: 16 = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 16 = 2.
  apply FalseE.
  exact neq_16_2 Heq.
- assume Hcase: 16 = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 16 = 3.
  apply FalseE.
  exact neq_16_3 Heq.
- assume Hcase: 16 = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 16 = 4.
  apply FalseE.
  exact neq_16_4 Heq.
- assume Hcase: 16 = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 16 = 5.
  apply FalseE.
  exact neq_16_5 Heq.
- assume Hcase: 16 = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 16 = 6.
  apply FalseE.
  exact neq_16_6 Heq.
- assume Hcase: 16 = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 16 = 7.
  apply FalseE.
  exact neq_16_7 Heq.
- assume Hcase: 16 = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 16 = 8.
  apply FalseE.
  exact neq_16_8 Heq.
- assume Hcase: 16 = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12).
  apply andEL Hcase.
  assume Heq: 16 = 9.
  apply FalseE.
  exact neq_16_9 Heq.
- assume Hcase: 16 = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16).
  apply andEL Hcase.
  assume Heq: 16 = 10.
  apply FalseE.
  exact neq_16_10 Heq.
- assume Hcase: 16 = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15).
  apply andEL Hcase.
  assume Heq: 16 = 11.
  apply FalseE.
  exact neq_16_11 Heq.
- assume Hcase: 16 = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 16 = 12.
  apply FalseE.
  exact neq_16_12 Heq.
- assume Hcase: 16 = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14).
  apply andEL Hcase.
  assume Heq: 16 = 13.
  apply FalseE.
  exact neq_16_13 Heq.
- assume Hcase: 16 = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13).
  apply andEL Hcase.
  assume Heq: 16 = 14.
  apply FalseE.
  exact neq_16_14 Heq.
- assume Hcase: 16 = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11).
  apply andEL Hcase.
  assume Heq: 16 = 15.
  apply FalseE.
  exact neq_16_15 Heq.
- assume Hcase: 16 = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10).
  apply andER Hcase.
  assume Hjcases: j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10.
  apply Hjcases.
  + assume Heq: j = 0.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIL.
    exact Heq.
  + assume Heq: j = 1.
    apply orIL.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 3.
    apply orIL.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 4.
    apply orIL.
    apply orIR.
    exact Heq.
  + assume Heq: j = 10.
    apply orIR.
    exact Heq.
Qed.

Theorem Adj17_triangle_free : triangle_free 17 Adj17.
prove forall x :e 17, forall y :e 17, forall z :e 17, Adj17 x y -> Adj17 y z -> Adj17 x z -> False.
let x. assume Hx: x :e 17.
let y. assume Hy: y :e 17.
let z. assume Hz: z :e 17.
assume Hxy: Adj17 x y.
assume Hyz: Adj17 y z.
assume Hxz: Adj17 x z.
apply Hxy.
- assume Hxy_case: x = 0 /\ (y = 9 \/ y = 14 \/ y = 15 \/ y = 16).
  apply Hxy_case.
  assume Hx_eq: x = 0.
  assume Hy_cases: y = 9 \/ y = 14 \/ y = 15 \/ y = 16.
  apply Hy_cases.
  - assume Hy_eq: y = 9.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_9 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_0.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_7.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_8.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_12.
      exact Hxz.
  - assume Hy_eq: y = 14.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_14 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_0.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_13.
      exact Hxz.
  - assume Hy_eq: y = 15.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_15 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_0.
      exact Hxz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_3.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_11.
      exact Hxz.
  - assume Hy_eq: y = 16.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_16 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_0.
      exact Hxz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_3.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_4.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_0_10.
      exact Hxz.
- assume Hxy_case: x = 1 /\ (y = 7 \/ y = 11 \/ y = 13 \/ y = 16).
  apply Hxy_case.
  assume Hx_eq: x = 1.
  assume Hy_cases: y = 7 \/ y = 11 \/ y = 13 \/ y = 16.
  apply Hy_cases.
  - assume Hy_eq: y = 7.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_7 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_1.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_10.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_15.
      exact Hxz.
  - assume Hy_eq: y = 11.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_11 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_1.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_8.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_15.
      exact Hxz.
  - assume Hy_eq: y = 13.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_13 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_3.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_5.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_14.
      exact Hxz.
  - assume Hy_eq: y = 16.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_16 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_0.
      exact Hxz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_3.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_4.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_1_10.
      exact Hxz.
- assume Hxy_case: x = 2 /\ (y = 8 \/ y = 10 \/ y = 12 \/ y = 15).
  apply Hxy_case.
  assume Hx_eq: x = 2.
  assume Hy_cases: y = 8 \/ y = 10 \/ y = 12 \/ y = 15.
  apply Hy_cases.
  - assume Hy_eq: y = 8.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_8 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_3.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_9.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_11.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_14.
      exact Hxz.
  - assume Hy_eq: y = 10.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_10 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_2.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_6.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_7.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_16.
      exact Hxz.
  - assume Hy_eq: y = 12.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_12 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_2.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_6.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_9.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_13.
      exact Hxz.
  - assume Hy_eq: y = 15.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_15 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_0.
      exact Hxz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_3.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_2_11.
      exact Hxz.
- assume Hxy_case: x = 3 /\ (y = 6 \/ y = 8 \/ y = 13 \/ y = 15 \/ y = 16).
  apply Hxy_case.
  assume Hx_eq: x = 3.
  assume Hy_cases: y = 6 \/ y = 8 \/ y = 13 \/ y = 15 \/ y = 16.
  apply Hy_cases.
  - assume Hy_eq: y = 6.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_6 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_3.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_11.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_14.
      exact Hxz.
  - assume Hy_eq: y = 8.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_8 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_3.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_9.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_11.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_14.
      exact Hxz.
  - assume Hy_eq: y = 13.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_13 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_3.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_5.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_14.
      exact Hxz.
  - assume Hy_eq: y = 15.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_15 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_0.
      exact Hxz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_3.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_11.
      exact Hxz.
  - assume Hy_eq: y = 16.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_16 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_0.
      exact Hxz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_3.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_4.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_3_10.
      exact Hxz.
- assume Hxy_case: x = 4 /\ (y = 5 \/ y = 7 \/ y = 12 \/ y = 14 \/ y = 16).
  apply Hxy_case.
  assume Hx_eq: x = 4.
  assume Hy_cases: y = 5 \/ y = 7 \/ y = 12 \/ y = 14 \/ y = 16.
  apply Hy_cases.
  - assume Hy_eq: y = 5.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_5 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_13.
      exact Hxz.
  - assume Hy_eq: y = 7.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_7 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_1.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_10.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_15.
      exact Hxz.
  - assume Hy_eq: y = 12.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_12 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_2.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_6.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_9.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_13.
      exact Hxz.
  - assume Hy_eq: y = 14.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_14 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_0.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_13.
      exact Hxz.
  - assume Hy_eq: y = 16.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_16 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_0.
      exact Hxz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_3.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_4.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_4_10.
      exact Hxz.
- assume Hxy_case: x = 5 /\ (y = 4 \/ y = 9 \/ y = 10 \/ y = 11 \/ y = 13).
  apply Hxy_case.
  assume Hx_eq: x = 5.
  assume Hy_cases: y = 4 \/ y = 9 \/ y = 10 \/ y = 11 \/ y = 13.
  apply Hy_cases.
  - assume Hy_eq: y = 4.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_4 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_7.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_14.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_16.
      exact Hxz.
  - assume Hy_eq: y = 9.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_9 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_0.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_7.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_8.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_12.
      exact Hxz.
  - assume Hy_eq: y = 10.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_10 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_2.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_6.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_7.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_16.
      exact Hxz.
  - assume Hy_eq: y = 11.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_11 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_1.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_8.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_15.
      exact Hxz.
  - assume Hy_eq: y = 13.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_13 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_3.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_5.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_5_14.
      exact Hxz.
- assume Hxy_case: x = 6 /\ (y = 3 \/ y = 10 \/ y = 11 \/ y = 12 \/ y = 14).
  apply Hxy_case.
  assume Hx_eq: x = 6.
  assume Hy_cases: y = 3 \/ y = 10 \/ y = 11 \/ y = 12 \/ y = 14.
  apply Hy_cases.
  - assume Hy_eq: y = 3.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_3 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_13.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_16.
      exact Hxz.
  - assume Hy_eq: y = 10.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_10 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_2.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_6.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_7.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_16.
      exact Hxz.
  - assume Hy_eq: y = 11.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_11 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_1.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_8.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_15.
      exact Hxz.
  - assume Hy_eq: y = 12.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_12 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_2.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_6.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_9.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_13.
      exact Hxz.
  - assume Hy_eq: y = 14.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_14 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_0.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_6_13.
      exact Hxz.
- assume Hxy_case: x = 7 /\ (y = 1 \/ y = 4 \/ y = 9 \/ y = 10 \/ y = 15).
  apply Hxy_case.
  assume Hx_eq: x = 7.
  assume Hy_cases: y = 1 \/ y = 4 \/ y = 9 \/ y = 10 \/ y = 15.
  apply Hy_cases.
  - assume Hy_eq: y = 1.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_1 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_13.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_16.
      exact Hxz.
  - assume Hy_eq: y = 4.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_4 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_7.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_14.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_16.
      exact Hxz.
  - assume Hy_eq: y = 9.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_9 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_0.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_7.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_8.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_12.
      exact Hxz.
  - assume Hy_eq: y = 10.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_10 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_2.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_6.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_7.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_16.
      exact Hxz.
  - assume Hy_eq: y = 15.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_15 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_0.
      exact Hxz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_3.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_7_11.
      exact Hxz.
- assume Hxy_case: x = 8 /\ (y = 2 \/ y = 3 \/ y = 9 \/ y = 11 \/ y = 14).
  apply Hxy_case.
  assume Hx_eq: x = 8.
  assume Hy_cases: y = 2 \/ y = 3 \/ y = 9 \/ y = 11 \/ y = 14.
  apply Hy_cases.
  - assume Hy_eq: y = 2.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_2 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_8.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_10.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_12.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_15.
      exact Hxz.
  - assume Hy_eq: y = 3.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_3 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_13.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_16.
      exact Hxz.
  - assume Hy_eq: y = 9.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_9 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_0.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_7.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_8.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_12.
      exact Hxz.
  - assume Hy_eq: y = 11.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_11 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_1.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_8.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_15.
      exact Hxz.
  - assume Hy_eq: y = 14.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_14 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_0.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_8_13.
      exact Hxz.
- assume Hxy_case: x = 9 /\ (y = 0 \/ y = 5 \/ y = 7 \/ y = 8 \/ y = 12).
  apply Hxy_case.
  assume Hx_eq: x = 9.
  assume Hy_cases: y = 0 \/ y = 5 \/ y = 7 \/ y = 8 \/ y = 12.
  apply Hy_cases.
  - assume Hy_eq: y = 0.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_0 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_9.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_14.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_16.
      exact Hxz.
  - assume Hy_eq: y = 5.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_5 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_13.
      exact Hxz.
  - assume Hy_eq: y = 7.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_7 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_1.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_10.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_15.
      exact Hxz.
  - assume Hy_eq: y = 8.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_8 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_3.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_9.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_11.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_14.
      exact Hxz.
  - assume Hy_eq: y = 12.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_12 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_2.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_6.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_9.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_9_13.
      exact Hxz.
- assume Hxy_case: x = 10 /\ (y = 2 \/ y = 5 \/ y = 6 \/ y = 7 \/ y = 16).
  apply Hxy_case.
  assume Hx_eq: x = 10.
  assume Hy_cases: y = 2 \/ y = 5 \/ y = 6 \/ y = 7 \/ y = 16.
  apply Hy_cases.
  - assume Hy_eq: y = 2.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_2 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_8.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_10.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_12.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_15.
      exact Hxz.
  - assume Hy_eq: y = 5.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_5 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_13.
      exact Hxz.
  - assume Hy_eq: y = 6.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_6 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_3.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_11.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_14.
      exact Hxz.
  - assume Hy_eq: y = 7.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_7 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_1.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_10.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_15.
      exact Hxz.
  - assume Hy_eq: y = 16.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_16 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_0.
      exact Hxz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_3.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_4.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_10_10.
      exact Hxz.
- assume Hxy_case: x = 11 /\ (y = 1 \/ y = 5 \/ y = 6 \/ y = 8 \/ y = 15).
  apply Hxy_case.
  assume Hx_eq: x = 11.
  assume Hy_cases: y = 1 \/ y = 5 \/ y = 6 \/ y = 8 \/ y = 15.
  apply Hy_cases.
  - assume Hy_eq: y = 1.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_1 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_13.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_16.
      exact Hxz.
  - assume Hy_eq: y = 5.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_5 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_13.
      exact Hxz.
  - assume Hy_eq: y = 6.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_6 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_3.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_11.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_14.
      exact Hxz.
  - assume Hy_eq: y = 8.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_8 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_3.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_9.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_11.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_14.
      exact Hxz.
  - assume Hy_eq: y = 15.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_15 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_0.
      exact Hxz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_3.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_11_11.
      exact Hxz.
- assume Hxy_case: x = 12 /\ (y = 2 \/ y = 4 \/ y = 6 \/ y = 9 \/ y = 13).
  apply Hxy_case.
  assume Hx_eq: x = 12.
  assume Hy_cases: y = 2 \/ y = 4 \/ y = 6 \/ y = 9 \/ y = 13.
  apply Hy_cases.
  - assume Hy_eq: y = 2.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_2 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_8.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_10.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_12.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_15.
      exact Hxz.
  - assume Hy_eq: y = 4.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_4 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_7.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_14.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_16.
      exact Hxz.
  - assume Hy_eq: y = 6.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_6 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_3.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_11.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_14.
      exact Hxz.
  - assume Hy_eq: y = 9.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_9 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_0.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_7.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_8.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_12.
      exact Hxz.
  - assume Hy_eq: y = 13.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_13 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_3.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_5.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_12_14.
      exact Hxz.
- assume Hxy_case: x = 13 /\ (y = 1 \/ y = 3 \/ y = 5 \/ y = 12 \/ y = 14).
  apply Hxy_case.
  assume Hx_eq: x = 13.
  assume Hy_cases: y = 1 \/ y = 3 \/ y = 5 \/ y = 12 \/ y = 14.
  apply Hy_cases.
  - assume Hy_eq: y = 1.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_1 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_13.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_16.
      exact Hxz.
  - assume Hy_eq: y = 3.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_3 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_13.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_16.
      exact Hxz.
  - assume Hy_eq: y = 5.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_5 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_13.
      exact Hxz.
  - assume Hy_eq: y = 12.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_12 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_2.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_6.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_9.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_13.
      exact Hxz.
  - assume Hy_eq: y = 14.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_14 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 0.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_0.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_4.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_13_13.
      exact Hxz.
- assume Hxy_case: x = 14 /\ (y = 0 \/ y = 4 \/ y = 6 \/ y = 8 \/ y = 13).
  apply Hxy_case.
  assume Hx_eq: x = 14.
  assume Hy_cases: y = 0 \/ y = 4 \/ y = 6 \/ y = 8 \/ y = 13.
  apply Hy_cases.
  - assume Hy_eq: y = 0.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_0 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_9.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_14.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_16.
      exact Hxz.
  - assume Hy_eq: y = 4.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_4 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_7.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_14.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_16.
      exact Hxz.
  - assume Hy_eq: y = 6.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_6 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_3.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_10.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_11.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_14.
      exact Hxz.
  - assume Hy_eq: y = 8.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_8 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_2.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_3.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_9.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_11.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_14.
      exact Hxz.
  - assume Hy_eq: y = 13.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_13 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_1.
      exact Hxz.
    - assume Hz_eq: z = 3.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_3.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_5.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_14_14.
      exact Hxz.
- assume Hxy_case: x = 15 /\ (y = 0 \/ y = 2 \/ y = 3 \/ y = 7 \/ y = 11).
  apply Hxy_case.
  assume Hx_eq: x = 15.
  assume Hy_cases: y = 0 \/ y = 2 \/ y = 3 \/ y = 7 \/ y = 11.
  apply Hy_cases.
  - assume Hy_eq: y = 0.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_0 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_9.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_14.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_16.
      exact Hxz.
  - assume Hy_eq: y = 2.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_2 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_8.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_10.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_12.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_15.
      exact Hxz.
  - assume Hy_eq: y = 3.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_3 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_13.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_16.
      exact Hxz.
  - assume Hy_eq: y = 7.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_7 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_1.
      exact Hxz.
    - assume Hz_eq: z = 4.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_4.
      exact Hxz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_9.
      exact Hxz.
    - assume Hz_eq: z = 10.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_10.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_15.
      exact Hxz.
  - assume Hy_eq: y = 11.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_11 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 1.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_1.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_8.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_15_15.
      exact Hxz.
- assume Hxy_case: x = 16 /\ (y = 0 \/ y = 1 \/ y = 3 \/ y = 4 \/ y = 10).
  apply Hxy_case.
  assume Hx_eq: x = 16.
  assume Hy_cases: y = 0 \/ y = 1 \/ y = 3 \/ y = 4 \/ y = 10.
  apply Hy_cases.
  - assume Hy_eq: y = 0.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_0 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 9.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_9.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_14.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_16.
      exact Hxz.
  - assume Hy_eq: y = 1.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_1 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_7.
      exact Hxz.
    - assume Hz_eq: z = 11.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_11.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_13.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_16.
      exact Hxz.
  - assume Hy_eq: y = 3.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_3 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_6.
      exact Hxz.
    - assume Hz_eq: z = 8.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_8.
      exact Hxz.
    - assume Hz_eq: z = 13.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_13.
      exact Hxz.
    - assume Hz_eq: z = 15.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_15.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_16.
      exact Hxz.
  - assume Hy_eq: y = 4.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_4 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_5.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_7.
      exact Hxz.
    - assume Hz_eq: z = 12.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_12.
      exact Hxz.
    - assume Hz_eq: z = 14.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_14.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_16.
      exact Hxz.
  - assume Hy_eq: y = 10.
    rewrite Hx_eq in Hxz.
    rewrite Hy_eq in Hyz.
    apply Adj17_cases_10 in Hyz.
    apply Hyz.
    - assume Hz_eq: z = 2.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_2.
      exact Hxz.
    - assume Hz_eq: z = 5.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_5.
      exact Hxz.
    - assume Hz_eq: z = 6.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_6.
      exact Hxz.
    - assume Hz_eq: z = 7.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_7.
      exact Hxz.
    - assume Hz_eq: z = 16.
      rewrite Hz_eq in Hxz.
      apply Adj17_not_16_16.
      exact Hxz.
Qed.
(* Proof branches: 398 two-edge paths *)
