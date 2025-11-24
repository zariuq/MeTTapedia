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

Theorem Adj17_not_0_1 : ~Adj17 0 1.
assume H: Adj17 0 1.
prove False.
apply H.
- assume Hcase: 0 = 0 /\ (1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16).
  apply Hcase.
  assume Heq0: 0 = 0.
  assume Hjcases: 1 = 9 \/ 1 = 14 \/ 1 = 15 \/ 1 = 16.
  apply Hjcases.
  + assume Heq: 1 = 9. exact neq_9_1 Heq.
  + assume Heq: 1 = 14. exact neq_14_1 Heq.
  + assume Heq: 1 = 15. exact neq_15_1 Heq.
  + assume Heq: 1 = 16. exact neq_16_1 Heq.
- assume Hcase: 0 = 1 /\ (1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16).
  apply Hcase.
  assume Heq0: 0 = 1.
  assume _: 1 = 7 \/ 1 = 11 \/ 1 = 13 \/ 1 = 16.
  exact neq_1_0 Heq0.
- assume Hcase: 0 = 2 /\ (1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15).
  apply Hcase.
  assume Heq0: 0 = 2.
  assume _: 1 = 8 \/ 1 = 10 \/ 1 = 12 \/ 1 = 15.
  exact neq_2_0 Heq0.
- assume Hcase: 0 = 3 /\ (1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16).
  apply Hcase.
  assume Heq0: 0 = 3.
  assume _: 1 = 6 \/ 1 = 8 \/ 1 = 13 \/ 1 = 15 \/ 1 = 16.
  exact neq_3_0 Heq0.
- assume Hcase: 0 = 4 /\ (1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16).
  apply Hcase.
  assume Heq0: 0 = 4.
  assume _: 1 = 5 \/ 1 = 7 \/ 1 = 12 \/ 1 = 14 \/ 1 = 16.
  exact neq_4_0 Heq0.
- assume Hcase: 0 = 5 /\ (1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13).
  apply Hcase.
  assume Heq0: 0 = 5.
  assume _: 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 11 \/ 1 = 13.
  exact neq_5_0 Heq0.
- assume Hcase: 0 = 6 /\ (1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14).
  apply Hcase.
  assume Heq0: 0 = 6.
  assume _: 1 = 3 \/ 1 = 10 \/ 1 = 11 \/ 1 = 12 \/ 1 = 14.
  exact neq_6_0 Heq0.
- assume Hcase: 0 = 7 /\ (1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15).
  apply Hcase.
  assume Heq0: 0 = 7.
  assume _: 1 = 1 \/ 1 = 4 \/ 1 = 9 \/ 1 = 10 \/ 1 = 15.
  exact neq_7_0 Heq0.
- assume Hcase: 0 = 8 /\ (1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14).
  apply Hcase.
  assume Heq0: 0 = 8.
  assume _: 1 = 2 \/ 1 = 3 \/ 1 = 9 \/ 1 = 11 \/ 1 = 14.
  exact neq_8_0 Heq0.
- assume Hcase: 0 = 9 /\ (1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12).
  apply Hcase.
  assume Heq0: 0 = 9.
  assume _: 1 = 0 \/ 1 = 5 \/ 1 = 7 \/ 1 = 8 \/ 1 = 12.
  exact neq_9_0 Heq0.
- assume Hcase: 0 = 10 /\ (1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16).
  apply Hcase.
  assume Heq0: 0 = 10.
  assume _: 1 = 2 \/ 1 = 5 \/ 1 = 6 \/ 1 = 7 \/ 1 = 16.
  exact neq_10_0 Heq0.
- assume Hcase: 0 = 11 /\ (1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15).
  apply Hcase.
  assume Heq0: 0 = 11.
  assume _: 1 = 1 \/ 1 = 5 \/ 1 = 6 \/ 1 = 8 \/ 1 = 15.
  exact neq_11_0 Heq0.
- assume Hcase: 0 = 12 /\ (1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13).
  apply Hcase.
  assume Heq0: 0 = 12.
  assume _: 1 = 2 \/ 1 = 4 \/ 1 = 6 \/ 1 = 9 \/ 1 = 13.
  exact neq_12_0 Heq0.
- assume Hcase: 0 = 13 /\ (1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14).
  apply Hcase.
  assume Heq0: 0 = 13.
  assume _: 1 = 1 \/ 1 = 3 \/ 1 = 5 \/ 1 = 12 \/ 1 = 14.
  exact neq_13_0 Heq0.
- assume Hcase: 0 = 14 /\ (1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13).
  apply Hcase.
  assume Heq0: 0 = 14.
  assume _: 1 = 0 \/ 1 = 4 \/ 1 = 6 \/ 1 = 8 \/ 1 = 13.
  exact neq_14_0 Heq0.
- assume Hcase: 0 = 15 /\ (1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11).
  apply Hcase.
  assume Heq0: 0 = 15.
  assume _: 1 = 0 \/ 1 = 2 \/ 1 = 3 \/ 1 = 7 \/ 1 = 11.
  exact neq_15_0 Heq0.
- assume Hcase: 0 = 16 /\ (1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10).
  apply Hcase.
  assume Heq0: 0 = 16.
  assume _: 1 = 0 \/ 1 = 1 \/ 1 = 3 \/ 1 = 4 \/ 1 = 10.
  exact neq_16_0 Heq0.
Qed.
