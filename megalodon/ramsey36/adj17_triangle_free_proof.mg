Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Theorem tf_0_0_0 : Adj17 0 0 -> Adj17 0 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_1 : Adj17 0 0 -> Adj17 0 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 1. assume H3: Adj17 0 1.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_2 : Adj17 0 0 -> Adj17 0 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 2. assume H3: Adj17 0 2.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_3 : Adj17 0 0 -> Adj17 0 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 3. assume H3: Adj17 0 3.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_4 : Adj17 0 0 -> Adj17 0 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 4. assume H3: Adj17 0 4.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_5 : Adj17 0 0 -> Adj17 0 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 5. assume H3: Adj17 0 5.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_6 : Adj17 0 0 -> Adj17 0 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 6. assume H3: Adj17 0 6.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_7 : Adj17 0 0 -> Adj17 0 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 7. assume H3: Adj17 0 7.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_8 : Adj17 0 0 -> Adj17 0 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 8. assume H3: Adj17 0 8.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_9 : Adj17 0 0 -> Adj17 0 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 9. assume H3: Adj17 0 9.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_10 : Adj17 0 0 -> Adj17 0 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 10. assume H3: Adj17 0 10.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_11 : Adj17 0 0 -> Adj17 0 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 11. assume H3: Adj17 0 11.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_12 : Adj17 0 0 -> Adj17 0 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 12. assume H3: Adj17 0 12.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_13 : Adj17 0 0 -> Adj17 0 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 13. assume H3: Adj17 0 13.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_14 : Adj17 0 0 -> Adj17 0 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 14. assume H3: Adj17 0 14.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_15 : Adj17 0 0 -> Adj17 0 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 15. assume H3: Adj17 0 15.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_0_16 : Adj17 0 0 -> Adj17 0 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 0. assume H2: Adj17 0 16. assume H3: Adj17 0 16.
exact Adj17_not_0_0 H1.
Qed.

Theorem tf_0_1_0 : Adj17 0 1 -> Adj17 1 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_1_1 : Adj17 0 1 -> Adj17 1 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 1. assume H3: Adj17 0 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_0_1_2 : Adj17 0 1 -> Adj17 1 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 2. assume H3: Adj17 0 2.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_3 : Adj17 0 1 -> Adj17 1 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 3. assume H3: Adj17 0 3.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_4 : Adj17 0 1 -> Adj17 1 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 4. assume H3: Adj17 0 4.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_5 : Adj17 0 1 -> Adj17 1 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 5. assume H3: Adj17 0 5.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_6 : Adj17 0 1 -> Adj17 1 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 6. assume H3: Adj17 0 6.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_7 : Adj17 0 1 -> Adj17 1 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 7. assume H3: Adj17 0 7.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_8 : Adj17 0 1 -> Adj17 1 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 8. assume H3: Adj17 0 8.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_9 : Adj17 0 1 -> Adj17 1 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 9. assume H3: Adj17 0 9.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_10 : Adj17 0 1 -> Adj17 1 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 10. assume H3: Adj17 0 10.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_11 : Adj17 0 1 -> Adj17 1 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 11. assume H3: Adj17 0 11.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_12 : Adj17 0 1 -> Adj17 1 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 12. assume H3: Adj17 0 12.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_13 : Adj17 0 1 -> Adj17 1 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 13. assume H3: Adj17 0 13.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_14 : Adj17 0 1 -> Adj17 1 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 14. assume H3: Adj17 0 14.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_15 : Adj17 0 1 -> Adj17 1 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 15. assume H3: Adj17 0 15.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_1_16 : Adj17 0 1 -> Adj17 1 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 1. assume H2: Adj17 1 16. assume H3: Adj17 0 16.
exact Adj17_not_0_1 H1.
Qed.

Theorem tf_0_2_0 : Adj17 0 2 -> Adj17 2 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_2_1 : Adj17 0 2 -> Adj17 2 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 1. assume H3: Adj17 0 1.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_2 : Adj17 0 2 -> Adj17 2 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 2. assume H3: Adj17 0 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_0_2_3 : Adj17 0 2 -> Adj17 2 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 3. assume H3: Adj17 0 3.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_4 : Adj17 0 2 -> Adj17 2 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 4. assume H3: Adj17 0 4.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_5 : Adj17 0 2 -> Adj17 2 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 5. assume H3: Adj17 0 5.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_6 : Adj17 0 2 -> Adj17 2 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 6. assume H3: Adj17 0 6.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_7 : Adj17 0 2 -> Adj17 2 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 7. assume H3: Adj17 0 7.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_8 : Adj17 0 2 -> Adj17 2 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 8. assume H3: Adj17 0 8.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_9 : Adj17 0 2 -> Adj17 2 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 9. assume H3: Adj17 0 9.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_10 : Adj17 0 2 -> Adj17 2 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 10. assume H3: Adj17 0 10.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_11 : Adj17 0 2 -> Adj17 2 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 11. assume H3: Adj17 0 11.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_12 : Adj17 0 2 -> Adj17 2 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 12. assume H3: Adj17 0 12.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_13 : Adj17 0 2 -> Adj17 2 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 13. assume H3: Adj17 0 13.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_14 : Adj17 0 2 -> Adj17 2 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 14. assume H3: Adj17 0 14.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_15 : Adj17 0 2 -> Adj17 2 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 15. assume H3: Adj17 0 15.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_2_16 : Adj17 0 2 -> Adj17 2 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 2. assume H2: Adj17 2 16. assume H3: Adj17 0 16.
exact Adj17_not_0_2 H1.
Qed.

Theorem tf_0_3_0 : Adj17 0 3 -> Adj17 3 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_3_1 : Adj17 0 3 -> Adj17 3 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 1. assume H3: Adj17 0 1.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_2 : Adj17 0 3 -> Adj17 3 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 2. assume H3: Adj17 0 2.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_3 : Adj17 0 3 -> Adj17 3 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 3. assume H3: Adj17 0 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_0_3_4 : Adj17 0 3 -> Adj17 3 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 4. assume H3: Adj17 0 4.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_5 : Adj17 0 3 -> Adj17 3 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 5. assume H3: Adj17 0 5.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_6 : Adj17 0 3 -> Adj17 3 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 6. assume H3: Adj17 0 6.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_7 : Adj17 0 3 -> Adj17 3 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 7. assume H3: Adj17 0 7.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_8 : Adj17 0 3 -> Adj17 3 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 8. assume H3: Adj17 0 8.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_9 : Adj17 0 3 -> Adj17 3 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 9. assume H3: Adj17 0 9.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_10 : Adj17 0 3 -> Adj17 3 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 10. assume H3: Adj17 0 10.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_11 : Adj17 0 3 -> Adj17 3 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 11. assume H3: Adj17 0 11.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_12 : Adj17 0 3 -> Adj17 3 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 12. assume H3: Adj17 0 12.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_13 : Adj17 0 3 -> Adj17 3 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 13. assume H3: Adj17 0 13.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_14 : Adj17 0 3 -> Adj17 3 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 14. assume H3: Adj17 0 14.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_15 : Adj17 0 3 -> Adj17 3 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 15. assume H3: Adj17 0 15.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_3_16 : Adj17 0 3 -> Adj17 3 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 3. assume H2: Adj17 3 16. assume H3: Adj17 0 16.
exact Adj17_not_0_3 H1.
Qed.

Theorem tf_0_4_0 : Adj17 0 4 -> Adj17 4 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_4_1 : Adj17 0 4 -> Adj17 4 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 1. assume H3: Adj17 0 1.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_2 : Adj17 0 4 -> Adj17 4 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 2. assume H3: Adj17 0 2.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_3 : Adj17 0 4 -> Adj17 4 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 3. assume H3: Adj17 0 3.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_4 : Adj17 0 4 -> Adj17 4 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 4. assume H3: Adj17 0 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_0_4_5 : Adj17 0 4 -> Adj17 4 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 5. assume H3: Adj17 0 5.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_6 : Adj17 0 4 -> Adj17 4 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 6. assume H3: Adj17 0 6.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_7 : Adj17 0 4 -> Adj17 4 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 7. assume H3: Adj17 0 7.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_8 : Adj17 0 4 -> Adj17 4 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 8. assume H3: Adj17 0 8.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_9 : Adj17 0 4 -> Adj17 4 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 9. assume H3: Adj17 0 9.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_10 : Adj17 0 4 -> Adj17 4 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 10. assume H3: Adj17 0 10.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_11 : Adj17 0 4 -> Adj17 4 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 11. assume H3: Adj17 0 11.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_12 : Adj17 0 4 -> Adj17 4 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 12. assume H3: Adj17 0 12.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_13 : Adj17 0 4 -> Adj17 4 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 13. assume H3: Adj17 0 13.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_14 : Adj17 0 4 -> Adj17 4 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 14. assume H3: Adj17 0 14.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_15 : Adj17 0 4 -> Adj17 4 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 15. assume H3: Adj17 0 15.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_4_16 : Adj17 0 4 -> Adj17 4 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 4. assume H2: Adj17 4 16. assume H3: Adj17 0 16.
exact Adj17_not_0_4 H1.
Qed.

Theorem tf_0_5_0 : Adj17 0 5 -> Adj17 5 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_5_1 : Adj17 0 5 -> Adj17 5 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 1. assume H3: Adj17 0 1.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_2 : Adj17 0 5 -> Adj17 5 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 2. assume H3: Adj17 0 2.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_3 : Adj17 0 5 -> Adj17 5 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 3. assume H3: Adj17 0 3.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_4 : Adj17 0 5 -> Adj17 5 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 4. assume H3: Adj17 0 4.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_5 : Adj17 0 5 -> Adj17 5 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 5. assume H3: Adj17 0 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_0_5_6 : Adj17 0 5 -> Adj17 5 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 6. assume H3: Adj17 0 6.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_7 : Adj17 0 5 -> Adj17 5 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 7. assume H3: Adj17 0 7.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_8 : Adj17 0 5 -> Adj17 5 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 8. assume H3: Adj17 0 8.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_9 : Adj17 0 5 -> Adj17 5 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 9. assume H3: Adj17 0 9.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_10 : Adj17 0 5 -> Adj17 5 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 10. assume H3: Adj17 0 10.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_11 : Adj17 0 5 -> Adj17 5 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 11. assume H3: Adj17 0 11.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_12 : Adj17 0 5 -> Adj17 5 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 12. assume H3: Adj17 0 12.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_13 : Adj17 0 5 -> Adj17 5 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 13. assume H3: Adj17 0 13.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_14 : Adj17 0 5 -> Adj17 5 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 14. assume H3: Adj17 0 14.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_15 : Adj17 0 5 -> Adj17 5 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 15. assume H3: Adj17 0 15.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_5_16 : Adj17 0 5 -> Adj17 5 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 5. assume H2: Adj17 5 16. assume H3: Adj17 0 16.
exact Adj17_not_0_5 H1.
Qed.

Theorem tf_0_6_0 : Adj17 0 6 -> Adj17 6 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_6_1 : Adj17 0 6 -> Adj17 6 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 1. assume H3: Adj17 0 1.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_2 : Adj17 0 6 -> Adj17 6 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 2. assume H3: Adj17 0 2.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_3 : Adj17 0 6 -> Adj17 6 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 3. assume H3: Adj17 0 3.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_4 : Adj17 0 6 -> Adj17 6 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 4. assume H3: Adj17 0 4.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_5 : Adj17 0 6 -> Adj17 6 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 5. assume H3: Adj17 0 5.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_6 : Adj17 0 6 -> Adj17 6 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 6. assume H3: Adj17 0 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_0_6_7 : Adj17 0 6 -> Adj17 6 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 7. assume H3: Adj17 0 7.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_8 : Adj17 0 6 -> Adj17 6 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 8. assume H3: Adj17 0 8.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_9 : Adj17 0 6 -> Adj17 6 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 9. assume H3: Adj17 0 9.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_10 : Adj17 0 6 -> Adj17 6 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 10. assume H3: Adj17 0 10.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_11 : Adj17 0 6 -> Adj17 6 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 11. assume H3: Adj17 0 11.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_12 : Adj17 0 6 -> Adj17 6 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 12. assume H3: Adj17 0 12.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_13 : Adj17 0 6 -> Adj17 6 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 13. assume H3: Adj17 0 13.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_14 : Adj17 0 6 -> Adj17 6 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 14. assume H3: Adj17 0 14.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_15 : Adj17 0 6 -> Adj17 6 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 15. assume H3: Adj17 0 15.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_6_16 : Adj17 0 6 -> Adj17 6 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 6. assume H2: Adj17 6 16. assume H3: Adj17 0 16.
exact Adj17_not_0_6 H1.
Qed.

Theorem tf_0_7_0 : Adj17 0 7 -> Adj17 7 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_7_1 : Adj17 0 7 -> Adj17 7 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 1. assume H3: Adj17 0 1.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_2 : Adj17 0 7 -> Adj17 7 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 2. assume H3: Adj17 0 2.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_3 : Adj17 0 7 -> Adj17 7 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 3. assume H3: Adj17 0 3.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_4 : Adj17 0 7 -> Adj17 7 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 4. assume H3: Adj17 0 4.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_5 : Adj17 0 7 -> Adj17 7 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 5. assume H3: Adj17 0 5.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_6 : Adj17 0 7 -> Adj17 7 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 6. assume H3: Adj17 0 6.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_7 : Adj17 0 7 -> Adj17 7 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 7. assume H3: Adj17 0 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_0_7_8 : Adj17 0 7 -> Adj17 7 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 8. assume H3: Adj17 0 8.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_9 : Adj17 0 7 -> Adj17 7 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 9. assume H3: Adj17 0 9.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_10 : Adj17 0 7 -> Adj17 7 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 10. assume H3: Adj17 0 10.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_11 : Adj17 0 7 -> Adj17 7 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 11. assume H3: Adj17 0 11.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_12 : Adj17 0 7 -> Adj17 7 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 12. assume H3: Adj17 0 12.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_13 : Adj17 0 7 -> Adj17 7 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 13. assume H3: Adj17 0 13.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_14 : Adj17 0 7 -> Adj17 7 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 14. assume H3: Adj17 0 14.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_15 : Adj17 0 7 -> Adj17 7 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 15. assume H3: Adj17 0 15.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_7_16 : Adj17 0 7 -> Adj17 7 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 7. assume H2: Adj17 7 16. assume H3: Adj17 0 16.
exact Adj17_not_0_7 H1.
Qed.

Theorem tf_0_8_0 : Adj17 0 8 -> Adj17 8 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_8_1 : Adj17 0 8 -> Adj17 8 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 1. assume H3: Adj17 0 1.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_2 : Adj17 0 8 -> Adj17 8 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 2. assume H3: Adj17 0 2.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_3 : Adj17 0 8 -> Adj17 8 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 3. assume H3: Adj17 0 3.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_4 : Adj17 0 8 -> Adj17 8 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 4. assume H3: Adj17 0 4.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_5 : Adj17 0 8 -> Adj17 8 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 5. assume H3: Adj17 0 5.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_6 : Adj17 0 8 -> Adj17 8 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 6. assume H3: Adj17 0 6.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_7 : Adj17 0 8 -> Adj17 8 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 7. assume H3: Adj17 0 7.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_8 : Adj17 0 8 -> Adj17 8 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 8. assume H3: Adj17 0 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_0_8_9 : Adj17 0 8 -> Adj17 8 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 9. assume H3: Adj17 0 9.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_10 : Adj17 0 8 -> Adj17 8 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 10. assume H3: Adj17 0 10.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_11 : Adj17 0 8 -> Adj17 8 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 11. assume H3: Adj17 0 11.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_12 : Adj17 0 8 -> Adj17 8 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 12. assume H3: Adj17 0 12.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_13 : Adj17 0 8 -> Adj17 8 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 13. assume H3: Adj17 0 13.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_14 : Adj17 0 8 -> Adj17 8 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 14. assume H3: Adj17 0 14.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_15 : Adj17 0 8 -> Adj17 8 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 15. assume H3: Adj17 0 15.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_8_16 : Adj17 0 8 -> Adj17 8 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 8. assume H2: Adj17 8 16. assume H3: Adj17 0 16.
exact Adj17_not_0_8 H1.
Qed.

Theorem tf_0_9_0 : Adj17 0 9 -> Adj17 9 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_9_1 : Adj17 0 9 -> Adj17 9 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 1. assume H3: Adj17 0 1.
exact Adj17_not_9_1 H2.
Qed.

Theorem tf_0_9_2 : Adj17 0 9 -> Adj17 9 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 2. assume H3: Adj17 0 2.
exact Adj17_not_9_2 H2.
Qed.

Theorem tf_0_9_3 : Adj17 0 9 -> Adj17 9 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 3. assume H3: Adj17 0 3.
exact Adj17_not_9_3 H2.
Qed.

Theorem tf_0_9_4 : Adj17 0 9 -> Adj17 9 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 4. assume H3: Adj17 0 4.
exact Adj17_not_9_4 H2.
Qed.

Theorem tf_0_9_5 : Adj17 0 9 -> Adj17 9 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 5. assume H3: Adj17 0 5.
exact Adj17_not_0_5 H3.
Qed.

Theorem tf_0_9_6 : Adj17 0 9 -> Adj17 9 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 6. assume H3: Adj17 0 6.
exact Adj17_not_9_6 H2.
Qed.

Theorem tf_0_9_7 : Adj17 0 9 -> Adj17 9 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 7. assume H3: Adj17 0 7.
exact Adj17_not_0_7 H3.
Qed.

Theorem tf_0_9_8 : Adj17 0 9 -> Adj17 9 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 8. assume H3: Adj17 0 8.
exact Adj17_not_0_8 H3.
Qed.

Theorem tf_0_9_9 : Adj17 0 9 -> Adj17 9 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 9. assume H3: Adj17 0 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_0_9_10 : Adj17 0 9 -> Adj17 9 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 10. assume H3: Adj17 0 10.
exact Adj17_not_9_10 H2.
Qed.

Theorem tf_0_9_11 : Adj17 0 9 -> Adj17 9 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 11. assume H3: Adj17 0 11.
exact Adj17_not_9_11 H2.
Qed.

Theorem tf_0_9_12 : Adj17 0 9 -> Adj17 9 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 12. assume H3: Adj17 0 12.
exact Adj17_not_0_12 H3.
Qed.

Theorem tf_0_9_13 : Adj17 0 9 -> Adj17 9 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 13. assume H3: Adj17 0 13.
exact Adj17_not_9_13 H2.
Qed.

Theorem tf_0_9_14 : Adj17 0 9 -> Adj17 9 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 14. assume H3: Adj17 0 14.
exact Adj17_not_9_14 H2.
Qed.

Theorem tf_0_9_15 : Adj17 0 9 -> Adj17 9 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 15. assume H3: Adj17 0 15.
exact Adj17_not_9_15 H2.
Qed.

Theorem tf_0_9_16 : Adj17 0 9 -> Adj17 9 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 9. assume H2: Adj17 9 16. assume H3: Adj17 0 16.
exact Adj17_not_9_16 H2.
Qed.

Theorem tf_0_10_0 : Adj17 0 10 -> Adj17 10 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_10_1 : Adj17 0 10 -> Adj17 10 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 1. assume H3: Adj17 0 1.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_2 : Adj17 0 10 -> Adj17 10 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 2. assume H3: Adj17 0 2.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_3 : Adj17 0 10 -> Adj17 10 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 3. assume H3: Adj17 0 3.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_4 : Adj17 0 10 -> Adj17 10 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 4. assume H3: Adj17 0 4.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_5 : Adj17 0 10 -> Adj17 10 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 5. assume H3: Adj17 0 5.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_6 : Adj17 0 10 -> Adj17 10 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 6. assume H3: Adj17 0 6.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_7 : Adj17 0 10 -> Adj17 10 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 7. assume H3: Adj17 0 7.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_8 : Adj17 0 10 -> Adj17 10 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 8. assume H3: Adj17 0 8.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_9 : Adj17 0 10 -> Adj17 10 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 9. assume H3: Adj17 0 9.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_10 : Adj17 0 10 -> Adj17 10 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 10. assume H3: Adj17 0 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_0_10_11 : Adj17 0 10 -> Adj17 10 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 11. assume H3: Adj17 0 11.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_12 : Adj17 0 10 -> Adj17 10 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 12. assume H3: Adj17 0 12.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_13 : Adj17 0 10 -> Adj17 10 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 13. assume H3: Adj17 0 13.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_14 : Adj17 0 10 -> Adj17 10 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 14. assume H3: Adj17 0 14.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_15 : Adj17 0 10 -> Adj17 10 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 15. assume H3: Adj17 0 15.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_10_16 : Adj17 0 10 -> Adj17 10 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 10. assume H2: Adj17 10 16. assume H3: Adj17 0 16.
exact Adj17_not_0_10 H1.
Qed.

Theorem tf_0_11_0 : Adj17 0 11 -> Adj17 11 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_11_1 : Adj17 0 11 -> Adj17 11 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 1. assume H3: Adj17 0 1.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_2 : Adj17 0 11 -> Adj17 11 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 2. assume H3: Adj17 0 2.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_3 : Adj17 0 11 -> Adj17 11 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 3. assume H3: Adj17 0 3.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_4 : Adj17 0 11 -> Adj17 11 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 4. assume H3: Adj17 0 4.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_5 : Adj17 0 11 -> Adj17 11 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 5. assume H3: Adj17 0 5.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_6 : Adj17 0 11 -> Adj17 11 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 6. assume H3: Adj17 0 6.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_7 : Adj17 0 11 -> Adj17 11 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 7. assume H3: Adj17 0 7.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_8 : Adj17 0 11 -> Adj17 11 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 8. assume H3: Adj17 0 8.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_9 : Adj17 0 11 -> Adj17 11 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 9. assume H3: Adj17 0 9.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_10 : Adj17 0 11 -> Adj17 11 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 10. assume H3: Adj17 0 10.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_11 : Adj17 0 11 -> Adj17 11 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 11. assume H3: Adj17 0 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_0_11_12 : Adj17 0 11 -> Adj17 11 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 12. assume H3: Adj17 0 12.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_13 : Adj17 0 11 -> Adj17 11 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 13. assume H3: Adj17 0 13.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_14 : Adj17 0 11 -> Adj17 11 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 14. assume H3: Adj17 0 14.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_15 : Adj17 0 11 -> Adj17 11 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 15. assume H3: Adj17 0 15.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_11_16 : Adj17 0 11 -> Adj17 11 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 11. assume H2: Adj17 11 16. assume H3: Adj17 0 16.
exact Adj17_not_0_11 H1.
Qed.

Theorem tf_0_12_0 : Adj17 0 12 -> Adj17 12 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_12_1 : Adj17 0 12 -> Adj17 12 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 1. assume H3: Adj17 0 1.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_2 : Adj17 0 12 -> Adj17 12 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 2. assume H3: Adj17 0 2.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_3 : Adj17 0 12 -> Adj17 12 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 3. assume H3: Adj17 0 3.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_4 : Adj17 0 12 -> Adj17 12 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 4. assume H3: Adj17 0 4.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_5 : Adj17 0 12 -> Adj17 12 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 5. assume H3: Adj17 0 5.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_6 : Adj17 0 12 -> Adj17 12 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 6. assume H3: Adj17 0 6.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_7 : Adj17 0 12 -> Adj17 12 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 7. assume H3: Adj17 0 7.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_8 : Adj17 0 12 -> Adj17 12 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 8. assume H3: Adj17 0 8.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_9 : Adj17 0 12 -> Adj17 12 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 9. assume H3: Adj17 0 9.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_10 : Adj17 0 12 -> Adj17 12 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 10. assume H3: Adj17 0 10.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_11 : Adj17 0 12 -> Adj17 12 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 11. assume H3: Adj17 0 11.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_12 : Adj17 0 12 -> Adj17 12 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 12. assume H3: Adj17 0 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_0_12_13 : Adj17 0 12 -> Adj17 12 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 13. assume H3: Adj17 0 13.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_14 : Adj17 0 12 -> Adj17 12 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 14. assume H3: Adj17 0 14.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_15 : Adj17 0 12 -> Adj17 12 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 15. assume H3: Adj17 0 15.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_12_16 : Adj17 0 12 -> Adj17 12 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 12. assume H2: Adj17 12 16. assume H3: Adj17 0 16.
exact Adj17_not_0_12 H1.
Qed.

Theorem tf_0_13_0 : Adj17 0 13 -> Adj17 13 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_13_1 : Adj17 0 13 -> Adj17 13 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 1. assume H3: Adj17 0 1.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_2 : Adj17 0 13 -> Adj17 13 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 2. assume H3: Adj17 0 2.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_3 : Adj17 0 13 -> Adj17 13 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 3. assume H3: Adj17 0 3.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_4 : Adj17 0 13 -> Adj17 13 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 4. assume H3: Adj17 0 4.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_5 : Adj17 0 13 -> Adj17 13 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 5. assume H3: Adj17 0 5.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_6 : Adj17 0 13 -> Adj17 13 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 6. assume H3: Adj17 0 6.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_7 : Adj17 0 13 -> Adj17 13 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 7. assume H3: Adj17 0 7.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_8 : Adj17 0 13 -> Adj17 13 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 8. assume H3: Adj17 0 8.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_9 : Adj17 0 13 -> Adj17 13 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 9. assume H3: Adj17 0 9.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_10 : Adj17 0 13 -> Adj17 13 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 10. assume H3: Adj17 0 10.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_11 : Adj17 0 13 -> Adj17 13 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 11. assume H3: Adj17 0 11.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_12 : Adj17 0 13 -> Adj17 13 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 12. assume H3: Adj17 0 12.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_13 : Adj17 0 13 -> Adj17 13 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 13. assume H3: Adj17 0 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_0_13_14 : Adj17 0 13 -> Adj17 13 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 14. assume H3: Adj17 0 14.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_15 : Adj17 0 13 -> Adj17 13 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 15. assume H3: Adj17 0 15.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_13_16 : Adj17 0 13 -> Adj17 13 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 13. assume H2: Adj17 13 16. assume H3: Adj17 0 16.
exact Adj17_not_0_13 H1.
Qed.

Theorem tf_0_14_0 : Adj17 0 14 -> Adj17 14 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_14_1 : Adj17 0 14 -> Adj17 14 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 1. assume H3: Adj17 0 1.
exact Adj17_not_14_1 H2.
Qed.

Theorem tf_0_14_2 : Adj17 0 14 -> Adj17 14 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 2. assume H3: Adj17 0 2.
exact Adj17_not_14_2 H2.
Qed.

Theorem tf_0_14_3 : Adj17 0 14 -> Adj17 14 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 3. assume H3: Adj17 0 3.
exact Adj17_not_14_3 H2.
Qed.

Theorem tf_0_14_4 : Adj17 0 14 -> Adj17 14 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 4. assume H3: Adj17 0 4.
exact Adj17_not_0_4 H3.
Qed.

Theorem tf_0_14_5 : Adj17 0 14 -> Adj17 14 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 5. assume H3: Adj17 0 5.
exact Adj17_not_14_5 H2.
Qed.

Theorem tf_0_14_6 : Adj17 0 14 -> Adj17 14 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 6. assume H3: Adj17 0 6.
exact Adj17_not_0_6 H3.
Qed.

Theorem tf_0_14_7 : Adj17 0 14 -> Adj17 14 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 7. assume H3: Adj17 0 7.
exact Adj17_not_14_7 H2.
Qed.

Theorem tf_0_14_8 : Adj17 0 14 -> Adj17 14 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 8. assume H3: Adj17 0 8.
exact Adj17_not_0_8 H3.
Qed.

Theorem tf_0_14_9 : Adj17 0 14 -> Adj17 14 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 9. assume H3: Adj17 0 9.
exact Adj17_not_14_9 H2.
Qed.

Theorem tf_0_14_10 : Adj17 0 14 -> Adj17 14 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 10. assume H3: Adj17 0 10.
exact Adj17_not_14_10 H2.
Qed.

Theorem tf_0_14_11 : Adj17 0 14 -> Adj17 14 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 11. assume H3: Adj17 0 11.
exact Adj17_not_14_11 H2.
Qed.

Theorem tf_0_14_12 : Adj17 0 14 -> Adj17 14 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 12. assume H3: Adj17 0 12.
exact Adj17_not_14_12 H2.
Qed.

Theorem tf_0_14_13 : Adj17 0 14 -> Adj17 14 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 13. assume H3: Adj17 0 13.
exact Adj17_not_0_13 H3.
Qed.

Theorem tf_0_14_14 : Adj17 0 14 -> Adj17 14 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 14. assume H3: Adj17 0 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_0_14_15 : Adj17 0 14 -> Adj17 14 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 15. assume H3: Adj17 0 15.
exact Adj17_not_14_15 H2.
Qed.

Theorem tf_0_14_16 : Adj17 0 14 -> Adj17 14 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 14. assume H2: Adj17 14 16. assume H3: Adj17 0 16.
exact Adj17_not_14_16 H2.
Qed.

Theorem tf_0_15_0 : Adj17 0 15 -> Adj17 15 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_15_1 : Adj17 0 15 -> Adj17 15 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 1. assume H3: Adj17 0 1.
exact Adj17_not_15_1 H2.
Qed.

Theorem tf_0_15_2 : Adj17 0 15 -> Adj17 15 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 2. assume H3: Adj17 0 2.
exact Adj17_not_0_2 H3.
Qed.

Theorem tf_0_15_3 : Adj17 0 15 -> Adj17 15 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 3. assume H3: Adj17 0 3.
exact Adj17_not_0_3 H3.
Qed.

Theorem tf_0_15_4 : Adj17 0 15 -> Adj17 15 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 4. assume H3: Adj17 0 4.
exact Adj17_not_15_4 H2.
Qed.

Theorem tf_0_15_5 : Adj17 0 15 -> Adj17 15 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 5. assume H3: Adj17 0 5.
exact Adj17_not_15_5 H2.
Qed.

Theorem tf_0_15_6 : Adj17 0 15 -> Adj17 15 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 6. assume H3: Adj17 0 6.
exact Adj17_not_15_6 H2.
Qed.

Theorem tf_0_15_7 : Adj17 0 15 -> Adj17 15 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 7. assume H3: Adj17 0 7.
exact Adj17_not_0_7 H3.
Qed.

Theorem tf_0_15_8 : Adj17 0 15 -> Adj17 15 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 8. assume H3: Adj17 0 8.
exact Adj17_not_15_8 H2.
Qed.

Theorem tf_0_15_9 : Adj17 0 15 -> Adj17 15 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 9. assume H3: Adj17 0 9.
exact Adj17_not_15_9 H2.
Qed.

Theorem tf_0_15_10 : Adj17 0 15 -> Adj17 15 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 10. assume H3: Adj17 0 10.
exact Adj17_not_15_10 H2.
Qed.

Theorem tf_0_15_11 : Adj17 0 15 -> Adj17 15 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 11. assume H3: Adj17 0 11.
exact Adj17_not_0_11 H3.
Qed.

Theorem tf_0_15_12 : Adj17 0 15 -> Adj17 15 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 12. assume H3: Adj17 0 12.
exact Adj17_not_15_12 H2.
Qed.

Theorem tf_0_15_13 : Adj17 0 15 -> Adj17 15 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 13. assume H3: Adj17 0 13.
exact Adj17_not_15_13 H2.
Qed.

Theorem tf_0_15_14 : Adj17 0 15 -> Adj17 15 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 14. assume H3: Adj17 0 14.
exact Adj17_not_15_14 H2.
Qed.

Theorem tf_0_15_15 : Adj17 0 15 -> Adj17 15 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 15. assume H3: Adj17 0 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_0_15_16 : Adj17 0 15 -> Adj17 15 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 15. assume H2: Adj17 15 16. assume H3: Adj17 0 16.
exact Adj17_not_15_16 H2.
Qed.

Theorem tf_0_16_0 : Adj17 0 16 -> Adj17 16 0 -> Adj17 0 0 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 0. assume H3: Adj17 0 0.
exact Adj17_not_0_0 H3.
Qed.

Theorem tf_0_16_1 : Adj17 0 16 -> Adj17 16 1 -> Adj17 0 1 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 1. assume H3: Adj17 0 1.
exact Adj17_not_0_1 H3.
Qed.

Theorem tf_0_16_2 : Adj17 0 16 -> Adj17 16 2 -> Adj17 0 2 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 2. assume H3: Adj17 0 2.
exact Adj17_not_16_2 H2.
Qed.

Theorem tf_0_16_3 : Adj17 0 16 -> Adj17 16 3 -> Adj17 0 3 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 3. assume H3: Adj17 0 3.
exact Adj17_not_0_3 H3.
Qed.

Theorem tf_0_16_4 : Adj17 0 16 -> Adj17 16 4 -> Adj17 0 4 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 4. assume H3: Adj17 0 4.
exact Adj17_not_0_4 H3.
Qed.

Theorem tf_0_16_5 : Adj17 0 16 -> Adj17 16 5 -> Adj17 0 5 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 5. assume H3: Adj17 0 5.
exact Adj17_not_16_5 H2.
Qed.

Theorem tf_0_16_6 : Adj17 0 16 -> Adj17 16 6 -> Adj17 0 6 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 6. assume H3: Adj17 0 6.
exact Adj17_not_16_6 H2.
Qed.

Theorem tf_0_16_7 : Adj17 0 16 -> Adj17 16 7 -> Adj17 0 7 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 7. assume H3: Adj17 0 7.
exact Adj17_not_16_7 H2.
Qed.

Theorem tf_0_16_8 : Adj17 0 16 -> Adj17 16 8 -> Adj17 0 8 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 8. assume H3: Adj17 0 8.
exact Adj17_not_16_8 H2.
Qed.

Theorem tf_0_16_9 : Adj17 0 16 -> Adj17 16 9 -> Adj17 0 9 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 9. assume H3: Adj17 0 9.
exact Adj17_not_16_9 H2.
Qed.

Theorem tf_0_16_10 : Adj17 0 16 -> Adj17 16 10 -> Adj17 0 10 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 10. assume H3: Adj17 0 10.
exact Adj17_not_0_10 H3.
Qed.

Theorem tf_0_16_11 : Adj17 0 16 -> Adj17 16 11 -> Adj17 0 11 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 11. assume H3: Adj17 0 11.
exact Adj17_not_16_11 H2.
Qed.

Theorem tf_0_16_12 : Adj17 0 16 -> Adj17 16 12 -> Adj17 0 12 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 12. assume H3: Adj17 0 12.
exact Adj17_not_16_12 H2.
Qed.

Theorem tf_0_16_13 : Adj17 0 16 -> Adj17 16 13 -> Adj17 0 13 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 13. assume H3: Adj17 0 13.
exact Adj17_not_16_13 H2.
Qed.

Theorem tf_0_16_14 : Adj17 0 16 -> Adj17 16 14 -> Adj17 0 14 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 14. assume H3: Adj17 0 14.
exact Adj17_not_16_14 H2.
Qed.

Theorem tf_0_16_15 : Adj17 0 16 -> Adj17 16 15 -> Adj17 0 15 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 15. assume H3: Adj17 0 15.
exact Adj17_not_16_15 H2.
Qed.

Theorem tf_0_16_16 : Adj17 0 16 -> Adj17 16 16 -> Adj17 0 16 -> False.
assume H1: Adj17 0 16. assume H2: Adj17 16 16. assume H3: Adj17 0 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_1_0_0 : Adj17 1 0 -> Adj17 0 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 0. assume H3: Adj17 1 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_1_0_1 : Adj17 1 0 -> Adj17 0 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_0_2 : Adj17 1 0 -> Adj17 0 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 2. assume H3: Adj17 1 2.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_3 : Adj17 1 0 -> Adj17 0 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 3. assume H3: Adj17 1 3.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_4 : Adj17 1 0 -> Adj17 0 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 4. assume H3: Adj17 1 4.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_5 : Adj17 1 0 -> Adj17 0 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 5. assume H3: Adj17 1 5.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_6 : Adj17 1 0 -> Adj17 0 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 6. assume H3: Adj17 1 6.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_7 : Adj17 1 0 -> Adj17 0 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 7. assume H3: Adj17 1 7.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_8 : Adj17 1 0 -> Adj17 0 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 8. assume H3: Adj17 1 8.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_9 : Adj17 1 0 -> Adj17 0 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 9. assume H3: Adj17 1 9.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_10 : Adj17 1 0 -> Adj17 0 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 10. assume H3: Adj17 1 10.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_11 : Adj17 1 0 -> Adj17 0 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 11. assume H3: Adj17 1 11.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_12 : Adj17 1 0 -> Adj17 0 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 12. assume H3: Adj17 1 12.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_13 : Adj17 1 0 -> Adj17 0 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 13. assume H3: Adj17 1 13.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_14 : Adj17 1 0 -> Adj17 0 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 14. assume H3: Adj17 1 14.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_15 : Adj17 1 0 -> Adj17 0 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 15. assume H3: Adj17 1 15.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_0_16 : Adj17 1 0 -> Adj17 0 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 0. assume H2: Adj17 0 16. assume H3: Adj17 1 16.
exact Adj17_not_1_0 H1.
Qed.

Theorem tf_1_1_0 : Adj17 1 1 -> Adj17 1 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 0. assume H3: Adj17 1 0.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_1 : Adj17 1 1 -> Adj17 1 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_2 : Adj17 1 1 -> Adj17 1 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 2. assume H3: Adj17 1 2.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_3 : Adj17 1 1 -> Adj17 1 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 3. assume H3: Adj17 1 3.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_4 : Adj17 1 1 -> Adj17 1 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 4. assume H3: Adj17 1 4.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_5 : Adj17 1 1 -> Adj17 1 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 5. assume H3: Adj17 1 5.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_6 : Adj17 1 1 -> Adj17 1 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 6. assume H3: Adj17 1 6.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_7 : Adj17 1 1 -> Adj17 1 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 7. assume H3: Adj17 1 7.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_8 : Adj17 1 1 -> Adj17 1 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 8. assume H3: Adj17 1 8.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_9 : Adj17 1 1 -> Adj17 1 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 9. assume H3: Adj17 1 9.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_10 : Adj17 1 1 -> Adj17 1 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 10. assume H3: Adj17 1 10.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_11 : Adj17 1 1 -> Adj17 1 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 11. assume H3: Adj17 1 11.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_12 : Adj17 1 1 -> Adj17 1 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 12. assume H3: Adj17 1 12.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_13 : Adj17 1 1 -> Adj17 1 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 13. assume H3: Adj17 1 13.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_14 : Adj17 1 1 -> Adj17 1 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 14. assume H3: Adj17 1 14.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_15 : Adj17 1 1 -> Adj17 1 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 15. assume H3: Adj17 1 15.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_1_16 : Adj17 1 1 -> Adj17 1 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 1. assume H2: Adj17 1 16. assume H3: Adj17 1 16.
exact Adj17_not_1_1 H1.
Qed.

Theorem tf_1_2_0 : Adj17 1 2 -> Adj17 2 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 0. assume H3: Adj17 1 0.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_1 : Adj17 1 2 -> Adj17 2 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_2_2 : Adj17 1 2 -> Adj17 2 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 2. assume H3: Adj17 1 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_1_2_3 : Adj17 1 2 -> Adj17 2 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 3. assume H3: Adj17 1 3.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_4 : Adj17 1 2 -> Adj17 2 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 4. assume H3: Adj17 1 4.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_5 : Adj17 1 2 -> Adj17 2 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 5. assume H3: Adj17 1 5.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_6 : Adj17 1 2 -> Adj17 2 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 6. assume H3: Adj17 1 6.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_7 : Adj17 1 2 -> Adj17 2 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 7. assume H3: Adj17 1 7.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_8 : Adj17 1 2 -> Adj17 2 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 8. assume H3: Adj17 1 8.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_9 : Adj17 1 2 -> Adj17 2 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 9. assume H3: Adj17 1 9.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_10 : Adj17 1 2 -> Adj17 2 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 10. assume H3: Adj17 1 10.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_11 : Adj17 1 2 -> Adj17 2 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 11. assume H3: Adj17 1 11.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_12 : Adj17 1 2 -> Adj17 2 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 12. assume H3: Adj17 1 12.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_13 : Adj17 1 2 -> Adj17 2 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 13. assume H3: Adj17 1 13.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_14 : Adj17 1 2 -> Adj17 2 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 14. assume H3: Adj17 1 14.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_15 : Adj17 1 2 -> Adj17 2 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 15. assume H3: Adj17 1 15.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_2_16 : Adj17 1 2 -> Adj17 2 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 2. assume H2: Adj17 2 16. assume H3: Adj17 1 16.
exact Adj17_not_1_2 H1.
Qed.

Theorem tf_1_3_0 : Adj17 1 3 -> Adj17 3 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 0. assume H3: Adj17 1 0.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_1 : Adj17 1 3 -> Adj17 3 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_3_2 : Adj17 1 3 -> Adj17 3 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 2. assume H3: Adj17 1 2.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_3 : Adj17 1 3 -> Adj17 3 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 3. assume H3: Adj17 1 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_1_3_4 : Adj17 1 3 -> Adj17 3 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 4. assume H3: Adj17 1 4.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_5 : Adj17 1 3 -> Adj17 3 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 5. assume H3: Adj17 1 5.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_6 : Adj17 1 3 -> Adj17 3 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 6. assume H3: Adj17 1 6.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_7 : Adj17 1 3 -> Adj17 3 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 7. assume H3: Adj17 1 7.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_8 : Adj17 1 3 -> Adj17 3 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 8. assume H3: Adj17 1 8.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_9 : Adj17 1 3 -> Adj17 3 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 9. assume H3: Adj17 1 9.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_10 : Adj17 1 3 -> Adj17 3 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 10. assume H3: Adj17 1 10.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_11 : Adj17 1 3 -> Adj17 3 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 11. assume H3: Adj17 1 11.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_12 : Adj17 1 3 -> Adj17 3 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 12. assume H3: Adj17 1 12.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_13 : Adj17 1 3 -> Adj17 3 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 13. assume H3: Adj17 1 13.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_14 : Adj17 1 3 -> Adj17 3 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 14. assume H3: Adj17 1 14.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_15 : Adj17 1 3 -> Adj17 3 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 15. assume H3: Adj17 1 15.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_3_16 : Adj17 1 3 -> Adj17 3 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 3. assume H2: Adj17 3 16. assume H3: Adj17 1 16.
exact Adj17_not_1_3 H1.
Qed.

Theorem tf_1_4_0 : Adj17 1 4 -> Adj17 4 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 0. assume H3: Adj17 1 0.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_1 : Adj17 1 4 -> Adj17 4 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_4_2 : Adj17 1 4 -> Adj17 4 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 2. assume H3: Adj17 1 2.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_3 : Adj17 1 4 -> Adj17 4 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 3. assume H3: Adj17 1 3.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_4 : Adj17 1 4 -> Adj17 4 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 4. assume H3: Adj17 1 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_1_4_5 : Adj17 1 4 -> Adj17 4 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 5. assume H3: Adj17 1 5.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_6 : Adj17 1 4 -> Adj17 4 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 6. assume H3: Adj17 1 6.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_7 : Adj17 1 4 -> Adj17 4 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 7. assume H3: Adj17 1 7.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_8 : Adj17 1 4 -> Adj17 4 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 8. assume H3: Adj17 1 8.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_9 : Adj17 1 4 -> Adj17 4 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 9. assume H3: Adj17 1 9.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_10 : Adj17 1 4 -> Adj17 4 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 10. assume H3: Adj17 1 10.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_11 : Adj17 1 4 -> Adj17 4 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 11. assume H3: Adj17 1 11.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_12 : Adj17 1 4 -> Adj17 4 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 12. assume H3: Adj17 1 12.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_13 : Adj17 1 4 -> Adj17 4 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 13. assume H3: Adj17 1 13.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_14 : Adj17 1 4 -> Adj17 4 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 14. assume H3: Adj17 1 14.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_15 : Adj17 1 4 -> Adj17 4 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 15. assume H3: Adj17 1 15.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_4_16 : Adj17 1 4 -> Adj17 4 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 4. assume H2: Adj17 4 16. assume H3: Adj17 1 16.
exact Adj17_not_1_4 H1.
Qed.

Theorem tf_1_5_0 : Adj17 1 5 -> Adj17 5 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 0. assume H3: Adj17 1 0.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_1 : Adj17 1 5 -> Adj17 5 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_5_2 : Adj17 1 5 -> Adj17 5 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 2. assume H3: Adj17 1 2.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_3 : Adj17 1 5 -> Adj17 5 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 3. assume H3: Adj17 1 3.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_4 : Adj17 1 5 -> Adj17 5 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 4. assume H3: Adj17 1 4.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_5 : Adj17 1 5 -> Adj17 5 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 5. assume H3: Adj17 1 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_1_5_6 : Adj17 1 5 -> Adj17 5 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 6. assume H3: Adj17 1 6.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_7 : Adj17 1 5 -> Adj17 5 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 7. assume H3: Adj17 1 7.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_8 : Adj17 1 5 -> Adj17 5 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 8. assume H3: Adj17 1 8.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_9 : Adj17 1 5 -> Adj17 5 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 9. assume H3: Adj17 1 9.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_10 : Adj17 1 5 -> Adj17 5 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 10. assume H3: Adj17 1 10.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_11 : Adj17 1 5 -> Adj17 5 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 11. assume H3: Adj17 1 11.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_12 : Adj17 1 5 -> Adj17 5 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 12. assume H3: Adj17 1 12.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_13 : Adj17 1 5 -> Adj17 5 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 13. assume H3: Adj17 1 13.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_14 : Adj17 1 5 -> Adj17 5 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 14. assume H3: Adj17 1 14.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_15 : Adj17 1 5 -> Adj17 5 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 15. assume H3: Adj17 1 15.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_5_16 : Adj17 1 5 -> Adj17 5 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 5. assume H2: Adj17 5 16. assume H3: Adj17 1 16.
exact Adj17_not_1_5 H1.
Qed.

Theorem tf_1_6_0 : Adj17 1 6 -> Adj17 6 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 0. assume H3: Adj17 1 0.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_1 : Adj17 1 6 -> Adj17 6 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_6_2 : Adj17 1 6 -> Adj17 6 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 2. assume H3: Adj17 1 2.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_3 : Adj17 1 6 -> Adj17 6 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 3. assume H3: Adj17 1 3.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_4 : Adj17 1 6 -> Adj17 6 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 4. assume H3: Adj17 1 4.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_5 : Adj17 1 6 -> Adj17 6 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 5. assume H3: Adj17 1 5.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_6 : Adj17 1 6 -> Adj17 6 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 6. assume H3: Adj17 1 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_1_6_7 : Adj17 1 6 -> Adj17 6 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 7. assume H3: Adj17 1 7.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_8 : Adj17 1 6 -> Adj17 6 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 8. assume H3: Adj17 1 8.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_9 : Adj17 1 6 -> Adj17 6 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 9. assume H3: Adj17 1 9.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_10 : Adj17 1 6 -> Adj17 6 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 10. assume H3: Adj17 1 10.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_11 : Adj17 1 6 -> Adj17 6 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 11. assume H3: Adj17 1 11.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_12 : Adj17 1 6 -> Adj17 6 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 12. assume H3: Adj17 1 12.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_13 : Adj17 1 6 -> Adj17 6 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 13. assume H3: Adj17 1 13.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_14 : Adj17 1 6 -> Adj17 6 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 14. assume H3: Adj17 1 14.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_15 : Adj17 1 6 -> Adj17 6 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 15. assume H3: Adj17 1 15.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_6_16 : Adj17 1 6 -> Adj17 6 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 6. assume H2: Adj17 6 16. assume H3: Adj17 1 16.
exact Adj17_not_1_6 H1.
Qed.

Theorem tf_1_7_0 : Adj17 1 7 -> Adj17 7 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 0. assume H3: Adj17 1 0.
exact Adj17_not_7_0 H2.
Qed.

Theorem tf_1_7_1 : Adj17 1 7 -> Adj17 7 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_7_2 : Adj17 1 7 -> Adj17 7 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 2. assume H3: Adj17 1 2.
exact Adj17_not_7_2 H2.
Qed.

Theorem tf_1_7_3 : Adj17 1 7 -> Adj17 7 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 3. assume H3: Adj17 1 3.
exact Adj17_not_7_3 H2.
Qed.

Theorem tf_1_7_4 : Adj17 1 7 -> Adj17 7 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 4. assume H3: Adj17 1 4.
exact Adj17_not_1_4 H3.
Qed.

Theorem tf_1_7_5 : Adj17 1 7 -> Adj17 7 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 5. assume H3: Adj17 1 5.
exact Adj17_not_7_5 H2.
Qed.

Theorem tf_1_7_6 : Adj17 1 7 -> Adj17 7 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 6. assume H3: Adj17 1 6.
exact Adj17_not_7_6 H2.
Qed.

Theorem tf_1_7_7 : Adj17 1 7 -> Adj17 7 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 7. assume H3: Adj17 1 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_1_7_8 : Adj17 1 7 -> Adj17 7 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 8. assume H3: Adj17 1 8.
exact Adj17_not_7_8 H2.
Qed.

Theorem tf_1_7_9 : Adj17 1 7 -> Adj17 7 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 9. assume H3: Adj17 1 9.
exact Adj17_not_1_9 H3.
Qed.

Theorem tf_1_7_10 : Adj17 1 7 -> Adj17 7 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 10. assume H3: Adj17 1 10.
exact Adj17_not_1_10 H3.
Qed.

Theorem tf_1_7_11 : Adj17 1 7 -> Adj17 7 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 11. assume H3: Adj17 1 11.
exact Adj17_not_7_11 H2.
Qed.

Theorem tf_1_7_12 : Adj17 1 7 -> Adj17 7 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 12. assume H3: Adj17 1 12.
exact Adj17_not_7_12 H2.
Qed.

Theorem tf_1_7_13 : Adj17 1 7 -> Adj17 7 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 13. assume H3: Adj17 1 13.
exact Adj17_not_7_13 H2.
Qed.

Theorem tf_1_7_14 : Adj17 1 7 -> Adj17 7 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 14. assume H3: Adj17 1 14.
exact Adj17_not_7_14 H2.
Qed.

Theorem tf_1_7_15 : Adj17 1 7 -> Adj17 7 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 15. assume H3: Adj17 1 15.
exact Adj17_not_1_15 H3.
Qed.

Theorem tf_1_7_16 : Adj17 1 7 -> Adj17 7 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 7. assume H2: Adj17 7 16. assume H3: Adj17 1 16.
exact Adj17_not_7_16 H2.
Qed.

Theorem tf_1_8_0 : Adj17 1 8 -> Adj17 8 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 0. assume H3: Adj17 1 0.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_1 : Adj17 1 8 -> Adj17 8 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_8_2 : Adj17 1 8 -> Adj17 8 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 2. assume H3: Adj17 1 2.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_3 : Adj17 1 8 -> Adj17 8 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 3. assume H3: Adj17 1 3.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_4 : Adj17 1 8 -> Adj17 8 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 4. assume H3: Adj17 1 4.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_5 : Adj17 1 8 -> Adj17 8 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 5. assume H3: Adj17 1 5.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_6 : Adj17 1 8 -> Adj17 8 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 6. assume H3: Adj17 1 6.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_7 : Adj17 1 8 -> Adj17 8 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 7. assume H3: Adj17 1 7.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_8 : Adj17 1 8 -> Adj17 8 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 8. assume H3: Adj17 1 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_1_8_9 : Adj17 1 8 -> Adj17 8 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 9. assume H3: Adj17 1 9.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_10 : Adj17 1 8 -> Adj17 8 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 10. assume H3: Adj17 1 10.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_11 : Adj17 1 8 -> Adj17 8 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 11. assume H3: Adj17 1 11.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_12 : Adj17 1 8 -> Adj17 8 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 12. assume H3: Adj17 1 12.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_13 : Adj17 1 8 -> Adj17 8 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 13. assume H3: Adj17 1 13.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_14 : Adj17 1 8 -> Adj17 8 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 14. assume H3: Adj17 1 14.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_15 : Adj17 1 8 -> Adj17 8 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 15. assume H3: Adj17 1 15.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_8_16 : Adj17 1 8 -> Adj17 8 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 8. assume H2: Adj17 8 16. assume H3: Adj17 1 16.
exact Adj17_not_1_8 H1.
Qed.

Theorem tf_1_9_0 : Adj17 1 9 -> Adj17 9 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 0. assume H3: Adj17 1 0.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_1 : Adj17 1 9 -> Adj17 9 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_9_2 : Adj17 1 9 -> Adj17 9 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 2. assume H3: Adj17 1 2.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_3 : Adj17 1 9 -> Adj17 9 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 3. assume H3: Adj17 1 3.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_4 : Adj17 1 9 -> Adj17 9 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 4. assume H3: Adj17 1 4.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_5 : Adj17 1 9 -> Adj17 9 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 5. assume H3: Adj17 1 5.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_6 : Adj17 1 9 -> Adj17 9 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 6. assume H3: Adj17 1 6.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_7 : Adj17 1 9 -> Adj17 9 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 7. assume H3: Adj17 1 7.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_8 : Adj17 1 9 -> Adj17 9 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 8. assume H3: Adj17 1 8.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_9 : Adj17 1 9 -> Adj17 9 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 9. assume H3: Adj17 1 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_1_9_10 : Adj17 1 9 -> Adj17 9 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 10. assume H3: Adj17 1 10.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_11 : Adj17 1 9 -> Adj17 9 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 11. assume H3: Adj17 1 11.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_12 : Adj17 1 9 -> Adj17 9 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 12. assume H3: Adj17 1 12.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_13 : Adj17 1 9 -> Adj17 9 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 13. assume H3: Adj17 1 13.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_14 : Adj17 1 9 -> Adj17 9 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 14. assume H3: Adj17 1 14.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_15 : Adj17 1 9 -> Adj17 9 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 15. assume H3: Adj17 1 15.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_9_16 : Adj17 1 9 -> Adj17 9 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 9. assume H2: Adj17 9 16. assume H3: Adj17 1 16.
exact Adj17_not_1_9 H1.
Qed.

Theorem tf_1_10_0 : Adj17 1 10 -> Adj17 10 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 0. assume H3: Adj17 1 0.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_1 : Adj17 1 10 -> Adj17 10 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_10_2 : Adj17 1 10 -> Adj17 10 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 2. assume H3: Adj17 1 2.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_3 : Adj17 1 10 -> Adj17 10 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 3. assume H3: Adj17 1 3.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_4 : Adj17 1 10 -> Adj17 10 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 4. assume H3: Adj17 1 4.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_5 : Adj17 1 10 -> Adj17 10 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 5. assume H3: Adj17 1 5.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_6 : Adj17 1 10 -> Adj17 10 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 6. assume H3: Adj17 1 6.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_7 : Adj17 1 10 -> Adj17 10 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 7. assume H3: Adj17 1 7.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_8 : Adj17 1 10 -> Adj17 10 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 8. assume H3: Adj17 1 8.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_9 : Adj17 1 10 -> Adj17 10 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 9. assume H3: Adj17 1 9.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_10 : Adj17 1 10 -> Adj17 10 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 10. assume H3: Adj17 1 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_1_10_11 : Adj17 1 10 -> Adj17 10 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 11. assume H3: Adj17 1 11.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_12 : Adj17 1 10 -> Adj17 10 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 12. assume H3: Adj17 1 12.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_13 : Adj17 1 10 -> Adj17 10 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 13. assume H3: Adj17 1 13.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_14 : Adj17 1 10 -> Adj17 10 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 14. assume H3: Adj17 1 14.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_15 : Adj17 1 10 -> Adj17 10 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 15. assume H3: Adj17 1 15.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_10_16 : Adj17 1 10 -> Adj17 10 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 10. assume H2: Adj17 10 16. assume H3: Adj17 1 16.
exact Adj17_not_1_10 H1.
Qed.

Theorem tf_1_11_0 : Adj17 1 11 -> Adj17 11 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 0. assume H3: Adj17 1 0.
exact Adj17_not_11_0 H2.
Qed.

Theorem tf_1_11_1 : Adj17 1 11 -> Adj17 11 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_11_2 : Adj17 1 11 -> Adj17 11 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 2. assume H3: Adj17 1 2.
exact Adj17_not_11_2 H2.
Qed.

Theorem tf_1_11_3 : Adj17 1 11 -> Adj17 11 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 3. assume H3: Adj17 1 3.
exact Adj17_not_11_3 H2.
Qed.

Theorem tf_1_11_4 : Adj17 1 11 -> Adj17 11 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 4. assume H3: Adj17 1 4.
exact Adj17_not_11_4 H2.
Qed.

Theorem tf_1_11_5 : Adj17 1 11 -> Adj17 11 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 5. assume H3: Adj17 1 5.
exact Adj17_not_1_5 H3.
Qed.

Theorem tf_1_11_6 : Adj17 1 11 -> Adj17 11 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 6. assume H3: Adj17 1 6.
exact Adj17_not_1_6 H3.
Qed.

Theorem tf_1_11_7 : Adj17 1 11 -> Adj17 11 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 7. assume H3: Adj17 1 7.
exact Adj17_not_11_7 H2.
Qed.

Theorem tf_1_11_8 : Adj17 1 11 -> Adj17 11 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 8. assume H3: Adj17 1 8.
exact Adj17_not_1_8 H3.
Qed.

Theorem tf_1_11_9 : Adj17 1 11 -> Adj17 11 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 9. assume H3: Adj17 1 9.
exact Adj17_not_11_9 H2.
Qed.

Theorem tf_1_11_10 : Adj17 1 11 -> Adj17 11 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 10. assume H3: Adj17 1 10.
exact Adj17_not_11_10 H2.
Qed.

Theorem tf_1_11_11 : Adj17 1 11 -> Adj17 11 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 11. assume H3: Adj17 1 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_1_11_12 : Adj17 1 11 -> Adj17 11 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 12. assume H3: Adj17 1 12.
exact Adj17_not_11_12 H2.
Qed.

Theorem tf_1_11_13 : Adj17 1 11 -> Adj17 11 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 13. assume H3: Adj17 1 13.
exact Adj17_not_11_13 H2.
Qed.

Theorem tf_1_11_14 : Adj17 1 11 -> Adj17 11 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 14. assume H3: Adj17 1 14.
exact Adj17_not_11_14 H2.
Qed.

Theorem tf_1_11_15 : Adj17 1 11 -> Adj17 11 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 15. assume H3: Adj17 1 15.
exact Adj17_not_1_15 H3.
Qed.

Theorem tf_1_11_16 : Adj17 1 11 -> Adj17 11 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 11. assume H2: Adj17 11 16. assume H3: Adj17 1 16.
exact Adj17_not_11_16 H2.
Qed.

Theorem tf_1_12_0 : Adj17 1 12 -> Adj17 12 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 0. assume H3: Adj17 1 0.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_1 : Adj17 1 12 -> Adj17 12 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_12_2 : Adj17 1 12 -> Adj17 12 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 2. assume H3: Adj17 1 2.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_3 : Adj17 1 12 -> Adj17 12 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 3. assume H3: Adj17 1 3.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_4 : Adj17 1 12 -> Adj17 12 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 4. assume H3: Adj17 1 4.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_5 : Adj17 1 12 -> Adj17 12 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 5. assume H3: Adj17 1 5.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_6 : Adj17 1 12 -> Adj17 12 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 6. assume H3: Adj17 1 6.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_7 : Adj17 1 12 -> Adj17 12 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 7. assume H3: Adj17 1 7.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_8 : Adj17 1 12 -> Adj17 12 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 8. assume H3: Adj17 1 8.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_9 : Adj17 1 12 -> Adj17 12 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 9. assume H3: Adj17 1 9.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_10 : Adj17 1 12 -> Adj17 12 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 10. assume H3: Adj17 1 10.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_11 : Adj17 1 12 -> Adj17 12 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 11. assume H3: Adj17 1 11.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_12 : Adj17 1 12 -> Adj17 12 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 12. assume H3: Adj17 1 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_1_12_13 : Adj17 1 12 -> Adj17 12 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 13. assume H3: Adj17 1 13.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_14 : Adj17 1 12 -> Adj17 12 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 14. assume H3: Adj17 1 14.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_15 : Adj17 1 12 -> Adj17 12 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 15. assume H3: Adj17 1 15.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_12_16 : Adj17 1 12 -> Adj17 12 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 12. assume H2: Adj17 12 16. assume H3: Adj17 1 16.
exact Adj17_not_1_12 H1.
Qed.

Theorem tf_1_13_0 : Adj17 1 13 -> Adj17 13 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 0. assume H3: Adj17 1 0.
exact Adj17_not_13_0 H2.
Qed.

Theorem tf_1_13_1 : Adj17 1 13 -> Adj17 13 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_13_2 : Adj17 1 13 -> Adj17 13 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 2. assume H3: Adj17 1 2.
exact Adj17_not_13_2 H2.
Qed.

Theorem tf_1_13_3 : Adj17 1 13 -> Adj17 13 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 3. assume H3: Adj17 1 3.
exact Adj17_not_1_3 H3.
Qed.

Theorem tf_1_13_4 : Adj17 1 13 -> Adj17 13 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 4. assume H3: Adj17 1 4.
exact Adj17_not_13_4 H2.
Qed.

Theorem tf_1_13_5 : Adj17 1 13 -> Adj17 13 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 5. assume H3: Adj17 1 5.
exact Adj17_not_1_5 H3.
Qed.

Theorem tf_1_13_6 : Adj17 1 13 -> Adj17 13 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 6. assume H3: Adj17 1 6.
exact Adj17_not_13_6 H2.
Qed.

Theorem tf_1_13_7 : Adj17 1 13 -> Adj17 13 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 7. assume H3: Adj17 1 7.
exact Adj17_not_13_7 H2.
Qed.

Theorem tf_1_13_8 : Adj17 1 13 -> Adj17 13 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 8. assume H3: Adj17 1 8.
exact Adj17_not_13_8 H2.
Qed.

Theorem tf_1_13_9 : Adj17 1 13 -> Adj17 13 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 9. assume H3: Adj17 1 9.
exact Adj17_not_13_9 H2.
Qed.

Theorem tf_1_13_10 : Adj17 1 13 -> Adj17 13 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 10. assume H3: Adj17 1 10.
exact Adj17_not_13_10 H2.
Qed.

Theorem tf_1_13_11 : Adj17 1 13 -> Adj17 13 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 11. assume H3: Adj17 1 11.
exact Adj17_not_13_11 H2.
Qed.

Theorem tf_1_13_12 : Adj17 1 13 -> Adj17 13 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 12. assume H3: Adj17 1 12.
exact Adj17_not_1_12 H3.
Qed.

Theorem tf_1_13_13 : Adj17 1 13 -> Adj17 13 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 13. assume H3: Adj17 1 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_1_13_14 : Adj17 1 13 -> Adj17 13 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 14. assume H3: Adj17 1 14.
exact Adj17_not_1_14 H3.
Qed.

Theorem tf_1_13_15 : Adj17 1 13 -> Adj17 13 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 15. assume H3: Adj17 1 15.
exact Adj17_not_13_15 H2.
Qed.

Theorem tf_1_13_16 : Adj17 1 13 -> Adj17 13 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 13. assume H2: Adj17 13 16. assume H3: Adj17 1 16.
exact Adj17_not_13_16 H2.
Qed.

Theorem tf_1_14_0 : Adj17 1 14 -> Adj17 14 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 0. assume H3: Adj17 1 0.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_1 : Adj17 1 14 -> Adj17 14 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_14_2 : Adj17 1 14 -> Adj17 14 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 2. assume H3: Adj17 1 2.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_3 : Adj17 1 14 -> Adj17 14 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 3. assume H3: Adj17 1 3.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_4 : Adj17 1 14 -> Adj17 14 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 4. assume H3: Adj17 1 4.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_5 : Adj17 1 14 -> Adj17 14 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 5. assume H3: Adj17 1 5.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_6 : Adj17 1 14 -> Adj17 14 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 6. assume H3: Adj17 1 6.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_7 : Adj17 1 14 -> Adj17 14 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 7. assume H3: Adj17 1 7.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_8 : Adj17 1 14 -> Adj17 14 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 8. assume H3: Adj17 1 8.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_9 : Adj17 1 14 -> Adj17 14 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 9. assume H3: Adj17 1 9.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_10 : Adj17 1 14 -> Adj17 14 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 10. assume H3: Adj17 1 10.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_11 : Adj17 1 14 -> Adj17 14 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 11. assume H3: Adj17 1 11.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_12 : Adj17 1 14 -> Adj17 14 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 12. assume H3: Adj17 1 12.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_13 : Adj17 1 14 -> Adj17 14 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 13. assume H3: Adj17 1 13.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_14 : Adj17 1 14 -> Adj17 14 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 14. assume H3: Adj17 1 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_1_14_15 : Adj17 1 14 -> Adj17 14 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 15. assume H3: Adj17 1 15.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_14_16 : Adj17 1 14 -> Adj17 14 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 14. assume H2: Adj17 14 16. assume H3: Adj17 1 16.
exact Adj17_not_1_14 H1.
Qed.

Theorem tf_1_15_0 : Adj17 1 15 -> Adj17 15 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 0. assume H3: Adj17 1 0.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_1 : Adj17 1 15 -> Adj17 15 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_15_2 : Adj17 1 15 -> Adj17 15 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 2. assume H3: Adj17 1 2.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_3 : Adj17 1 15 -> Adj17 15 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 3. assume H3: Adj17 1 3.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_4 : Adj17 1 15 -> Adj17 15 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 4. assume H3: Adj17 1 4.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_5 : Adj17 1 15 -> Adj17 15 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 5. assume H3: Adj17 1 5.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_6 : Adj17 1 15 -> Adj17 15 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 6. assume H3: Adj17 1 6.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_7 : Adj17 1 15 -> Adj17 15 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 7. assume H3: Adj17 1 7.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_8 : Adj17 1 15 -> Adj17 15 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 8. assume H3: Adj17 1 8.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_9 : Adj17 1 15 -> Adj17 15 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 9. assume H3: Adj17 1 9.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_10 : Adj17 1 15 -> Adj17 15 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 10. assume H3: Adj17 1 10.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_11 : Adj17 1 15 -> Adj17 15 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 11. assume H3: Adj17 1 11.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_12 : Adj17 1 15 -> Adj17 15 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 12. assume H3: Adj17 1 12.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_13 : Adj17 1 15 -> Adj17 15 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 13. assume H3: Adj17 1 13.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_14 : Adj17 1 15 -> Adj17 15 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 14. assume H3: Adj17 1 14.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_15_15 : Adj17 1 15 -> Adj17 15 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 15. assume H3: Adj17 1 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_1_15_16 : Adj17 1 15 -> Adj17 15 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 15. assume H2: Adj17 15 16. assume H3: Adj17 1 16.
exact Adj17_not_1_15 H1.
Qed.

Theorem tf_1_16_0 : Adj17 1 16 -> Adj17 16 0 -> Adj17 1 0 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 0. assume H3: Adj17 1 0.
exact Adj17_not_1_0 H3.
Qed.

Theorem tf_1_16_1 : Adj17 1 16 -> Adj17 16 1 -> Adj17 1 1 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 1. assume H3: Adj17 1 1.
exact Adj17_not_1_1 H3.
Qed.

Theorem tf_1_16_2 : Adj17 1 16 -> Adj17 16 2 -> Adj17 1 2 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 2. assume H3: Adj17 1 2.
exact Adj17_not_16_2 H2.
Qed.

Theorem tf_1_16_3 : Adj17 1 16 -> Adj17 16 3 -> Adj17 1 3 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 3. assume H3: Adj17 1 3.
exact Adj17_not_1_3 H3.
Qed.

Theorem tf_1_16_4 : Adj17 1 16 -> Adj17 16 4 -> Adj17 1 4 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 4. assume H3: Adj17 1 4.
exact Adj17_not_1_4 H3.
Qed.

Theorem tf_1_16_5 : Adj17 1 16 -> Adj17 16 5 -> Adj17 1 5 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 5. assume H3: Adj17 1 5.
exact Adj17_not_16_5 H2.
Qed.

Theorem tf_1_16_6 : Adj17 1 16 -> Adj17 16 6 -> Adj17 1 6 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 6. assume H3: Adj17 1 6.
exact Adj17_not_16_6 H2.
Qed.

Theorem tf_1_16_7 : Adj17 1 16 -> Adj17 16 7 -> Adj17 1 7 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 7. assume H3: Adj17 1 7.
exact Adj17_not_16_7 H2.
Qed.

Theorem tf_1_16_8 : Adj17 1 16 -> Adj17 16 8 -> Adj17 1 8 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 8. assume H3: Adj17 1 8.
exact Adj17_not_16_8 H2.
Qed.

Theorem tf_1_16_9 : Adj17 1 16 -> Adj17 16 9 -> Adj17 1 9 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 9. assume H3: Adj17 1 9.
exact Adj17_not_16_9 H2.
Qed.

Theorem tf_1_16_10 : Adj17 1 16 -> Adj17 16 10 -> Adj17 1 10 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 10. assume H3: Adj17 1 10.
exact Adj17_not_1_10 H3.
Qed.

Theorem tf_1_16_11 : Adj17 1 16 -> Adj17 16 11 -> Adj17 1 11 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 11. assume H3: Adj17 1 11.
exact Adj17_not_16_11 H2.
Qed.

Theorem tf_1_16_12 : Adj17 1 16 -> Adj17 16 12 -> Adj17 1 12 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 12. assume H3: Adj17 1 12.
exact Adj17_not_16_12 H2.
Qed.

Theorem tf_1_16_13 : Adj17 1 16 -> Adj17 16 13 -> Adj17 1 13 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 13. assume H3: Adj17 1 13.
exact Adj17_not_16_13 H2.
Qed.

Theorem tf_1_16_14 : Adj17 1 16 -> Adj17 16 14 -> Adj17 1 14 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 14. assume H3: Adj17 1 14.
exact Adj17_not_16_14 H2.
Qed.

Theorem tf_1_16_15 : Adj17 1 16 -> Adj17 16 15 -> Adj17 1 15 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 15. assume H3: Adj17 1 15.
exact Adj17_not_16_15 H2.
Qed.

Theorem tf_1_16_16 : Adj17 1 16 -> Adj17 16 16 -> Adj17 1 16 -> False.
assume H1: Adj17 1 16. assume H2: Adj17 16 16. assume H3: Adj17 1 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_2_0_0 : Adj17 2 0 -> Adj17 0 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 0. assume H3: Adj17 2 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_2_0_1 : Adj17 2 0 -> Adj17 0 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 1. assume H3: Adj17 2 1.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_2 : Adj17 2 0 -> Adj17 0 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_0_3 : Adj17 2 0 -> Adj17 0 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 3. assume H3: Adj17 2 3.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_4 : Adj17 2 0 -> Adj17 0 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 4. assume H3: Adj17 2 4.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_5 : Adj17 2 0 -> Adj17 0 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 5. assume H3: Adj17 2 5.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_6 : Adj17 2 0 -> Adj17 0 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 6. assume H3: Adj17 2 6.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_7 : Adj17 2 0 -> Adj17 0 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 7. assume H3: Adj17 2 7.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_8 : Adj17 2 0 -> Adj17 0 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 8. assume H3: Adj17 2 8.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_9 : Adj17 2 0 -> Adj17 0 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 9. assume H3: Adj17 2 9.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_10 : Adj17 2 0 -> Adj17 0 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 10. assume H3: Adj17 2 10.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_11 : Adj17 2 0 -> Adj17 0 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 11. assume H3: Adj17 2 11.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_12 : Adj17 2 0 -> Adj17 0 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 12. assume H3: Adj17 2 12.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_13 : Adj17 2 0 -> Adj17 0 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 13. assume H3: Adj17 2 13.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_14 : Adj17 2 0 -> Adj17 0 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 14. assume H3: Adj17 2 14.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_15 : Adj17 2 0 -> Adj17 0 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 15. assume H3: Adj17 2 15.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_0_16 : Adj17 2 0 -> Adj17 0 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 0. assume H2: Adj17 0 16. assume H3: Adj17 2 16.
exact Adj17_not_2_0 H1.
Qed.

Theorem tf_2_1_0 : Adj17 2 1 -> Adj17 1 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 0. assume H3: Adj17 2 0.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_1 : Adj17 2 1 -> Adj17 1 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 1. assume H3: Adj17 2 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_2_1_2 : Adj17 2 1 -> Adj17 1 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_1_3 : Adj17 2 1 -> Adj17 1 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 3. assume H3: Adj17 2 3.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_4 : Adj17 2 1 -> Adj17 1 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 4. assume H3: Adj17 2 4.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_5 : Adj17 2 1 -> Adj17 1 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 5. assume H3: Adj17 2 5.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_6 : Adj17 2 1 -> Adj17 1 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 6. assume H3: Adj17 2 6.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_7 : Adj17 2 1 -> Adj17 1 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 7. assume H3: Adj17 2 7.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_8 : Adj17 2 1 -> Adj17 1 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 8. assume H3: Adj17 2 8.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_9 : Adj17 2 1 -> Adj17 1 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 9. assume H3: Adj17 2 9.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_10 : Adj17 2 1 -> Adj17 1 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 10. assume H3: Adj17 2 10.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_11 : Adj17 2 1 -> Adj17 1 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 11. assume H3: Adj17 2 11.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_12 : Adj17 2 1 -> Adj17 1 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 12. assume H3: Adj17 2 12.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_13 : Adj17 2 1 -> Adj17 1 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 13. assume H3: Adj17 2 13.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_14 : Adj17 2 1 -> Adj17 1 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 14. assume H3: Adj17 2 14.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_15 : Adj17 2 1 -> Adj17 1 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 15. assume H3: Adj17 2 15.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_1_16 : Adj17 2 1 -> Adj17 1 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 1. assume H2: Adj17 1 16. assume H3: Adj17 2 16.
exact Adj17_not_2_1 H1.
Qed.

Theorem tf_2_2_0 : Adj17 2 2 -> Adj17 2 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 0. assume H3: Adj17 2 0.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_1 : Adj17 2 2 -> Adj17 2 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 1. assume H3: Adj17 2 1.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_2 : Adj17 2 2 -> Adj17 2 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_3 : Adj17 2 2 -> Adj17 2 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 3. assume H3: Adj17 2 3.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_4 : Adj17 2 2 -> Adj17 2 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 4. assume H3: Adj17 2 4.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_5 : Adj17 2 2 -> Adj17 2 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 5. assume H3: Adj17 2 5.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_6 : Adj17 2 2 -> Adj17 2 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 6. assume H3: Adj17 2 6.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_7 : Adj17 2 2 -> Adj17 2 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 7. assume H3: Adj17 2 7.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_8 : Adj17 2 2 -> Adj17 2 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 8. assume H3: Adj17 2 8.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_9 : Adj17 2 2 -> Adj17 2 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 9. assume H3: Adj17 2 9.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_10 : Adj17 2 2 -> Adj17 2 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 10. assume H3: Adj17 2 10.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_11 : Adj17 2 2 -> Adj17 2 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 11. assume H3: Adj17 2 11.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_12 : Adj17 2 2 -> Adj17 2 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 12. assume H3: Adj17 2 12.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_13 : Adj17 2 2 -> Adj17 2 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 13. assume H3: Adj17 2 13.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_14 : Adj17 2 2 -> Adj17 2 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 14. assume H3: Adj17 2 14.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_15 : Adj17 2 2 -> Adj17 2 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 15. assume H3: Adj17 2 15.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_2_16 : Adj17 2 2 -> Adj17 2 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 2. assume H2: Adj17 2 16. assume H3: Adj17 2 16.
exact Adj17_not_2_2 H1.
Qed.

Theorem tf_2_3_0 : Adj17 2 3 -> Adj17 3 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 0. assume H3: Adj17 2 0.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_1 : Adj17 2 3 -> Adj17 3 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 1. assume H3: Adj17 2 1.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_2 : Adj17 2 3 -> Adj17 3 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_3_3 : Adj17 2 3 -> Adj17 3 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 3. assume H3: Adj17 2 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_2_3_4 : Adj17 2 3 -> Adj17 3 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 4. assume H3: Adj17 2 4.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_5 : Adj17 2 3 -> Adj17 3 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 5. assume H3: Adj17 2 5.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_6 : Adj17 2 3 -> Adj17 3 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 6. assume H3: Adj17 2 6.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_7 : Adj17 2 3 -> Adj17 3 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 7. assume H3: Adj17 2 7.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_8 : Adj17 2 3 -> Adj17 3 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 8. assume H3: Adj17 2 8.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_9 : Adj17 2 3 -> Adj17 3 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 9. assume H3: Adj17 2 9.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_10 : Adj17 2 3 -> Adj17 3 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 10. assume H3: Adj17 2 10.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_11 : Adj17 2 3 -> Adj17 3 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 11. assume H3: Adj17 2 11.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_12 : Adj17 2 3 -> Adj17 3 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 12. assume H3: Adj17 2 12.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_13 : Adj17 2 3 -> Adj17 3 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 13. assume H3: Adj17 2 13.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_14 : Adj17 2 3 -> Adj17 3 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 14. assume H3: Adj17 2 14.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_15 : Adj17 2 3 -> Adj17 3 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 15. assume H3: Adj17 2 15.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_3_16 : Adj17 2 3 -> Adj17 3 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 3. assume H2: Adj17 3 16. assume H3: Adj17 2 16.
exact Adj17_not_2_3 H1.
Qed.

Theorem tf_2_4_0 : Adj17 2 4 -> Adj17 4 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 0. assume H3: Adj17 2 0.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_1 : Adj17 2 4 -> Adj17 4 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 1. assume H3: Adj17 2 1.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_2 : Adj17 2 4 -> Adj17 4 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_4_3 : Adj17 2 4 -> Adj17 4 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 3. assume H3: Adj17 2 3.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_4 : Adj17 2 4 -> Adj17 4 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 4. assume H3: Adj17 2 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_2_4_5 : Adj17 2 4 -> Adj17 4 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 5. assume H3: Adj17 2 5.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_6 : Adj17 2 4 -> Adj17 4 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 6. assume H3: Adj17 2 6.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_7 : Adj17 2 4 -> Adj17 4 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 7. assume H3: Adj17 2 7.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_8 : Adj17 2 4 -> Adj17 4 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 8. assume H3: Adj17 2 8.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_9 : Adj17 2 4 -> Adj17 4 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 9. assume H3: Adj17 2 9.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_10 : Adj17 2 4 -> Adj17 4 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 10. assume H3: Adj17 2 10.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_11 : Adj17 2 4 -> Adj17 4 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 11. assume H3: Adj17 2 11.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_12 : Adj17 2 4 -> Adj17 4 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 12. assume H3: Adj17 2 12.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_13 : Adj17 2 4 -> Adj17 4 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 13. assume H3: Adj17 2 13.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_14 : Adj17 2 4 -> Adj17 4 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 14. assume H3: Adj17 2 14.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_15 : Adj17 2 4 -> Adj17 4 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 15. assume H3: Adj17 2 15.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_4_16 : Adj17 2 4 -> Adj17 4 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 4. assume H2: Adj17 4 16. assume H3: Adj17 2 16.
exact Adj17_not_2_4 H1.
Qed.

Theorem tf_2_5_0 : Adj17 2 5 -> Adj17 5 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 0. assume H3: Adj17 2 0.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_1 : Adj17 2 5 -> Adj17 5 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 1. assume H3: Adj17 2 1.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_2 : Adj17 2 5 -> Adj17 5 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_5_3 : Adj17 2 5 -> Adj17 5 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 3. assume H3: Adj17 2 3.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_4 : Adj17 2 5 -> Adj17 5 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 4. assume H3: Adj17 2 4.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_5 : Adj17 2 5 -> Adj17 5 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 5. assume H3: Adj17 2 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_2_5_6 : Adj17 2 5 -> Adj17 5 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 6. assume H3: Adj17 2 6.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_7 : Adj17 2 5 -> Adj17 5 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 7. assume H3: Adj17 2 7.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_8 : Adj17 2 5 -> Adj17 5 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 8. assume H3: Adj17 2 8.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_9 : Adj17 2 5 -> Adj17 5 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 9. assume H3: Adj17 2 9.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_10 : Adj17 2 5 -> Adj17 5 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 10. assume H3: Adj17 2 10.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_11 : Adj17 2 5 -> Adj17 5 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 11. assume H3: Adj17 2 11.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_12 : Adj17 2 5 -> Adj17 5 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 12. assume H3: Adj17 2 12.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_13 : Adj17 2 5 -> Adj17 5 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 13. assume H3: Adj17 2 13.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_14 : Adj17 2 5 -> Adj17 5 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 14. assume H3: Adj17 2 14.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_15 : Adj17 2 5 -> Adj17 5 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 15. assume H3: Adj17 2 15.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_5_16 : Adj17 2 5 -> Adj17 5 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 5. assume H2: Adj17 5 16. assume H3: Adj17 2 16.
exact Adj17_not_2_5 H1.
Qed.

Theorem tf_2_6_0 : Adj17 2 6 -> Adj17 6 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 0. assume H3: Adj17 2 0.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_1 : Adj17 2 6 -> Adj17 6 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 1. assume H3: Adj17 2 1.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_2 : Adj17 2 6 -> Adj17 6 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_6_3 : Adj17 2 6 -> Adj17 6 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 3. assume H3: Adj17 2 3.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_4 : Adj17 2 6 -> Adj17 6 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 4. assume H3: Adj17 2 4.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_5 : Adj17 2 6 -> Adj17 6 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 5. assume H3: Adj17 2 5.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_6 : Adj17 2 6 -> Adj17 6 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 6. assume H3: Adj17 2 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_2_6_7 : Adj17 2 6 -> Adj17 6 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 7. assume H3: Adj17 2 7.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_8 : Adj17 2 6 -> Adj17 6 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 8. assume H3: Adj17 2 8.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_9 : Adj17 2 6 -> Adj17 6 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 9. assume H3: Adj17 2 9.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_10 : Adj17 2 6 -> Adj17 6 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 10. assume H3: Adj17 2 10.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_11 : Adj17 2 6 -> Adj17 6 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 11. assume H3: Adj17 2 11.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_12 : Adj17 2 6 -> Adj17 6 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 12. assume H3: Adj17 2 12.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_13 : Adj17 2 6 -> Adj17 6 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 13. assume H3: Adj17 2 13.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_14 : Adj17 2 6 -> Adj17 6 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 14. assume H3: Adj17 2 14.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_15 : Adj17 2 6 -> Adj17 6 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 15. assume H3: Adj17 2 15.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_6_16 : Adj17 2 6 -> Adj17 6 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 6. assume H2: Adj17 6 16. assume H3: Adj17 2 16.
exact Adj17_not_2_6 H1.
Qed.

Theorem tf_2_7_0 : Adj17 2 7 -> Adj17 7 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 0. assume H3: Adj17 2 0.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_1 : Adj17 2 7 -> Adj17 7 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 1. assume H3: Adj17 2 1.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_2 : Adj17 2 7 -> Adj17 7 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_7_3 : Adj17 2 7 -> Adj17 7 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 3. assume H3: Adj17 2 3.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_4 : Adj17 2 7 -> Adj17 7 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 4. assume H3: Adj17 2 4.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_5 : Adj17 2 7 -> Adj17 7 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 5. assume H3: Adj17 2 5.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_6 : Adj17 2 7 -> Adj17 7 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 6. assume H3: Adj17 2 6.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_7 : Adj17 2 7 -> Adj17 7 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 7. assume H3: Adj17 2 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_2_7_8 : Adj17 2 7 -> Adj17 7 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 8. assume H3: Adj17 2 8.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_9 : Adj17 2 7 -> Adj17 7 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 9. assume H3: Adj17 2 9.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_10 : Adj17 2 7 -> Adj17 7 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 10. assume H3: Adj17 2 10.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_11 : Adj17 2 7 -> Adj17 7 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 11. assume H3: Adj17 2 11.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_12 : Adj17 2 7 -> Adj17 7 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 12. assume H3: Adj17 2 12.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_13 : Adj17 2 7 -> Adj17 7 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 13. assume H3: Adj17 2 13.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_14 : Adj17 2 7 -> Adj17 7 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 14. assume H3: Adj17 2 14.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_15 : Adj17 2 7 -> Adj17 7 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 15. assume H3: Adj17 2 15.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_7_16 : Adj17 2 7 -> Adj17 7 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 7. assume H2: Adj17 7 16. assume H3: Adj17 2 16.
exact Adj17_not_2_7 H1.
Qed.

Theorem tf_2_8_0 : Adj17 2 8 -> Adj17 8 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 0. assume H3: Adj17 2 0.
exact Adj17_not_8_0 H2.
Qed.

Theorem tf_2_8_1 : Adj17 2 8 -> Adj17 8 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 1. assume H3: Adj17 2 1.
exact Adj17_not_8_1 H2.
Qed.

Theorem tf_2_8_2 : Adj17 2 8 -> Adj17 8 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_8_3 : Adj17 2 8 -> Adj17 8 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 3. assume H3: Adj17 2 3.
exact Adj17_not_2_3 H3.
Qed.

Theorem tf_2_8_4 : Adj17 2 8 -> Adj17 8 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 4. assume H3: Adj17 2 4.
exact Adj17_not_8_4 H2.
Qed.

Theorem tf_2_8_5 : Adj17 2 8 -> Adj17 8 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 5. assume H3: Adj17 2 5.
exact Adj17_not_8_5 H2.
Qed.

Theorem tf_2_8_6 : Adj17 2 8 -> Adj17 8 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 6. assume H3: Adj17 2 6.
exact Adj17_not_8_6 H2.
Qed.

Theorem tf_2_8_7 : Adj17 2 8 -> Adj17 8 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 7. assume H3: Adj17 2 7.
exact Adj17_not_8_7 H2.
Qed.

Theorem tf_2_8_8 : Adj17 2 8 -> Adj17 8 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 8. assume H3: Adj17 2 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_2_8_9 : Adj17 2 8 -> Adj17 8 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 9. assume H3: Adj17 2 9.
exact Adj17_not_2_9 H3.
Qed.

Theorem tf_2_8_10 : Adj17 2 8 -> Adj17 8 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 10. assume H3: Adj17 2 10.
exact Adj17_not_8_10 H2.
Qed.

Theorem tf_2_8_11 : Adj17 2 8 -> Adj17 8 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 11. assume H3: Adj17 2 11.
exact Adj17_not_2_11 H3.
Qed.

Theorem tf_2_8_12 : Adj17 2 8 -> Adj17 8 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 12. assume H3: Adj17 2 12.
exact Adj17_not_8_12 H2.
Qed.

Theorem tf_2_8_13 : Adj17 2 8 -> Adj17 8 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 13. assume H3: Adj17 2 13.
exact Adj17_not_8_13 H2.
Qed.

Theorem tf_2_8_14 : Adj17 2 8 -> Adj17 8 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 14. assume H3: Adj17 2 14.
exact Adj17_not_2_14 H3.
Qed.

Theorem tf_2_8_15 : Adj17 2 8 -> Adj17 8 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 15. assume H3: Adj17 2 15.
exact Adj17_not_8_15 H2.
Qed.

Theorem tf_2_8_16 : Adj17 2 8 -> Adj17 8 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 8. assume H2: Adj17 8 16. assume H3: Adj17 2 16.
exact Adj17_not_8_16 H2.
Qed.

Theorem tf_2_9_0 : Adj17 2 9 -> Adj17 9 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 0. assume H3: Adj17 2 0.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_1 : Adj17 2 9 -> Adj17 9 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 1. assume H3: Adj17 2 1.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_2 : Adj17 2 9 -> Adj17 9 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_9_3 : Adj17 2 9 -> Adj17 9 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 3. assume H3: Adj17 2 3.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_4 : Adj17 2 9 -> Adj17 9 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 4. assume H3: Adj17 2 4.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_5 : Adj17 2 9 -> Adj17 9 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 5. assume H3: Adj17 2 5.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_6 : Adj17 2 9 -> Adj17 9 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 6. assume H3: Adj17 2 6.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_7 : Adj17 2 9 -> Adj17 9 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 7. assume H3: Adj17 2 7.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_8 : Adj17 2 9 -> Adj17 9 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 8. assume H3: Adj17 2 8.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_9 : Adj17 2 9 -> Adj17 9 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 9. assume H3: Adj17 2 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_2_9_10 : Adj17 2 9 -> Adj17 9 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 10. assume H3: Adj17 2 10.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_11 : Adj17 2 9 -> Adj17 9 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 11. assume H3: Adj17 2 11.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_12 : Adj17 2 9 -> Adj17 9 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 12. assume H3: Adj17 2 12.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_13 : Adj17 2 9 -> Adj17 9 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 13. assume H3: Adj17 2 13.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_14 : Adj17 2 9 -> Adj17 9 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 14. assume H3: Adj17 2 14.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_15 : Adj17 2 9 -> Adj17 9 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 15. assume H3: Adj17 2 15.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_9_16 : Adj17 2 9 -> Adj17 9 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 9. assume H2: Adj17 9 16. assume H3: Adj17 2 16.
exact Adj17_not_2_9 H1.
Qed.

Theorem tf_2_10_0 : Adj17 2 10 -> Adj17 10 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 0. assume H3: Adj17 2 0.
exact Adj17_not_10_0 H2.
Qed.

Theorem tf_2_10_1 : Adj17 2 10 -> Adj17 10 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 1. assume H3: Adj17 2 1.
exact Adj17_not_10_1 H2.
Qed.

Theorem tf_2_10_2 : Adj17 2 10 -> Adj17 10 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_10_3 : Adj17 2 10 -> Adj17 10 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 3. assume H3: Adj17 2 3.
exact Adj17_not_10_3 H2.
Qed.

Theorem tf_2_10_4 : Adj17 2 10 -> Adj17 10 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 4. assume H3: Adj17 2 4.
exact Adj17_not_10_4 H2.
Qed.

Theorem tf_2_10_5 : Adj17 2 10 -> Adj17 10 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 5. assume H3: Adj17 2 5.
exact Adj17_not_2_5 H3.
Qed.

Theorem tf_2_10_6 : Adj17 2 10 -> Adj17 10 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 6. assume H3: Adj17 2 6.
exact Adj17_not_2_6 H3.
Qed.

Theorem tf_2_10_7 : Adj17 2 10 -> Adj17 10 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 7. assume H3: Adj17 2 7.
exact Adj17_not_2_7 H3.
Qed.

Theorem tf_2_10_8 : Adj17 2 10 -> Adj17 10 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 8. assume H3: Adj17 2 8.
exact Adj17_not_10_8 H2.
Qed.

Theorem tf_2_10_9 : Adj17 2 10 -> Adj17 10 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 9. assume H3: Adj17 2 9.
exact Adj17_not_10_9 H2.
Qed.

Theorem tf_2_10_10 : Adj17 2 10 -> Adj17 10 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 10. assume H3: Adj17 2 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_2_10_11 : Adj17 2 10 -> Adj17 10 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 11. assume H3: Adj17 2 11.
exact Adj17_not_10_11 H2.
Qed.

Theorem tf_2_10_12 : Adj17 2 10 -> Adj17 10 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 12. assume H3: Adj17 2 12.
exact Adj17_not_10_12 H2.
Qed.

Theorem tf_2_10_13 : Adj17 2 10 -> Adj17 10 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 13. assume H3: Adj17 2 13.
exact Adj17_not_10_13 H2.
Qed.

Theorem tf_2_10_14 : Adj17 2 10 -> Adj17 10 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 14. assume H3: Adj17 2 14.
exact Adj17_not_10_14 H2.
Qed.

Theorem tf_2_10_15 : Adj17 2 10 -> Adj17 10 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 15. assume H3: Adj17 2 15.
exact Adj17_not_10_15 H2.
Qed.

Theorem tf_2_10_16 : Adj17 2 10 -> Adj17 10 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 10. assume H2: Adj17 10 16. assume H3: Adj17 2 16.
exact Adj17_not_2_16 H3.
Qed.

Theorem tf_2_11_0 : Adj17 2 11 -> Adj17 11 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 0. assume H3: Adj17 2 0.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_1 : Adj17 2 11 -> Adj17 11 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 1. assume H3: Adj17 2 1.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_2 : Adj17 2 11 -> Adj17 11 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_11_3 : Adj17 2 11 -> Adj17 11 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 3. assume H3: Adj17 2 3.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_4 : Adj17 2 11 -> Adj17 11 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 4. assume H3: Adj17 2 4.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_5 : Adj17 2 11 -> Adj17 11 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 5. assume H3: Adj17 2 5.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_6 : Adj17 2 11 -> Adj17 11 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 6. assume H3: Adj17 2 6.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_7 : Adj17 2 11 -> Adj17 11 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 7. assume H3: Adj17 2 7.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_8 : Adj17 2 11 -> Adj17 11 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 8. assume H3: Adj17 2 8.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_9 : Adj17 2 11 -> Adj17 11 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 9. assume H3: Adj17 2 9.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_10 : Adj17 2 11 -> Adj17 11 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 10. assume H3: Adj17 2 10.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_11 : Adj17 2 11 -> Adj17 11 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 11. assume H3: Adj17 2 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_2_11_12 : Adj17 2 11 -> Adj17 11 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 12. assume H3: Adj17 2 12.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_13 : Adj17 2 11 -> Adj17 11 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 13. assume H3: Adj17 2 13.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_14 : Adj17 2 11 -> Adj17 11 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 14. assume H3: Adj17 2 14.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_15 : Adj17 2 11 -> Adj17 11 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 15. assume H3: Adj17 2 15.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_11_16 : Adj17 2 11 -> Adj17 11 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 11. assume H2: Adj17 11 16. assume H3: Adj17 2 16.
exact Adj17_not_2_11 H1.
Qed.

Theorem tf_2_12_0 : Adj17 2 12 -> Adj17 12 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 0. assume H3: Adj17 2 0.
exact Adj17_not_12_0 H2.
Qed.

Theorem tf_2_12_1 : Adj17 2 12 -> Adj17 12 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 1. assume H3: Adj17 2 1.
exact Adj17_not_12_1 H2.
Qed.

Theorem tf_2_12_2 : Adj17 2 12 -> Adj17 12 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_12_3 : Adj17 2 12 -> Adj17 12 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 3. assume H3: Adj17 2 3.
exact Adj17_not_12_3 H2.
Qed.

Theorem tf_2_12_4 : Adj17 2 12 -> Adj17 12 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 4. assume H3: Adj17 2 4.
exact Adj17_not_2_4 H3.
Qed.

Theorem tf_2_12_5 : Adj17 2 12 -> Adj17 12 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 5. assume H3: Adj17 2 5.
exact Adj17_not_12_5 H2.
Qed.

Theorem tf_2_12_6 : Adj17 2 12 -> Adj17 12 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 6. assume H3: Adj17 2 6.
exact Adj17_not_2_6 H3.
Qed.

Theorem tf_2_12_7 : Adj17 2 12 -> Adj17 12 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 7. assume H3: Adj17 2 7.
exact Adj17_not_12_7 H2.
Qed.

Theorem tf_2_12_8 : Adj17 2 12 -> Adj17 12 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 8. assume H3: Adj17 2 8.
exact Adj17_not_12_8 H2.
Qed.

Theorem tf_2_12_9 : Adj17 2 12 -> Adj17 12 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 9. assume H3: Adj17 2 9.
exact Adj17_not_2_9 H3.
Qed.

Theorem tf_2_12_10 : Adj17 2 12 -> Adj17 12 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 10. assume H3: Adj17 2 10.
exact Adj17_not_12_10 H2.
Qed.

Theorem tf_2_12_11 : Adj17 2 12 -> Adj17 12 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 11. assume H3: Adj17 2 11.
exact Adj17_not_12_11 H2.
Qed.

Theorem tf_2_12_12 : Adj17 2 12 -> Adj17 12 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 12. assume H3: Adj17 2 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_2_12_13 : Adj17 2 12 -> Adj17 12 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 13. assume H3: Adj17 2 13.
exact Adj17_not_2_13 H3.
Qed.

Theorem tf_2_12_14 : Adj17 2 12 -> Adj17 12 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 14. assume H3: Adj17 2 14.
exact Adj17_not_12_14 H2.
Qed.

Theorem tf_2_12_15 : Adj17 2 12 -> Adj17 12 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 15. assume H3: Adj17 2 15.
exact Adj17_not_12_15 H2.
Qed.

Theorem tf_2_12_16 : Adj17 2 12 -> Adj17 12 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 12. assume H2: Adj17 12 16. assume H3: Adj17 2 16.
exact Adj17_not_12_16 H2.
Qed.

Theorem tf_2_13_0 : Adj17 2 13 -> Adj17 13 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 0. assume H3: Adj17 2 0.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_1 : Adj17 2 13 -> Adj17 13 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 1. assume H3: Adj17 2 1.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_2 : Adj17 2 13 -> Adj17 13 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_13_3 : Adj17 2 13 -> Adj17 13 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 3. assume H3: Adj17 2 3.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_4 : Adj17 2 13 -> Adj17 13 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 4. assume H3: Adj17 2 4.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_5 : Adj17 2 13 -> Adj17 13 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 5. assume H3: Adj17 2 5.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_6 : Adj17 2 13 -> Adj17 13 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 6. assume H3: Adj17 2 6.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_7 : Adj17 2 13 -> Adj17 13 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 7. assume H3: Adj17 2 7.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_8 : Adj17 2 13 -> Adj17 13 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 8. assume H3: Adj17 2 8.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_9 : Adj17 2 13 -> Adj17 13 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 9. assume H3: Adj17 2 9.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_10 : Adj17 2 13 -> Adj17 13 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 10. assume H3: Adj17 2 10.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_11 : Adj17 2 13 -> Adj17 13 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 11. assume H3: Adj17 2 11.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_12 : Adj17 2 13 -> Adj17 13 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 12. assume H3: Adj17 2 12.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_13 : Adj17 2 13 -> Adj17 13 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 13. assume H3: Adj17 2 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_2_13_14 : Adj17 2 13 -> Adj17 13 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 14. assume H3: Adj17 2 14.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_15 : Adj17 2 13 -> Adj17 13 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 15. assume H3: Adj17 2 15.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_13_16 : Adj17 2 13 -> Adj17 13 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 13. assume H2: Adj17 13 16. assume H3: Adj17 2 16.
exact Adj17_not_2_13 H1.
Qed.

Theorem tf_2_14_0 : Adj17 2 14 -> Adj17 14 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 0. assume H3: Adj17 2 0.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_1 : Adj17 2 14 -> Adj17 14 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 1. assume H3: Adj17 2 1.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_2 : Adj17 2 14 -> Adj17 14 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_14_3 : Adj17 2 14 -> Adj17 14 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 3. assume H3: Adj17 2 3.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_4 : Adj17 2 14 -> Adj17 14 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 4. assume H3: Adj17 2 4.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_5 : Adj17 2 14 -> Adj17 14 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 5. assume H3: Adj17 2 5.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_6 : Adj17 2 14 -> Adj17 14 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 6. assume H3: Adj17 2 6.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_7 : Adj17 2 14 -> Adj17 14 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 7. assume H3: Adj17 2 7.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_8 : Adj17 2 14 -> Adj17 14 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 8. assume H3: Adj17 2 8.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_9 : Adj17 2 14 -> Adj17 14 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 9. assume H3: Adj17 2 9.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_10 : Adj17 2 14 -> Adj17 14 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 10. assume H3: Adj17 2 10.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_11 : Adj17 2 14 -> Adj17 14 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 11. assume H3: Adj17 2 11.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_12 : Adj17 2 14 -> Adj17 14 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 12. assume H3: Adj17 2 12.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_13 : Adj17 2 14 -> Adj17 14 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 13. assume H3: Adj17 2 13.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_14 : Adj17 2 14 -> Adj17 14 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 14. assume H3: Adj17 2 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_2_14_15 : Adj17 2 14 -> Adj17 14 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 15. assume H3: Adj17 2 15.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_14_16 : Adj17 2 14 -> Adj17 14 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 14. assume H2: Adj17 14 16. assume H3: Adj17 2 16.
exact Adj17_not_2_14 H1.
Qed.

Theorem tf_2_15_0 : Adj17 2 15 -> Adj17 15 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 0. assume H3: Adj17 2 0.
exact Adj17_not_2_0 H3.
Qed.

Theorem tf_2_15_1 : Adj17 2 15 -> Adj17 15 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 1. assume H3: Adj17 2 1.
exact Adj17_not_15_1 H2.
Qed.

Theorem tf_2_15_2 : Adj17 2 15 -> Adj17 15 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_15_3 : Adj17 2 15 -> Adj17 15 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 3. assume H3: Adj17 2 3.
exact Adj17_not_2_3 H3.
Qed.

Theorem tf_2_15_4 : Adj17 2 15 -> Adj17 15 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 4. assume H3: Adj17 2 4.
exact Adj17_not_15_4 H2.
Qed.

Theorem tf_2_15_5 : Adj17 2 15 -> Adj17 15 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 5. assume H3: Adj17 2 5.
exact Adj17_not_15_5 H2.
Qed.

Theorem tf_2_15_6 : Adj17 2 15 -> Adj17 15 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 6. assume H3: Adj17 2 6.
exact Adj17_not_15_6 H2.
Qed.

Theorem tf_2_15_7 : Adj17 2 15 -> Adj17 15 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 7. assume H3: Adj17 2 7.
exact Adj17_not_2_7 H3.
Qed.

Theorem tf_2_15_8 : Adj17 2 15 -> Adj17 15 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 8. assume H3: Adj17 2 8.
exact Adj17_not_15_8 H2.
Qed.

Theorem tf_2_15_9 : Adj17 2 15 -> Adj17 15 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 9. assume H3: Adj17 2 9.
exact Adj17_not_15_9 H2.
Qed.

Theorem tf_2_15_10 : Adj17 2 15 -> Adj17 15 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 10. assume H3: Adj17 2 10.
exact Adj17_not_15_10 H2.
Qed.

Theorem tf_2_15_11 : Adj17 2 15 -> Adj17 15 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 11. assume H3: Adj17 2 11.
exact Adj17_not_2_11 H3.
Qed.

Theorem tf_2_15_12 : Adj17 2 15 -> Adj17 15 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 12. assume H3: Adj17 2 12.
exact Adj17_not_15_12 H2.
Qed.

Theorem tf_2_15_13 : Adj17 2 15 -> Adj17 15 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 13. assume H3: Adj17 2 13.
exact Adj17_not_15_13 H2.
Qed.

Theorem tf_2_15_14 : Adj17 2 15 -> Adj17 15 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 14. assume H3: Adj17 2 14.
exact Adj17_not_15_14 H2.
Qed.

Theorem tf_2_15_15 : Adj17 2 15 -> Adj17 15 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 15. assume H3: Adj17 2 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_2_15_16 : Adj17 2 15 -> Adj17 15 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 15. assume H2: Adj17 15 16. assume H3: Adj17 2 16.
exact Adj17_not_15_16 H2.
Qed.

Theorem tf_2_16_0 : Adj17 2 16 -> Adj17 16 0 -> Adj17 2 0 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 0. assume H3: Adj17 2 0.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_1 : Adj17 2 16 -> Adj17 16 1 -> Adj17 2 1 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 1. assume H3: Adj17 2 1.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_2 : Adj17 2 16 -> Adj17 16 2 -> Adj17 2 2 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 2. assume H3: Adj17 2 2.
exact Adj17_not_2_2 H3.
Qed.

Theorem tf_2_16_3 : Adj17 2 16 -> Adj17 16 3 -> Adj17 2 3 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 3. assume H3: Adj17 2 3.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_4 : Adj17 2 16 -> Adj17 16 4 -> Adj17 2 4 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 4. assume H3: Adj17 2 4.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_5 : Adj17 2 16 -> Adj17 16 5 -> Adj17 2 5 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 5. assume H3: Adj17 2 5.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_6 : Adj17 2 16 -> Adj17 16 6 -> Adj17 2 6 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 6. assume H3: Adj17 2 6.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_7 : Adj17 2 16 -> Adj17 16 7 -> Adj17 2 7 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 7. assume H3: Adj17 2 7.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_8 : Adj17 2 16 -> Adj17 16 8 -> Adj17 2 8 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 8. assume H3: Adj17 2 8.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_9 : Adj17 2 16 -> Adj17 16 9 -> Adj17 2 9 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 9. assume H3: Adj17 2 9.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_10 : Adj17 2 16 -> Adj17 16 10 -> Adj17 2 10 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 10. assume H3: Adj17 2 10.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_11 : Adj17 2 16 -> Adj17 16 11 -> Adj17 2 11 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 11. assume H3: Adj17 2 11.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_12 : Adj17 2 16 -> Adj17 16 12 -> Adj17 2 12 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 12. assume H3: Adj17 2 12.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_13 : Adj17 2 16 -> Adj17 16 13 -> Adj17 2 13 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 13. assume H3: Adj17 2 13.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_14 : Adj17 2 16 -> Adj17 16 14 -> Adj17 2 14 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 14. assume H3: Adj17 2 14.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_15 : Adj17 2 16 -> Adj17 16 15 -> Adj17 2 15 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 15. assume H3: Adj17 2 15.
exact Adj17_not_2_16 H1.
Qed.

Theorem tf_2_16_16 : Adj17 2 16 -> Adj17 16 16 -> Adj17 2 16 -> False.
assume H1: Adj17 2 16. assume H2: Adj17 16 16. assume H3: Adj17 2 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_3_0_0 : Adj17 3 0 -> Adj17 0 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 0. assume H3: Adj17 3 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_3_0_1 : Adj17 3 0 -> Adj17 0 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 1. assume H3: Adj17 3 1.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_2 : Adj17 3 0 -> Adj17 0 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 2. assume H3: Adj17 3 2.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_3 : Adj17 3 0 -> Adj17 0 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_0_4 : Adj17 3 0 -> Adj17 0 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 4. assume H3: Adj17 3 4.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_5 : Adj17 3 0 -> Adj17 0 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 5. assume H3: Adj17 3 5.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_6 : Adj17 3 0 -> Adj17 0 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 6. assume H3: Adj17 3 6.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_7 : Adj17 3 0 -> Adj17 0 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 7. assume H3: Adj17 3 7.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_8 : Adj17 3 0 -> Adj17 0 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 8. assume H3: Adj17 3 8.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_9 : Adj17 3 0 -> Adj17 0 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 9. assume H3: Adj17 3 9.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_10 : Adj17 3 0 -> Adj17 0 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 10. assume H3: Adj17 3 10.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_11 : Adj17 3 0 -> Adj17 0 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 11. assume H3: Adj17 3 11.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_12 : Adj17 3 0 -> Adj17 0 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 12. assume H3: Adj17 3 12.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_13 : Adj17 3 0 -> Adj17 0 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 13. assume H3: Adj17 3 13.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_14 : Adj17 3 0 -> Adj17 0 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 14. assume H3: Adj17 3 14.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_15 : Adj17 3 0 -> Adj17 0 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 15. assume H3: Adj17 3 15.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_0_16 : Adj17 3 0 -> Adj17 0 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 0. assume H2: Adj17 0 16. assume H3: Adj17 3 16.
exact Adj17_not_3_0 H1.
Qed.

Theorem tf_3_1_0 : Adj17 3 1 -> Adj17 1 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 0. assume H3: Adj17 3 0.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_1 : Adj17 3 1 -> Adj17 1 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 1. assume H3: Adj17 3 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_3_1_2 : Adj17 3 1 -> Adj17 1 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 2. assume H3: Adj17 3 2.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_3 : Adj17 3 1 -> Adj17 1 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_1_4 : Adj17 3 1 -> Adj17 1 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 4. assume H3: Adj17 3 4.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_5 : Adj17 3 1 -> Adj17 1 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 5. assume H3: Adj17 3 5.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_6 : Adj17 3 1 -> Adj17 1 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 6. assume H3: Adj17 3 6.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_7 : Adj17 3 1 -> Adj17 1 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 7. assume H3: Adj17 3 7.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_8 : Adj17 3 1 -> Adj17 1 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 8. assume H3: Adj17 3 8.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_9 : Adj17 3 1 -> Adj17 1 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 9. assume H3: Adj17 3 9.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_10 : Adj17 3 1 -> Adj17 1 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 10. assume H3: Adj17 3 10.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_11 : Adj17 3 1 -> Adj17 1 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 11. assume H3: Adj17 3 11.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_12 : Adj17 3 1 -> Adj17 1 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 12. assume H3: Adj17 3 12.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_13 : Adj17 3 1 -> Adj17 1 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 13. assume H3: Adj17 3 13.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_14 : Adj17 3 1 -> Adj17 1 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 14. assume H3: Adj17 3 14.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_15 : Adj17 3 1 -> Adj17 1 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 15. assume H3: Adj17 3 15.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_1_16 : Adj17 3 1 -> Adj17 1 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 1. assume H2: Adj17 1 16. assume H3: Adj17 3 16.
exact Adj17_not_3_1 H1.
Qed.

Theorem tf_3_2_0 : Adj17 3 2 -> Adj17 2 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 0. assume H3: Adj17 3 0.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_1 : Adj17 3 2 -> Adj17 2 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 1. assume H3: Adj17 3 1.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_2 : Adj17 3 2 -> Adj17 2 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 2. assume H3: Adj17 3 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_3_2_3 : Adj17 3 2 -> Adj17 2 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_2_4 : Adj17 3 2 -> Adj17 2 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 4. assume H3: Adj17 3 4.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_5 : Adj17 3 2 -> Adj17 2 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 5. assume H3: Adj17 3 5.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_6 : Adj17 3 2 -> Adj17 2 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 6. assume H3: Adj17 3 6.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_7 : Adj17 3 2 -> Adj17 2 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 7. assume H3: Adj17 3 7.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_8 : Adj17 3 2 -> Adj17 2 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 8. assume H3: Adj17 3 8.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_9 : Adj17 3 2 -> Adj17 2 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 9. assume H3: Adj17 3 9.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_10 : Adj17 3 2 -> Adj17 2 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 10. assume H3: Adj17 3 10.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_11 : Adj17 3 2 -> Adj17 2 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 11. assume H3: Adj17 3 11.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_12 : Adj17 3 2 -> Adj17 2 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 12. assume H3: Adj17 3 12.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_13 : Adj17 3 2 -> Adj17 2 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 13. assume H3: Adj17 3 13.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_14 : Adj17 3 2 -> Adj17 2 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 14. assume H3: Adj17 3 14.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_15 : Adj17 3 2 -> Adj17 2 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 15. assume H3: Adj17 3 15.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_2_16 : Adj17 3 2 -> Adj17 2 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 2. assume H2: Adj17 2 16. assume H3: Adj17 3 16.
exact Adj17_not_3_2 H1.
Qed.

Theorem tf_3_3_0 : Adj17 3 3 -> Adj17 3 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 0. assume H3: Adj17 3 0.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_1 : Adj17 3 3 -> Adj17 3 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 1. assume H3: Adj17 3 1.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_2 : Adj17 3 3 -> Adj17 3 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 2. assume H3: Adj17 3 2.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_3 : Adj17 3 3 -> Adj17 3 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_4 : Adj17 3 3 -> Adj17 3 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 4. assume H3: Adj17 3 4.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_5 : Adj17 3 3 -> Adj17 3 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 5. assume H3: Adj17 3 5.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_6 : Adj17 3 3 -> Adj17 3 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 6. assume H3: Adj17 3 6.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_7 : Adj17 3 3 -> Adj17 3 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 7. assume H3: Adj17 3 7.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_8 : Adj17 3 3 -> Adj17 3 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 8. assume H3: Adj17 3 8.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_9 : Adj17 3 3 -> Adj17 3 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 9. assume H3: Adj17 3 9.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_10 : Adj17 3 3 -> Adj17 3 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 10. assume H3: Adj17 3 10.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_11 : Adj17 3 3 -> Adj17 3 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 11. assume H3: Adj17 3 11.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_12 : Adj17 3 3 -> Adj17 3 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 12. assume H3: Adj17 3 12.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_13 : Adj17 3 3 -> Adj17 3 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 13. assume H3: Adj17 3 13.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_14 : Adj17 3 3 -> Adj17 3 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 14. assume H3: Adj17 3 14.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_15 : Adj17 3 3 -> Adj17 3 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 15. assume H3: Adj17 3 15.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_3_16 : Adj17 3 3 -> Adj17 3 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 3. assume H2: Adj17 3 16. assume H3: Adj17 3 16.
exact Adj17_not_3_3 H1.
Qed.

Theorem tf_3_4_0 : Adj17 3 4 -> Adj17 4 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 0. assume H3: Adj17 3 0.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_1 : Adj17 3 4 -> Adj17 4 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 1. assume H3: Adj17 3 1.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_2 : Adj17 3 4 -> Adj17 4 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 2. assume H3: Adj17 3 2.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_3 : Adj17 3 4 -> Adj17 4 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_4_4 : Adj17 3 4 -> Adj17 4 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 4. assume H3: Adj17 3 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_3_4_5 : Adj17 3 4 -> Adj17 4 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 5. assume H3: Adj17 3 5.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_6 : Adj17 3 4 -> Adj17 4 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 6. assume H3: Adj17 3 6.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_7 : Adj17 3 4 -> Adj17 4 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 7. assume H3: Adj17 3 7.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_8 : Adj17 3 4 -> Adj17 4 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 8. assume H3: Adj17 3 8.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_9 : Adj17 3 4 -> Adj17 4 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 9. assume H3: Adj17 3 9.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_10 : Adj17 3 4 -> Adj17 4 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 10. assume H3: Adj17 3 10.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_11 : Adj17 3 4 -> Adj17 4 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 11. assume H3: Adj17 3 11.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_12 : Adj17 3 4 -> Adj17 4 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 12. assume H3: Adj17 3 12.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_13 : Adj17 3 4 -> Adj17 4 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 13. assume H3: Adj17 3 13.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_14 : Adj17 3 4 -> Adj17 4 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 14. assume H3: Adj17 3 14.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_15 : Adj17 3 4 -> Adj17 4 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 15. assume H3: Adj17 3 15.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_4_16 : Adj17 3 4 -> Adj17 4 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 4. assume H2: Adj17 4 16. assume H3: Adj17 3 16.
exact Adj17_not_3_4 H1.
Qed.

Theorem tf_3_5_0 : Adj17 3 5 -> Adj17 5 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 0. assume H3: Adj17 3 0.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_1 : Adj17 3 5 -> Adj17 5 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 1. assume H3: Adj17 3 1.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_2 : Adj17 3 5 -> Adj17 5 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 2. assume H3: Adj17 3 2.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_3 : Adj17 3 5 -> Adj17 5 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_5_4 : Adj17 3 5 -> Adj17 5 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 4. assume H3: Adj17 3 4.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_5 : Adj17 3 5 -> Adj17 5 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 5. assume H3: Adj17 3 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_3_5_6 : Adj17 3 5 -> Adj17 5 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 6. assume H3: Adj17 3 6.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_7 : Adj17 3 5 -> Adj17 5 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 7. assume H3: Adj17 3 7.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_8 : Adj17 3 5 -> Adj17 5 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 8. assume H3: Adj17 3 8.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_9 : Adj17 3 5 -> Adj17 5 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 9. assume H3: Adj17 3 9.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_10 : Adj17 3 5 -> Adj17 5 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 10. assume H3: Adj17 3 10.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_11 : Adj17 3 5 -> Adj17 5 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 11. assume H3: Adj17 3 11.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_12 : Adj17 3 5 -> Adj17 5 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 12. assume H3: Adj17 3 12.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_13 : Adj17 3 5 -> Adj17 5 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 13. assume H3: Adj17 3 13.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_14 : Adj17 3 5 -> Adj17 5 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 14. assume H3: Adj17 3 14.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_15 : Adj17 3 5 -> Adj17 5 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 15. assume H3: Adj17 3 15.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_5_16 : Adj17 3 5 -> Adj17 5 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 5. assume H2: Adj17 5 16. assume H3: Adj17 3 16.
exact Adj17_not_3_5 H1.
Qed.

Theorem tf_3_6_0 : Adj17 3 6 -> Adj17 6 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 0. assume H3: Adj17 3 0.
exact Adj17_not_6_0 H2.
Qed.

Theorem tf_3_6_1 : Adj17 3 6 -> Adj17 6 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 1. assume H3: Adj17 3 1.
exact Adj17_not_6_1 H2.
Qed.

Theorem tf_3_6_2 : Adj17 3 6 -> Adj17 6 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 2. assume H3: Adj17 3 2.
exact Adj17_not_6_2 H2.
Qed.

Theorem tf_3_6_3 : Adj17 3 6 -> Adj17 6 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_6_4 : Adj17 3 6 -> Adj17 6 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 4. assume H3: Adj17 3 4.
exact Adj17_not_6_4 H2.
Qed.

Theorem tf_3_6_5 : Adj17 3 6 -> Adj17 6 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 5. assume H3: Adj17 3 5.
exact Adj17_not_6_5 H2.
Qed.

Theorem tf_3_6_6 : Adj17 3 6 -> Adj17 6 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 6. assume H3: Adj17 3 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_3_6_7 : Adj17 3 6 -> Adj17 6 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 7. assume H3: Adj17 3 7.
exact Adj17_not_6_7 H2.
Qed.

Theorem tf_3_6_8 : Adj17 3 6 -> Adj17 6 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 8. assume H3: Adj17 3 8.
exact Adj17_not_6_8 H2.
Qed.

Theorem tf_3_6_9 : Adj17 3 6 -> Adj17 6 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 9. assume H3: Adj17 3 9.
exact Adj17_not_6_9 H2.
Qed.

Theorem tf_3_6_10 : Adj17 3 6 -> Adj17 6 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 10. assume H3: Adj17 3 10.
exact Adj17_not_3_10 H3.
Qed.

Theorem tf_3_6_11 : Adj17 3 6 -> Adj17 6 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 11. assume H3: Adj17 3 11.
exact Adj17_not_3_11 H3.
Qed.

Theorem tf_3_6_12 : Adj17 3 6 -> Adj17 6 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 12. assume H3: Adj17 3 12.
exact Adj17_not_3_12 H3.
Qed.

Theorem tf_3_6_13 : Adj17 3 6 -> Adj17 6 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 13. assume H3: Adj17 3 13.
exact Adj17_not_6_13 H2.
Qed.

Theorem tf_3_6_14 : Adj17 3 6 -> Adj17 6 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 14. assume H3: Adj17 3 14.
exact Adj17_not_3_14 H3.
Qed.

Theorem tf_3_6_15 : Adj17 3 6 -> Adj17 6 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 15. assume H3: Adj17 3 15.
exact Adj17_not_6_15 H2.
Qed.

Theorem tf_3_6_16 : Adj17 3 6 -> Adj17 6 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 6. assume H2: Adj17 6 16. assume H3: Adj17 3 16.
exact Adj17_not_6_16 H2.
Qed.

Theorem tf_3_7_0 : Adj17 3 7 -> Adj17 7 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 0. assume H3: Adj17 3 0.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_1 : Adj17 3 7 -> Adj17 7 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 1. assume H3: Adj17 3 1.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_2 : Adj17 3 7 -> Adj17 7 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 2. assume H3: Adj17 3 2.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_3 : Adj17 3 7 -> Adj17 7 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_7_4 : Adj17 3 7 -> Adj17 7 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 4. assume H3: Adj17 3 4.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_5 : Adj17 3 7 -> Adj17 7 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 5. assume H3: Adj17 3 5.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_6 : Adj17 3 7 -> Adj17 7 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 6. assume H3: Adj17 3 6.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_7 : Adj17 3 7 -> Adj17 7 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 7. assume H3: Adj17 3 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_3_7_8 : Adj17 3 7 -> Adj17 7 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 8. assume H3: Adj17 3 8.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_9 : Adj17 3 7 -> Adj17 7 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 9. assume H3: Adj17 3 9.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_10 : Adj17 3 7 -> Adj17 7 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 10. assume H3: Adj17 3 10.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_11 : Adj17 3 7 -> Adj17 7 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 11. assume H3: Adj17 3 11.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_12 : Adj17 3 7 -> Adj17 7 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 12. assume H3: Adj17 3 12.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_13 : Adj17 3 7 -> Adj17 7 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 13. assume H3: Adj17 3 13.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_14 : Adj17 3 7 -> Adj17 7 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 14. assume H3: Adj17 3 14.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_15 : Adj17 3 7 -> Adj17 7 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 15. assume H3: Adj17 3 15.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_7_16 : Adj17 3 7 -> Adj17 7 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 7. assume H2: Adj17 7 16. assume H3: Adj17 3 16.
exact Adj17_not_3_7 H1.
Qed.

Theorem tf_3_8_0 : Adj17 3 8 -> Adj17 8 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 0. assume H3: Adj17 3 0.
exact Adj17_not_8_0 H2.
Qed.

Theorem tf_3_8_1 : Adj17 3 8 -> Adj17 8 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 1. assume H3: Adj17 3 1.
exact Adj17_not_8_1 H2.
Qed.

Theorem tf_3_8_2 : Adj17 3 8 -> Adj17 8 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 2. assume H3: Adj17 3 2.
exact Adj17_not_3_2 H3.
Qed.

Theorem tf_3_8_3 : Adj17 3 8 -> Adj17 8 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_8_4 : Adj17 3 8 -> Adj17 8 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 4. assume H3: Adj17 3 4.
exact Adj17_not_8_4 H2.
Qed.

Theorem tf_3_8_5 : Adj17 3 8 -> Adj17 8 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 5. assume H3: Adj17 3 5.
exact Adj17_not_8_5 H2.
Qed.

Theorem tf_3_8_6 : Adj17 3 8 -> Adj17 8 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 6. assume H3: Adj17 3 6.
exact Adj17_not_8_6 H2.
Qed.

Theorem tf_3_8_7 : Adj17 3 8 -> Adj17 8 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 7. assume H3: Adj17 3 7.
exact Adj17_not_8_7 H2.
Qed.

Theorem tf_3_8_8 : Adj17 3 8 -> Adj17 8 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 8. assume H3: Adj17 3 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_3_8_9 : Adj17 3 8 -> Adj17 8 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 9. assume H3: Adj17 3 9.
exact Adj17_not_3_9 H3.
Qed.

Theorem tf_3_8_10 : Adj17 3 8 -> Adj17 8 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 10. assume H3: Adj17 3 10.
exact Adj17_not_8_10 H2.
Qed.

Theorem tf_3_8_11 : Adj17 3 8 -> Adj17 8 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 11. assume H3: Adj17 3 11.
exact Adj17_not_3_11 H3.
Qed.

Theorem tf_3_8_12 : Adj17 3 8 -> Adj17 8 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 12. assume H3: Adj17 3 12.
exact Adj17_not_8_12 H2.
Qed.

Theorem tf_3_8_13 : Adj17 3 8 -> Adj17 8 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 13. assume H3: Adj17 3 13.
exact Adj17_not_8_13 H2.
Qed.

Theorem tf_3_8_14 : Adj17 3 8 -> Adj17 8 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 14. assume H3: Adj17 3 14.
exact Adj17_not_3_14 H3.
Qed.

Theorem tf_3_8_15 : Adj17 3 8 -> Adj17 8 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 15. assume H3: Adj17 3 15.
exact Adj17_not_8_15 H2.
Qed.

Theorem tf_3_8_16 : Adj17 3 8 -> Adj17 8 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 8. assume H2: Adj17 8 16. assume H3: Adj17 3 16.
exact Adj17_not_8_16 H2.
Qed.

Theorem tf_3_9_0 : Adj17 3 9 -> Adj17 9 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 0. assume H3: Adj17 3 0.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_1 : Adj17 3 9 -> Adj17 9 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 1. assume H3: Adj17 3 1.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_2 : Adj17 3 9 -> Adj17 9 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 2. assume H3: Adj17 3 2.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_3 : Adj17 3 9 -> Adj17 9 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_9_4 : Adj17 3 9 -> Adj17 9 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 4. assume H3: Adj17 3 4.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_5 : Adj17 3 9 -> Adj17 9 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 5. assume H3: Adj17 3 5.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_6 : Adj17 3 9 -> Adj17 9 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 6. assume H3: Adj17 3 6.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_7 : Adj17 3 9 -> Adj17 9 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 7. assume H3: Adj17 3 7.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_8 : Adj17 3 9 -> Adj17 9 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 8. assume H3: Adj17 3 8.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_9 : Adj17 3 9 -> Adj17 9 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 9. assume H3: Adj17 3 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_3_9_10 : Adj17 3 9 -> Adj17 9 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 10. assume H3: Adj17 3 10.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_11 : Adj17 3 9 -> Adj17 9 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 11. assume H3: Adj17 3 11.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_12 : Adj17 3 9 -> Adj17 9 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 12. assume H3: Adj17 3 12.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_13 : Adj17 3 9 -> Adj17 9 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 13. assume H3: Adj17 3 13.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_14 : Adj17 3 9 -> Adj17 9 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 14. assume H3: Adj17 3 14.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_15 : Adj17 3 9 -> Adj17 9 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 15. assume H3: Adj17 3 15.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_9_16 : Adj17 3 9 -> Adj17 9 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 9. assume H2: Adj17 9 16. assume H3: Adj17 3 16.
exact Adj17_not_3_9 H1.
Qed.

Theorem tf_3_10_0 : Adj17 3 10 -> Adj17 10 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 0. assume H3: Adj17 3 0.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_1 : Adj17 3 10 -> Adj17 10 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 1. assume H3: Adj17 3 1.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_2 : Adj17 3 10 -> Adj17 10 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 2. assume H3: Adj17 3 2.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_3 : Adj17 3 10 -> Adj17 10 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_10_4 : Adj17 3 10 -> Adj17 10 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 4. assume H3: Adj17 3 4.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_5 : Adj17 3 10 -> Adj17 10 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 5. assume H3: Adj17 3 5.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_6 : Adj17 3 10 -> Adj17 10 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 6. assume H3: Adj17 3 6.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_7 : Adj17 3 10 -> Adj17 10 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 7. assume H3: Adj17 3 7.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_8 : Adj17 3 10 -> Adj17 10 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 8. assume H3: Adj17 3 8.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_9 : Adj17 3 10 -> Adj17 10 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 9. assume H3: Adj17 3 9.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_10 : Adj17 3 10 -> Adj17 10 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 10. assume H3: Adj17 3 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_3_10_11 : Adj17 3 10 -> Adj17 10 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 11. assume H3: Adj17 3 11.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_12 : Adj17 3 10 -> Adj17 10 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 12. assume H3: Adj17 3 12.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_13 : Adj17 3 10 -> Adj17 10 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 13. assume H3: Adj17 3 13.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_14 : Adj17 3 10 -> Adj17 10 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 14. assume H3: Adj17 3 14.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_15 : Adj17 3 10 -> Adj17 10 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 15. assume H3: Adj17 3 15.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_10_16 : Adj17 3 10 -> Adj17 10 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 10. assume H2: Adj17 10 16. assume H3: Adj17 3 16.
exact Adj17_not_3_10 H1.
Qed.

Theorem tf_3_11_0 : Adj17 3 11 -> Adj17 11 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 0. assume H3: Adj17 3 0.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_1 : Adj17 3 11 -> Adj17 11 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 1. assume H3: Adj17 3 1.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_2 : Adj17 3 11 -> Adj17 11 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 2. assume H3: Adj17 3 2.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_3 : Adj17 3 11 -> Adj17 11 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_11_4 : Adj17 3 11 -> Adj17 11 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 4. assume H3: Adj17 3 4.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_5 : Adj17 3 11 -> Adj17 11 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 5. assume H3: Adj17 3 5.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_6 : Adj17 3 11 -> Adj17 11 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 6. assume H3: Adj17 3 6.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_7 : Adj17 3 11 -> Adj17 11 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 7. assume H3: Adj17 3 7.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_8 : Adj17 3 11 -> Adj17 11 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 8. assume H3: Adj17 3 8.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_9 : Adj17 3 11 -> Adj17 11 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 9. assume H3: Adj17 3 9.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_10 : Adj17 3 11 -> Adj17 11 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 10. assume H3: Adj17 3 10.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_11 : Adj17 3 11 -> Adj17 11 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 11. assume H3: Adj17 3 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_3_11_12 : Adj17 3 11 -> Adj17 11 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 12. assume H3: Adj17 3 12.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_13 : Adj17 3 11 -> Adj17 11 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 13. assume H3: Adj17 3 13.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_14 : Adj17 3 11 -> Adj17 11 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 14. assume H3: Adj17 3 14.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_15 : Adj17 3 11 -> Adj17 11 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 15. assume H3: Adj17 3 15.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_11_16 : Adj17 3 11 -> Adj17 11 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 11. assume H2: Adj17 11 16. assume H3: Adj17 3 16.
exact Adj17_not_3_11 H1.
Qed.

Theorem tf_3_12_0 : Adj17 3 12 -> Adj17 12 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 0. assume H3: Adj17 3 0.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_1 : Adj17 3 12 -> Adj17 12 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 1. assume H3: Adj17 3 1.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_2 : Adj17 3 12 -> Adj17 12 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 2. assume H3: Adj17 3 2.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_3 : Adj17 3 12 -> Adj17 12 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_12_4 : Adj17 3 12 -> Adj17 12 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 4. assume H3: Adj17 3 4.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_5 : Adj17 3 12 -> Adj17 12 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 5. assume H3: Adj17 3 5.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_6 : Adj17 3 12 -> Adj17 12 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 6. assume H3: Adj17 3 6.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_7 : Adj17 3 12 -> Adj17 12 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 7. assume H3: Adj17 3 7.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_8 : Adj17 3 12 -> Adj17 12 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 8. assume H3: Adj17 3 8.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_9 : Adj17 3 12 -> Adj17 12 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 9. assume H3: Adj17 3 9.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_10 : Adj17 3 12 -> Adj17 12 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 10. assume H3: Adj17 3 10.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_11 : Adj17 3 12 -> Adj17 12 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 11. assume H3: Adj17 3 11.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_12 : Adj17 3 12 -> Adj17 12 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 12. assume H3: Adj17 3 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_3_12_13 : Adj17 3 12 -> Adj17 12 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 13. assume H3: Adj17 3 13.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_14 : Adj17 3 12 -> Adj17 12 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 14. assume H3: Adj17 3 14.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_15 : Adj17 3 12 -> Adj17 12 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 15. assume H3: Adj17 3 15.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_12_16 : Adj17 3 12 -> Adj17 12 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 12. assume H2: Adj17 12 16. assume H3: Adj17 3 16.
exact Adj17_not_3_12 H1.
Qed.

Theorem tf_3_13_0 : Adj17 3 13 -> Adj17 13 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 0. assume H3: Adj17 3 0.
exact Adj17_not_13_0 H2.
Qed.

Theorem tf_3_13_1 : Adj17 3 13 -> Adj17 13 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 1. assume H3: Adj17 3 1.
exact Adj17_not_3_1 H3.
Qed.

Theorem tf_3_13_2 : Adj17 3 13 -> Adj17 13 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 2. assume H3: Adj17 3 2.
exact Adj17_not_13_2 H2.
Qed.

Theorem tf_3_13_3 : Adj17 3 13 -> Adj17 13 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_13_4 : Adj17 3 13 -> Adj17 13 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 4. assume H3: Adj17 3 4.
exact Adj17_not_13_4 H2.
Qed.

Theorem tf_3_13_5 : Adj17 3 13 -> Adj17 13 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 5. assume H3: Adj17 3 5.
exact Adj17_not_3_5 H3.
Qed.

Theorem tf_3_13_6 : Adj17 3 13 -> Adj17 13 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 6. assume H3: Adj17 3 6.
exact Adj17_not_13_6 H2.
Qed.

Theorem tf_3_13_7 : Adj17 3 13 -> Adj17 13 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 7. assume H3: Adj17 3 7.
exact Adj17_not_13_7 H2.
Qed.

Theorem tf_3_13_8 : Adj17 3 13 -> Adj17 13 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 8. assume H3: Adj17 3 8.
exact Adj17_not_13_8 H2.
Qed.

Theorem tf_3_13_9 : Adj17 3 13 -> Adj17 13 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 9. assume H3: Adj17 3 9.
exact Adj17_not_13_9 H2.
Qed.

Theorem tf_3_13_10 : Adj17 3 13 -> Adj17 13 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 10. assume H3: Adj17 3 10.
exact Adj17_not_13_10 H2.
Qed.

Theorem tf_3_13_11 : Adj17 3 13 -> Adj17 13 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 11. assume H3: Adj17 3 11.
exact Adj17_not_13_11 H2.
Qed.

Theorem tf_3_13_12 : Adj17 3 13 -> Adj17 13 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 12. assume H3: Adj17 3 12.
exact Adj17_not_3_12 H3.
Qed.

Theorem tf_3_13_13 : Adj17 3 13 -> Adj17 13 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 13. assume H3: Adj17 3 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_3_13_14 : Adj17 3 13 -> Adj17 13 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 14. assume H3: Adj17 3 14.
exact Adj17_not_3_14 H3.
Qed.

Theorem tf_3_13_15 : Adj17 3 13 -> Adj17 13 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 15. assume H3: Adj17 3 15.
exact Adj17_not_13_15 H2.
Qed.

Theorem tf_3_13_16 : Adj17 3 13 -> Adj17 13 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 13. assume H2: Adj17 13 16. assume H3: Adj17 3 16.
exact Adj17_not_13_16 H2.
Qed.

Theorem tf_3_14_0 : Adj17 3 14 -> Adj17 14 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 0. assume H3: Adj17 3 0.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_1 : Adj17 3 14 -> Adj17 14 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 1. assume H3: Adj17 3 1.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_2 : Adj17 3 14 -> Adj17 14 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 2. assume H3: Adj17 3 2.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_3 : Adj17 3 14 -> Adj17 14 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_14_4 : Adj17 3 14 -> Adj17 14 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 4. assume H3: Adj17 3 4.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_5 : Adj17 3 14 -> Adj17 14 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 5. assume H3: Adj17 3 5.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_6 : Adj17 3 14 -> Adj17 14 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 6. assume H3: Adj17 3 6.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_7 : Adj17 3 14 -> Adj17 14 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 7. assume H3: Adj17 3 7.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_8 : Adj17 3 14 -> Adj17 14 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 8. assume H3: Adj17 3 8.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_9 : Adj17 3 14 -> Adj17 14 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 9. assume H3: Adj17 3 9.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_10 : Adj17 3 14 -> Adj17 14 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 10. assume H3: Adj17 3 10.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_11 : Adj17 3 14 -> Adj17 14 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 11. assume H3: Adj17 3 11.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_12 : Adj17 3 14 -> Adj17 14 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 12. assume H3: Adj17 3 12.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_13 : Adj17 3 14 -> Adj17 14 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 13. assume H3: Adj17 3 13.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_14 : Adj17 3 14 -> Adj17 14 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 14. assume H3: Adj17 3 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_3_14_15 : Adj17 3 14 -> Adj17 14 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 15. assume H3: Adj17 3 15.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_14_16 : Adj17 3 14 -> Adj17 14 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 14. assume H2: Adj17 14 16. assume H3: Adj17 3 16.
exact Adj17_not_3_14 H1.
Qed.

Theorem tf_3_15_0 : Adj17 3 15 -> Adj17 15 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 0. assume H3: Adj17 3 0.
exact Adj17_not_3_0 H3.
Qed.

Theorem tf_3_15_1 : Adj17 3 15 -> Adj17 15 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 1. assume H3: Adj17 3 1.
exact Adj17_not_15_1 H2.
Qed.

Theorem tf_3_15_2 : Adj17 3 15 -> Adj17 15 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 2. assume H3: Adj17 3 2.
exact Adj17_not_3_2 H3.
Qed.

Theorem tf_3_15_3 : Adj17 3 15 -> Adj17 15 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_15_4 : Adj17 3 15 -> Adj17 15 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 4. assume H3: Adj17 3 4.
exact Adj17_not_15_4 H2.
Qed.

Theorem tf_3_15_5 : Adj17 3 15 -> Adj17 15 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 5. assume H3: Adj17 3 5.
exact Adj17_not_15_5 H2.
Qed.

Theorem tf_3_15_6 : Adj17 3 15 -> Adj17 15 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 6. assume H3: Adj17 3 6.
exact Adj17_not_15_6 H2.
Qed.

Theorem tf_3_15_7 : Adj17 3 15 -> Adj17 15 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 7. assume H3: Adj17 3 7.
exact Adj17_not_3_7 H3.
Qed.

Theorem tf_3_15_8 : Adj17 3 15 -> Adj17 15 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 8. assume H3: Adj17 3 8.
exact Adj17_not_15_8 H2.
Qed.

Theorem tf_3_15_9 : Adj17 3 15 -> Adj17 15 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 9. assume H3: Adj17 3 9.
exact Adj17_not_15_9 H2.
Qed.

Theorem tf_3_15_10 : Adj17 3 15 -> Adj17 15 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 10. assume H3: Adj17 3 10.
exact Adj17_not_15_10 H2.
Qed.

Theorem tf_3_15_11 : Adj17 3 15 -> Adj17 15 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 11. assume H3: Adj17 3 11.
exact Adj17_not_3_11 H3.
Qed.

Theorem tf_3_15_12 : Adj17 3 15 -> Adj17 15 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 12. assume H3: Adj17 3 12.
exact Adj17_not_15_12 H2.
Qed.

Theorem tf_3_15_13 : Adj17 3 15 -> Adj17 15 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 13. assume H3: Adj17 3 13.
exact Adj17_not_15_13 H2.
Qed.

Theorem tf_3_15_14 : Adj17 3 15 -> Adj17 15 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 14. assume H3: Adj17 3 14.
exact Adj17_not_15_14 H2.
Qed.

Theorem tf_3_15_15 : Adj17 3 15 -> Adj17 15 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 15. assume H3: Adj17 3 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_3_15_16 : Adj17 3 15 -> Adj17 15 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 15. assume H2: Adj17 15 16. assume H3: Adj17 3 16.
exact Adj17_not_15_16 H2.
Qed.

Theorem tf_3_16_0 : Adj17 3 16 -> Adj17 16 0 -> Adj17 3 0 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 0. assume H3: Adj17 3 0.
exact Adj17_not_3_0 H3.
Qed.

Theorem tf_3_16_1 : Adj17 3 16 -> Adj17 16 1 -> Adj17 3 1 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 1. assume H3: Adj17 3 1.
exact Adj17_not_3_1 H3.
Qed.

Theorem tf_3_16_2 : Adj17 3 16 -> Adj17 16 2 -> Adj17 3 2 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 2. assume H3: Adj17 3 2.
exact Adj17_not_16_2 H2.
Qed.

Theorem tf_3_16_3 : Adj17 3 16 -> Adj17 16 3 -> Adj17 3 3 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 3. assume H3: Adj17 3 3.
exact Adj17_not_3_3 H3.
Qed.

Theorem tf_3_16_4 : Adj17 3 16 -> Adj17 16 4 -> Adj17 3 4 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 4. assume H3: Adj17 3 4.
exact Adj17_not_3_4 H3.
Qed.

Theorem tf_3_16_5 : Adj17 3 16 -> Adj17 16 5 -> Adj17 3 5 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 5. assume H3: Adj17 3 5.
exact Adj17_not_16_5 H2.
Qed.

Theorem tf_3_16_6 : Adj17 3 16 -> Adj17 16 6 -> Adj17 3 6 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 6. assume H3: Adj17 3 6.
exact Adj17_not_16_6 H2.
Qed.

Theorem tf_3_16_7 : Adj17 3 16 -> Adj17 16 7 -> Adj17 3 7 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 7. assume H3: Adj17 3 7.
exact Adj17_not_16_7 H2.
Qed.

Theorem tf_3_16_8 : Adj17 3 16 -> Adj17 16 8 -> Adj17 3 8 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 8. assume H3: Adj17 3 8.
exact Adj17_not_16_8 H2.
Qed.

Theorem tf_3_16_9 : Adj17 3 16 -> Adj17 16 9 -> Adj17 3 9 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 9. assume H3: Adj17 3 9.
exact Adj17_not_16_9 H2.
Qed.

Theorem tf_3_16_10 : Adj17 3 16 -> Adj17 16 10 -> Adj17 3 10 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 10. assume H3: Adj17 3 10.
exact Adj17_not_3_10 H3.
Qed.

Theorem tf_3_16_11 : Adj17 3 16 -> Adj17 16 11 -> Adj17 3 11 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 11. assume H3: Adj17 3 11.
exact Adj17_not_16_11 H2.
Qed.

Theorem tf_3_16_12 : Adj17 3 16 -> Adj17 16 12 -> Adj17 3 12 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 12. assume H3: Adj17 3 12.
exact Adj17_not_16_12 H2.
Qed.

Theorem tf_3_16_13 : Adj17 3 16 -> Adj17 16 13 -> Adj17 3 13 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 13. assume H3: Adj17 3 13.
exact Adj17_not_16_13 H2.
Qed.

Theorem tf_3_16_14 : Adj17 3 16 -> Adj17 16 14 -> Adj17 3 14 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 14. assume H3: Adj17 3 14.
exact Adj17_not_16_14 H2.
Qed.

Theorem tf_3_16_15 : Adj17 3 16 -> Adj17 16 15 -> Adj17 3 15 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 15. assume H3: Adj17 3 15.
exact Adj17_not_16_15 H2.
Qed.

Theorem tf_3_16_16 : Adj17 3 16 -> Adj17 16 16 -> Adj17 3 16 -> False.
assume H1: Adj17 3 16. assume H2: Adj17 16 16. assume H3: Adj17 3 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_4_0_0 : Adj17 4 0 -> Adj17 0 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 0. assume H3: Adj17 4 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_4_0_1 : Adj17 4 0 -> Adj17 0 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 1. assume H3: Adj17 4 1.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_2 : Adj17 4 0 -> Adj17 0 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 2. assume H3: Adj17 4 2.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_3 : Adj17 4 0 -> Adj17 0 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 3. assume H3: Adj17 4 3.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_4 : Adj17 4 0 -> Adj17 0 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_0_5 : Adj17 4 0 -> Adj17 0 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 5. assume H3: Adj17 4 5.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_6 : Adj17 4 0 -> Adj17 0 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 6. assume H3: Adj17 4 6.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_7 : Adj17 4 0 -> Adj17 0 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 7. assume H3: Adj17 4 7.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_8 : Adj17 4 0 -> Adj17 0 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 8. assume H3: Adj17 4 8.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_9 : Adj17 4 0 -> Adj17 0 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 9. assume H3: Adj17 4 9.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_10 : Adj17 4 0 -> Adj17 0 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 10. assume H3: Adj17 4 10.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_11 : Adj17 4 0 -> Adj17 0 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 11. assume H3: Adj17 4 11.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_12 : Adj17 4 0 -> Adj17 0 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 12. assume H3: Adj17 4 12.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_13 : Adj17 4 0 -> Adj17 0 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 13. assume H3: Adj17 4 13.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_14 : Adj17 4 0 -> Adj17 0 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 14. assume H3: Adj17 4 14.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_15 : Adj17 4 0 -> Adj17 0 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 15. assume H3: Adj17 4 15.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_0_16 : Adj17 4 0 -> Adj17 0 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 0. assume H2: Adj17 0 16. assume H3: Adj17 4 16.
exact Adj17_not_4_0 H1.
Qed.

Theorem tf_4_1_0 : Adj17 4 1 -> Adj17 1 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 0. assume H3: Adj17 4 0.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_1 : Adj17 4 1 -> Adj17 1 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 1. assume H3: Adj17 4 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_4_1_2 : Adj17 4 1 -> Adj17 1 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 2. assume H3: Adj17 4 2.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_3 : Adj17 4 1 -> Adj17 1 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 3. assume H3: Adj17 4 3.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_4 : Adj17 4 1 -> Adj17 1 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_1_5 : Adj17 4 1 -> Adj17 1 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 5. assume H3: Adj17 4 5.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_6 : Adj17 4 1 -> Adj17 1 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 6. assume H3: Adj17 4 6.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_7 : Adj17 4 1 -> Adj17 1 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 7. assume H3: Adj17 4 7.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_8 : Adj17 4 1 -> Adj17 1 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 8. assume H3: Adj17 4 8.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_9 : Adj17 4 1 -> Adj17 1 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 9. assume H3: Adj17 4 9.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_10 : Adj17 4 1 -> Adj17 1 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 10. assume H3: Adj17 4 10.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_11 : Adj17 4 1 -> Adj17 1 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 11. assume H3: Adj17 4 11.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_12 : Adj17 4 1 -> Adj17 1 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 12. assume H3: Adj17 4 12.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_13 : Adj17 4 1 -> Adj17 1 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 13. assume H3: Adj17 4 13.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_14 : Adj17 4 1 -> Adj17 1 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 14. assume H3: Adj17 4 14.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_15 : Adj17 4 1 -> Adj17 1 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 15. assume H3: Adj17 4 15.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_1_16 : Adj17 4 1 -> Adj17 1 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 1. assume H2: Adj17 1 16. assume H3: Adj17 4 16.
exact Adj17_not_4_1 H1.
Qed.

Theorem tf_4_2_0 : Adj17 4 2 -> Adj17 2 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 0. assume H3: Adj17 4 0.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_1 : Adj17 4 2 -> Adj17 2 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 1. assume H3: Adj17 4 1.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_2 : Adj17 4 2 -> Adj17 2 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 2. assume H3: Adj17 4 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_4_2_3 : Adj17 4 2 -> Adj17 2 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 3. assume H3: Adj17 4 3.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_4 : Adj17 4 2 -> Adj17 2 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_2_5 : Adj17 4 2 -> Adj17 2 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 5. assume H3: Adj17 4 5.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_6 : Adj17 4 2 -> Adj17 2 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 6. assume H3: Adj17 4 6.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_7 : Adj17 4 2 -> Adj17 2 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 7. assume H3: Adj17 4 7.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_8 : Adj17 4 2 -> Adj17 2 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 8. assume H3: Adj17 4 8.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_9 : Adj17 4 2 -> Adj17 2 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 9. assume H3: Adj17 4 9.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_10 : Adj17 4 2 -> Adj17 2 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 10. assume H3: Adj17 4 10.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_11 : Adj17 4 2 -> Adj17 2 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 11. assume H3: Adj17 4 11.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_12 : Adj17 4 2 -> Adj17 2 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 12. assume H3: Adj17 4 12.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_13 : Adj17 4 2 -> Adj17 2 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 13. assume H3: Adj17 4 13.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_14 : Adj17 4 2 -> Adj17 2 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 14. assume H3: Adj17 4 14.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_15 : Adj17 4 2 -> Adj17 2 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 15. assume H3: Adj17 4 15.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_2_16 : Adj17 4 2 -> Adj17 2 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 2. assume H2: Adj17 2 16. assume H3: Adj17 4 16.
exact Adj17_not_4_2 H1.
Qed.

Theorem tf_4_3_0 : Adj17 4 3 -> Adj17 3 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 0. assume H3: Adj17 4 0.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_1 : Adj17 4 3 -> Adj17 3 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 1. assume H3: Adj17 4 1.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_2 : Adj17 4 3 -> Adj17 3 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 2. assume H3: Adj17 4 2.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_3 : Adj17 4 3 -> Adj17 3 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 3. assume H3: Adj17 4 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_4_3_4 : Adj17 4 3 -> Adj17 3 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_3_5 : Adj17 4 3 -> Adj17 3 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 5. assume H3: Adj17 4 5.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_6 : Adj17 4 3 -> Adj17 3 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 6. assume H3: Adj17 4 6.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_7 : Adj17 4 3 -> Adj17 3 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 7. assume H3: Adj17 4 7.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_8 : Adj17 4 3 -> Adj17 3 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 8. assume H3: Adj17 4 8.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_9 : Adj17 4 3 -> Adj17 3 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 9. assume H3: Adj17 4 9.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_10 : Adj17 4 3 -> Adj17 3 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 10. assume H3: Adj17 4 10.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_11 : Adj17 4 3 -> Adj17 3 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 11. assume H3: Adj17 4 11.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_12 : Adj17 4 3 -> Adj17 3 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 12. assume H3: Adj17 4 12.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_13 : Adj17 4 3 -> Adj17 3 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 13. assume H3: Adj17 4 13.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_14 : Adj17 4 3 -> Adj17 3 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 14. assume H3: Adj17 4 14.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_15 : Adj17 4 3 -> Adj17 3 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 15. assume H3: Adj17 4 15.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_3_16 : Adj17 4 3 -> Adj17 3 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 3. assume H2: Adj17 3 16. assume H3: Adj17 4 16.
exact Adj17_not_4_3 H1.
Qed.

Theorem tf_4_4_0 : Adj17 4 4 -> Adj17 4 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 0. assume H3: Adj17 4 0.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_1 : Adj17 4 4 -> Adj17 4 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 1. assume H3: Adj17 4 1.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_2 : Adj17 4 4 -> Adj17 4 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 2. assume H3: Adj17 4 2.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_3 : Adj17 4 4 -> Adj17 4 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 3. assume H3: Adj17 4 3.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_4 : Adj17 4 4 -> Adj17 4 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_5 : Adj17 4 4 -> Adj17 4 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 5. assume H3: Adj17 4 5.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_6 : Adj17 4 4 -> Adj17 4 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 6. assume H3: Adj17 4 6.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_7 : Adj17 4 4 -> Adj17 4 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 7. assume H3: Adj17 4 7.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_8 : Adj17 4 4 -> Adj17 4 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 8. assume H3: Adj17 4 8.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_9 : Adj17 4 4 -> Adj17 4 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 9. assume H3: Adj17 4 9.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_10 : Adj17 4 4 -> Adj17 4 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 10. assume H3: Adj17 4 10.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_11 : Adj17 4 4 -> Adj17 4 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 11. assume H3: Adj17 4 11.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_12 : Adj17 4 4 -> Adj17 4 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 12. assume H3: Adj17 4 12.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_13 : Adj17 4 4 -> Adj17 4 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 13. assume H3: Adj17 4 13.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_14 : Adj17 4 4 -> Adj17 4 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 14. assume H3: Adj17 4 14.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_15 : Adj17 4 4 -> Adj17 4 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 15. assume H3: Adj17 4 15.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_4_16 : Adj17 4 4 -> Adj17 4 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 4. assume H2: Adj17 4 16. assume H3: Adj17 4 16.
exact Adj17_not_4_4 H1.
Qed.

Theorem tf_4_5_0 : Adj17 4 5 -> Adj17 5 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 0. assume H3: Adj17 4 0.
exact Adj17_not_5_0 H2.
Qed.

Theorem tf_4_5_1 : Adj17 4 5 -> Adj17 5 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 1. assume H3: Adj17 4 1.
exact Adj17_not_5_1 H2.
Qed.

Theorem tf_4_5_2 : Adj17 4 5 -> Adj17 5 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 2. assume H3: Adj17 4 2.
exact Adj17_not_5_2 H2.
Qed.

Theorem tf_4_5_3 : Adj17 4 5 -> Adj17 5 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 3. assume H3: Adj17 4 3.
exact Adj17_not_5_3 H2.
Qed.

Theorem tf_4_5_4 : Adj17 4 5 -> Adj17 5 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_5_5 : Adj17 4 5 -> Adj17 5 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 5. assume H3: Adj17 4 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_4_5_6 : Adj17 4 5 -> Adj17 5 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 6. assume H3: Adj17 4 6.
exact Adj17_not_5_6 H2.
Qed.

Theorem tf_4_5_7 : Adj17 4 5 -> Adj17 5 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 7. assume H3: Adj17 4 7.
exact Adj17_not_5_7 H2.
Qed.

Theorem tf_4_5_8 : Adj17 4 5 -> Adj17 5 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 8. assume H3: Adj17 4 8.
exact Adj17_not_5_8 H2.
Qed.

Theorem tf_4_5_9 : Adj17 4 5 -> Adj17 5 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 9. assume H3: Adj17 4 9.
exact Adj17_not_4_9 H3.
Qed.

Theorem tf_4_5_10 : Adj17 4 5 -> Adj17 5 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 10. assume H3: Adj17 4 10.
exact Adj17_not_4_10 H3.
Qed.

Theorem tf_4_5_11 : Adj17 4 5 -> Adj17 5 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 11. assume H3: Adj17 4 11.
exact Adj17_not_4_11 H3.
Qed.

Theorem tf_4_5_12 : Adj17 4 5 -> Adj17 5 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 12. assume H3: Adj17 4 12.
exact Adj17_not_5_12 H2.
Qed.

Theorem tf_4_5_13 : Adj17 4 5 -> Adj17 5 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 13. assume H3: Adj17 4 13.
exact Adj17_not_4_13 H3.
Qed.

Theorem tf_4_5_14 : Adj17 4 5 -> Adj17 5 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 14. assume H3: Adj17 4 14.
exact Adj17_not_5_14 H2.
Qed.

Theorem tf_4_5_15 : Adj17 4 5 -> Adj17 5 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 15. assume H3: Adj17 4 15.
exact Adj17_not_5_15 H2.
Qed.

Theorem tf_4_5_16 : Adj17 4 5 -> Adj17 5 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 5. assume H2: Adj17 5 16. assume H3: Adj17 4 16.
exact Adj17_not_5_16 H2.
Qed.

Theorem tf_4_6_0 : Adj17 4 6 -> Adj17 6 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 0. assume H3: Adj17 4 0.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_1 : Adj17 4 6 -> Adj17 6 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 1. assume H3: Adj17 4 1.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_2 : Adj17 4 6 -> Adj17 6 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 2. assume H3: Adj17 4 2.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_3 : Adj17 4 6 -> Adj17 6 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 3. assume H3: Adj17 4 3.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_4 : Adj17 4 6 -> Adj17 6 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_6_5 : Adj17 4 6 -> Adj17 6 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 5. assume H3: Adj17 4 5.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_6 : Adj17 4 6 -> Adj17 6 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 6. assume H3: Adj17 4 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_4_6_7 : Adj17 4 6 -> Adj17 6 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 7. assume H3: Adj17 4 7.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_8 : Adj17 4 6 -> Adj17 6 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 8. assume H3: Adj17 4 8.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_9 : Adj17 4 6 -> Adj17 6 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 9. assume H3: Adj17 4 9.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_10 : Adj17 4 6 -> Adj17 6 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 10. assume H3: Adj17 4 10.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_11 : Adj17 4 6 -> Adj17 6 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 11. assume H3: Adj17 4 11.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_12 : Adj17 4 6 -> Adj17 6 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 12. assume H3: Adj17 4 12.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_13 : Adj17 4 6 -> Adj17 6 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 13. assume H3: Adj17 4 13.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_14 : Adj17 4 6 -> Adj17 6 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 14. assume H3: Adj17 4 14.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_15 : Adj17 4 6 -> Adj17 6 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 15. assume H3: Adj17 4 15.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_6_16 : Adj17 4 6 -> Adj17 6 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 6. assume H2: Adj17 6 16. assume H3: Adj17 4 16.
exact Adj17_not_4_6 H1.
Qed.

Theorem tf_4_7_0 : Adj17 4 7 -> Adj17 7 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 0. assume H3: Adj17 4 0.
exact Adj17_not_7_0 H2.
Qed.

Theorem tf_4_7_1 : Adj17 4 7 -> Adj17 7 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 1. assume H3: Adj17 4 1.
exact Adj17_not_4_1 H3.
Qed.

Theorem tf_4_7_2 : Adj17 4 7 -> Adj17 7 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 2. assume H3: Adj17 4 2.
exact Adj17_not_7_2 H2.
Qed.

Theorem tf_4_7_3 : Adj17 4 7 -> Adj17 7 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 3. assume H3: Adj17 4 3.
exact Adj17_not_7_3 H2.
Qed.

Theorem tf_4_7_4 : Adj17 4 7 -> Adj17 7 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_7_5 : Adj17 4 7 -> Adj17 7 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 5. assume H3: Adj17 4 5.
exact Adj17_not_7_5 H2.
Qed.

Theorem tf_4_7_6 : Adj17 4 7 -> Adj17 7 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 6. assume H3: Adj17 4 6.
exact Adj17_not_7_6 H2.
Qed.

Theorem tf_4_7_7 : Adj17 4 7 -> Adj17 7 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 7. assume H3: Adj17 4 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_4_7_8 : Adj17 4 7 -> Adj17 7 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 8. assume H3: Adj17 4 8.
exact Adj17_not_7_8 H2.
Qed.

Theorem tf_4_7_9 : Adj17 4 7 -> Adj17 7 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 9. assume H3: Adj17 4 9.
exact Adj17_not_4_9 H3.
Qed.

Theorem tf_4_7_10 : Adj17 4 7 -> Adj17 7 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 10. assume H3: Adj17 4 10.
exact Adj17_not_4_10 H3.
Qed.

Theorem tf_4_7_11 : Adj17 4 7 -> Adj17 7 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 11. assume H3: Adj17 4 11.
exact Adj17_not_7_11 H2.
Qed.

Theorem tf_4_7_12 : Adj17 4 7 -> Adj17 7 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 12. assume H3: Adj17 4 12.
exact Adj17_not_7_12 H2.
Qed.

Theorem tf_4_7_13 : Adj17 4 7 -> Adj17 7 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 13. assume H3: Adj17 4 13.
exact Adj17_not_7_13 H2.
Qed.

Theorem tf_4_7_14 : Adj17 4 7 -> Adj17 7 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 14. assume H3: Adj17 4 14.
exact Adj17_not_7_14 H2.
Qed.

Theorem tf_4_7_15 : Adj17 4 7 -> Adj17 7 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 15. assume H3: Adj17 4 15.
exact Adj17_not_4_15 H3.
Qed.

Theorem tf_4_7_16 : Adj17 4 7 -> Adj17 7 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 7. assume H2: Adj17 7 16. assume H3: Adj17 4 16.
exact Adj17_not_7_16 H2.
Qed.

Theorem tf_4_8_0 : Adj17 4 8 -> Adj17 8 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 0. assume H3: Adj17 4 0.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_1 : Adj17 4 8 -> Adj17 8 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 1. assume H3: Adj17 4 1.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_2 : Adj17 4 8 -> Adj17 8 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 2. assume H3: Adj17 4 2.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_3 : Adj17 4 8 -> Adj17 8 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 3. assume H3: Adj17 4 3.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_4 : Adj17 4 8 -> Adj17 8 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_8_5 : Adj17 4 8 -> Adj17 8 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 5. assume H3: Adj17 4 5.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_6 : Adj17 4 8 -> Adj17 8 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 6. assume H3: Adj17 4 6.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_7 : Adj17 4 8 -> Adj17 8 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 7. assume H3: Adj17 4 7.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_8 : Adj17 4 8 -> Adj17 8 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 8. assume H3: Adj17 4 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_4_8_9 : Adj17 4 8 -> Adj17 8 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 9. assume H3: Adj17 4 9.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_10 : Adj17 4 8 -> Adj17 8 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 10. assume H3: Adj17 4 10.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_11 : Adj17 4 8 -> Adj17 8 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 11. assume H3: Adj17 4 11.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_12 : Adj17 4 8 -> Adj17 8 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 12. assume H3: Adj17 4 12.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_13 : Adj17 4 8 -> Adj17 8 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 13. assume H3: Adj17 4 13.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_14 : Adj17 4 8 -> Adj17 8 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 14. assume H3: Adj17 4 14.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_15 : Adj17 4 8 -> Adj17 8 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 15. assume H3: Adj17 4 15.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_8_16 : Adj17 4 8 -> Adj17 8 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 8. assume H2: Adj17 8 16. assume H3: Adj17 4 16.
exact Adj17_not_4_8 H1.
Qed.

Theorem tf_4_9_0 : Adj17 4 9 -> Adj17 9 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 0. assume H3: Adj17 4 0.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_1 : Adj17 4 9 -> Adj17 9 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 1. assume H3: Adj17 4 1.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_2 : Adj17 4 9 -> Adj17 9 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 2. assume H3: Adj17 4 2.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_3 : Adj17 4 9 -> Adj17 9 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 3. assume H3: Adj17 4 3.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_4 : Adj17 4 9 -> Adj17 9 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_9_5 : Adj17 4 9 -> Adj17 9 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 5. assume H3: Adj17 4 5.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_6 : Adj17 4 9 -> Adj17 9 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 6. assume H3: Adj17 4 6.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_7 : Adj17 4 9 -> Adj17 9 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 7. assume H3: Adj17 4 7.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_8 : Adj17 4 9 -> Adj17 9 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 8. assume H3: Adj17 4 8.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_9 : Adj17 4 9 -> Adj17 9 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 9. assume H3: Adj17 4 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_4_9_10 : Adj17 4 9 -> Adj17 9 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 10. assume H3: Adj17 4 10.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_11 : Adj17 4 9 -> Adj17 9 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 11. assume H3: Adj17 4 11.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_12 : Adj17 4 9 -> Adj17 9 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 12. assume H3: Adj17 4 12.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_13 : Adj17 4 9 -> Adj17 9 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 13. assume H3: Adj17 4 13.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_14 : Adj17 4 9 -> Adj17 9 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 14. assume H3: Adj17 4 14.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_15 : Adj17 4 9 -> Adj17 9 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 15. assume H3: Adj17 4 15.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_9_16 : Adj17 4 9 -> Adj17 9 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 9. assume H2: Adj17 9 16. assume H3: Adj17 4 16.
exact Adj17_not_4_9 H1.
Qed.

Theorem tf_4_10_0 : Adj17 4 10 -> Adj17 10 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 0. assume H3: Adj17 4 0.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_1 : Adj17 4 10 -> Adj17 10 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 1. assume H3: Adj17 4 1.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_2 : Adj17 4 10 -> Adj17 10 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 2. assume H3: Adj17 4 2.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_3 : Adj17 4 10 -> Adj17 10 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 3. assume H3: Adj17 4 3.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_4 : Adj17 4 10 -> Adj17 10 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_10_5 : Adj17 4 10 -> Adj17 10 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 5. assume H3: Adj17 4 5.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_6 : Adj17 4 10 -> Adj17 10 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 6. assume H3: Adj17 4 6.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_7 : Adj17 4 10 -> Adj17 10 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 7. assume H3: Adj17 4 7.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_8 : Adj17 4 10 -> Adj17 10 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 8. assume H3: Adj17 4 8.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_9 : Adj17 4 10 -> Adj17 10 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 9. assume H3: Adj17 4 9.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_10 : Adj17 4 10 -> Adj17 10 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 10. assume H3: Adj17 4 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_4_10_11 : Adj17 4 10 -> Adj17 10 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 11. assume H3: Adj17 4 11.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_12 : Adj17 4 10 -> Adj17 10 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 12. assume H3: Adj17 4 12.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_13 : Adj17 4 10 -> Adj17 10 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 13. assume H3: Adj17 4 13.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_14 : Adj17 4 10 -> Adj17 10 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 14. assume H3: Adj17 4 14.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_15 : Adj17 4 10 -> Adj17 10 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 15. assume H3: Adj17 4 15.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_10_16 : Adj17 4 10 -> Adj17 10 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 10. assume H2: Adj17 10 16. assume H3: Adj17 4 16.
exact Adj17_not_4_10 H1.
Qed.

Theorem tf_4_11_0 : Adj17 4 11 -> Adj17 11 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 0. assume H3: Adj17 4 0.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_1 : Adj17 4 11 -> Adj17 11 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 1. assume H3: Adj17 4 1.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_2 : Adj17 4 11 -> Adj17 11 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 2. assume H3: Adj17 4 2.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_3 : Adj17 4 11 -> Adj17 11 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 3. assume H3: Adj17 4 3.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_4 : Adj17 4 11 -> Adj17 11 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_11_5 : Adj17 4 11 -> Adj17 11 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 5. assume H3: Adj17 4 5.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_6 : Adj17 4 11 -> Adj17 11 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 6. assume H3: Adj17 4 6.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_7 : Adj17 4 11 -> Adj17 11 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 7. assume H3: Adj17 4 7.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_8 : Adj17 4 11 -> Adj17 11 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 8. assume H3: Adj17 4 8.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_9 : Adj17 4 11 -> Adj17 11 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 9. assume H3: Adj17 4 9.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_10 : Adj17 4 11 -> Adj17 11 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 10. assume H3: Adj17 4 10.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_11 : Adj17 4 11 -> Adj17 11 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 11. assume H3: Adj17 4 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_4_11_12 : Adj17 4 11 -> Adj17 11 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 12. assume H3: Adj17 4 12.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_13 : Adj17 4 11 -> Adj17 11 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 13. assume H3: Adj17 4 13.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_14 : Adj17 4 11 -> Adj17 11 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 14. assume H3: Adj17 4 14.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_15 : Adj17 4 11 -> Adj17 11 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 15. assume H3: Adj17 4 15.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_11_16 : Adj17 4 11 -> Adj17 11 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 11. assume H2: Adj17 11 16. assume H3: Adj17 4 16.
exact Adj17_not_4_11 H1.
Qed.

Theorem tf_4_12_0 : Adj17 4 12 -> Adj17 12 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 0. assume H3: Adj17 4 0.
exact Adj17_not_12_0 H2.
Qed.

Theorem tf_4_12_1 : Adj17 4 12 -> Adj17 12 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 1. assume H3: Adj17 4 1.
exact Adj17_not_12_1 H2.
Qed.

Theorem tf_4_12_2 : Adj17 4 12 -> Adj17 12 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 2. assume H3: Adj17 4 2.
exact Adj17_not_4_2 H3.
Qed.

Theorem tf_4_12_3 : Adj17 4 12 -> Adj17 12 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 3. assume H3: Adj17 4 3.
exact Adj17_not_12_3 H2.
Qed.

Theorem tf_4_12_4 : Adj17 4 12 -> Adj17 12 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_12_5 : Adj17 4 12 -> Adj17 12 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 5. assume H3: Adj17 4 5.
exact Adj17_not_12_5 H2.
Qed.

Theorem tf_4_12_6 : Adj17 4 12 -> Adj17 12 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 6. assume H3: Adj17 4 6.
exact Adj17_not_4_6 H3.
Qed.

Theorem tf_4_12_7 : Adj17 4 12 -> Adj17 12 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 7. assume H3: Adj17 4 7.
exact Adj17_not_12_7 H2.
Qed.

Theorem tf_4_12_8 : Adj17 4 12 -> Adj17 12 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 8. assume H3: Adj17 4 8.
exact Adj17_not_12_8 H2.
Qed.

Theorem tf_4_12_9 : Adj17 4 12 -> Adj17 12 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 9. assume H3: Adj17 4 9.
exact Adj17_not_4_9 H3.
Qed.

Theorem tf_4_12_10 : Adj17 4 12 -> Adj17 12 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 10. assume H3: Adj17 4 10.
exact Adj17_not_12_10 H2.
Qed.

Theorem tf_4_12_11 : Adj17 4 12 -> Adj17 12 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 11. assume H3: Adj17 4 11.
exact Adj17_not_12_11 H2.
Qed.

Theorem tf_4_12_12 : Adj17 4 12 -> Adj17 12 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 12. assume H3: Adj17 4 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_4_12_13 : Adj17 4 12 -> Adj17 12 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 13. assume H3: Adj17 4 13.
exact Adj17_not_4_13 H3.
Qed.

Theorem tf_4_12_14 : Adj17 4 12 -> Adj17 12 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 14. assume H3: Adj17 4 14.
exact Adj17_not_12_14 H2.
Qed.

Theorem tf_4_12_15 : Adj17 4 12 -> Adj17 12 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 15. assume H3: Adj17 4 15.
exact Adj17_not_12_15 H2.
Qed.

Theorem tf_4_12_16 : Adj17 4 12 -> Adj17 12 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 12. assume H2: Adj17 12 16. assume H3: Adj17 4 16.
exact Adj17_not_12_16 H2.
Qed.

Theorem tf_4_13_0 : Adj17 4 13 -> Adj17 13 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 0. assume H3: Adj17 4 0.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_1 : Adj17 4 13 -> Adj17 13 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 1. assume H3: Adj17 4 1.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_2 : Adj17 4 13 -> Adj17 13 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 2. assume H3: Adj17 4 2.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_3 : Adj17 4 13 -> Adj17 13 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 3. assume H3: Adj17 4 3.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_4 : Adj17 4 13 -> Adj17 13 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_13_5 : Adj17 4 13 -> Adj17 13 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 5. assume H3: Adj17 4 5.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_6 : Adj17 4 13 -> Adj17 13 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 6. assume H3: Adj17 4 6.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_7 : Adj17 4 13 -> Adj17 13 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 7. assume H3: Adj17 4 7.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_8 : Adj17 4 13 -> Adj17 13 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 8. assume H3: Adj17 4 8.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_9 : Adj17 4 13 -> Adj17 13 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 9. assume H3: Adj17 4 9.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_10 : Adj17 4 13 -> Adj17 13 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 10. assume H3: Adj17 4 10.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_11 : Adj17 4 13 -> Adj17 13 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 11. assume H3: Adj17 4 11.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_12 : Adj17 4 13 -> Adj17 13 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 12. assume H3: Adj17 4 12.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_13 : Adj17 4 13 -> Adj17 13 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 13. assume H3: Adj17 4 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_4_13_14 : Adj17 4 13 -> Adj17 13 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 14. assume H3: Adj17 4 14.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_15 : Adj17 4 13 -> Adj17 13 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 15. assume H3: Adj17 4 15.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_13_16 : Adj17 4 13 -> Adj17 13 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 13. assume H2: Adj17 13 16. assume H3: Adj17 4 16.
exact Adj17_not_4_13 H1.
Qed.

Theorem tf_4_14_0 : Adj17 4 14 -> Adj17 14 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 0. assume H3: Adj17 4 0.
exact Adj17_not_4_0 H3.
Qed.

Theorem tf_4_14_1 : Adj17 4 14 -> Adj17 14 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 1. assume H3: Adj17 4 1.
exact Adj17_not_14_1 H2.
Qed.

Theorem tf_4_14_2 : Adj17 4 14 -> Adj17 14 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 2. assume H3: Adj17 4 2.
exact Adj17_not_14_2 H2.
Qed.

Theorem tf_4_14_3 : Adj17 4 14 -> Adj17 14 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 3. assume H3: Adj17 4 3.
exact Adj17_not_14_3 H2.
Qed.

Theorem tf_4_14_4 : Adj17 4 14 -> Adj17 14 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_14_5 : Adj17 4 14 -> Adj17 14 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 5. assume H3: Adj17 4 5.
exact Adj17_not_14_5 H2.
Qed.

Theorem tf_4_14_6 : Adj17 4 14 -> Adj17 14 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 6. assume H3: Adj17 4 6.
exact Adj17_not_4_6 H3.
Qed.

Theorem tf_4_14_7 : Adj17 4 14 -> Adj17 14 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 7. assume H3: Adj17 4 7.
exact Adj17_not_14_7 H2.
Qed.

Theorem tf_4_14_8 : Adj17 4 14 -> Adj17 14 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 8. assume H3: Adj17 4 8.
exact Adj17_not_4_8 H3.
Qed.

Theorem tf_4_14_9 : Adj17 4 14 -> Adj17 14 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 9. assume H3: Adj17 4 9.
exact Adj17_not_14_9 H2.
Qed.

Theorem tf_4_14_10 : Adj17 4 14 -> Adj17 14 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 10. assume H3: Adj17 4 10.
exact Adj17_not_14_10 H2.
Qed.

Theorem tf_4_14_11 : Adj17 4 14 -> Adj17 14 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 11. assume H3: Adj17 4 11.
exact Adj17_not_14_11 H2.
Qed.

Theorem tf_4_14_12 : Adj17 4 14 -> Adj17 14 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 12. assume H3: Adj17 4 12.
exact Adj17_not_14_12 H2.
Qed.

Theorem tf_4_14_13 : Adj17 4 14 -> Adj17 14 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 13. assume H3: Adj17 4 13.
exact Adj17_not_4_13 H3.
Qed.

Theorem tf_4_14_14 : Adj17 4 14 -> Adj17 14 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 14. assume H3: Adj17 4 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_4_14_15 : Adj17 4 14 -> Adj17 14 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 15. assume H3: Adj17 4 15.
exact Adj17_not_14_15 H2.
Qed.

Theorem tf_4_14_16 : Adj17 4 14 -> Adj17 14 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 14. assume H2: Adj17 14 16. assume H3: Adj17 4 16.
exact Adj17_not_14_16 H2.
Qed.

Theorem tf_4_15_0 : Adj17 4 15 -> Adj17 15 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 0. assume H3: Adj17 4 0.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_1 : Adj17 4 15 -> Adj17 15 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 1. assume H3: Adj17 4 1.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_2 : Adj17 4 15 -> Adj17 15 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 2. assume H3: Adj17 4 2.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_3 : Adj17 4 15 -> Adj17 15 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 3. assume H3: Adj17 4 3.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_4 : Adj17 4 15 -> Adj17 15 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_15_5 : Adj17 4 15 -> Adj17 15 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 5. assume H3: Adj17 4 5.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_6 : Adj17 4 15 -> Adj17 15 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 6. assume H3: Adj17 4 6.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_7 : Adj17 4 15 -> Adj17 15 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 7. assume H3: Adj17 4 7.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_8 : Adj17 4 15 -> Adj17 15 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 8. assume H3: Adj17 4 8.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_9 : Adj17 4 15 -> Adj17 15 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 9. assume H3: Adj17 4 9.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_10 : Adj17 4 15 -> Adj17 15 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 10. assume H3: Adj17 4 10.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_11 : Adj17 4 15 -> Adj17 15 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 11. assume H3: Adj17 4 11.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_12 : Adj17 4 15 -> Adj17 15 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 12. assume H3: Adj17 4 12.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_13 : Adj17 4 15 -> Adj17 15 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 13. assume H3: Adj17 4 13.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_14 : Adj17 4 15 -> Adj17 15 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 14. assume H3: Adj17 4 14.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_15_15 : Adj17 4 15 -> Adj17 15 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 15. assume H3: Adj17 4 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_4_15_16 : Adj17 4 15 -> Adj17 15 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 15. assume H2: Adj17 15 16. assume H3: Adj17 4 16.
exact Adj17_not_4_15 H1.
Qed.

Theorem tf_4_16_0 : Adj17 4 16 -> Adj17 16 0 -> Adj17 4 0 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 0. assume H3: Adj17 4 0.
exact Adj17_not_4_0 H3.
Qed.

Theorem tf_4_16_1 : Adj17 4 16 -> Adj17 16 1 -> Adj17 4 1 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 1. assume H3: Adj17 4 1.
exact Adj17_not_4_1 H3.
Qed.

Theorem tf_4_16_2 : Adj17 4 16 -> Adj17 16 2 -> Adj17 4 2 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 2. assume H3: Adj17 4 2.
exact Adj17_not_16_2 H2.
Qed.

Theorem tf_4_16_3 : Adj17 4 16 -> Adj17 16 3 -> Adj17 4 3 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 3. assume H3: Adj17 4 3.
exact Adj17_not_4_3 H3.
Qed.

Theorem tf_4_16_4 : Adj17 4 16 -> Adj17 16 4 -> Adj17 4 4 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 4. assume H3: Adj17 4 4.
exact Adj17_not_4_4 H3.
Qed.

Theorem tf_4_16_5 : Adj17 4 16 -> Adj17 16 5 -> Adj17 4 5 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 5. assume H3: Adj17 4 5.
exact Adj17_not_16_5 H2.
Qed.

Theorem tf_4_16_6 : Adj17 4 16 -> Adj17 16 6 -> Adj17 4 6 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 6. assume H3: Adj17 4 6.
exact Adj17_not_16_6 H2.
Qed.

Theorem tf_4_16_7 : Adj17 4 16 -> Adj17 16 7 -> Adj17 4 7 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 7. assume H3: Adj17 4 7.
exact Adj17_not_16_7 H2.
Qed.

Theorem tf_4_16_8 : Adj17 4 16 -> Adj17 16 8 -> Adj17 4 8 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 8. assume H3: Adj17 4 8.
exact Adj17_not_16_8 H2.
Qed.

Theorem tf_4_16_9 : Adj17 4 16 -> Adj17 16 9 -> Adj17 4 9 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 9. assume H3: Adj17 4 9.
exact Adj17_not_16_9 H2.
Qed.

Theorem tf_4_16_10 : Adj17 4 16 -> Adj17 16 10 -> Adj17 4 10 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 10. assume H3: Adj17 4 10.
exact Adj17_not_4_10 H3.
Qed.

Theorem tf_4_16_11 : Adj17 4 16 -> Adj17 16 11 -> Adj17 4 11 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 11. assume H3: Adj17 4 11.
exact Adj17_not_16_11 H2.
Qed.

Theorem tf_4_16_12 : Adj17 4 16 -> Adj17 16 12 -> Adj17 4 12 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 12. assume H3: Adj17 4 12.
exact Adj17_not_16_12 H2.
Qed.

Theorem tf_4_16_13 : Adj17 4 16 -> Adj17 16 13 -> Adj17 4 13 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 13. assume H3: Adj17 4 13.
exact Adj17_not_16_13 H2.
Qed.

Theorem tf_4_16_14 : Adj17 4 16 -> Adj17 16 14 -> Adj17 4 14 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 14. assume H3: Adj17 4 14.
exact Adj17_not_16_14 H2.
Qed.

Theorem tf_4_16_15 : Adj17 4 16 -> Adj17 16 15 -> Adj17 4 15 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 15. assume H3: Adj17 4 15.
exact Adj17_not_16_15 H2.
Qed.

Theorem tf_4_16_16 : Adj17 4 16 -> Adj17 16 16 -> Adj17 4 16 -> False.
assume H1: Adj17 4 16. assume H2: Adj17 16 16. assume H3: Adj17 4 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_5_0_0 : Adj17 5 0 -> Adj17 0 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 0. assume H3: Adj17 5 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_5_0_1 : Adj17 5 0 -> Adj17 0 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 1. assume H3: Adj17 5 1.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_2 : Adj17 5 0 -> Adj17 0 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 2. assume H3: Adj17 5 2.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_3 : Adj17 5 0 -> Adj17 0 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 3. assume H3: Adj17 5 3.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_4 : Adj17 5 0 -> Adj17 0 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 4. assume H3: Adj17 5 4.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_5 : Adj17 5 0 -> Adj17 0 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_0_6 : Adj17 5 0 -> Adj17 0 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 6. assume H3: Adj17 5 6.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_7 : Adj17 5 0 -> Adj17 0 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 7. assume H3: Adj17 5 7.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_8 : Adj17 5 0 -> Adj17 0 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 8. assume H3: Adj17 5 8.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_9 : Adj17 5 0 -> Adj17 0 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 9. assume H3: Adj17 5 9.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_10 : Adj17 5 0 -> Adj17 0 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 10. assume H3: Adj17 5 10.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_11 : Adj17 5 0 -> Adj17 0 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 11. assume H3: Adj17 5 11.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_12 : Adj17 5 0 -> Adj17 0 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 12. assume H3: Adj17 5 12.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_13 : Adj17 5 0 -> Adj17 0 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 13. assume H3: Adj17 5 13.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_14 : Adj17 5 0 -> Adj17 0 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 14. assume H3: Adj17 5 14.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_15 : Adj17 5 0 -> Adj17 0 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 15. assume H3: Adj17 5 15.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_0_16 : Adj17 5 0 -> Adj17 0 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 0. assume H2: Adj17 0 16. assume H3: Adj17 5 16.
exact Adj17_not_5_0 H1.
Qed.

Theorem tf_5_1_0 : Adj17 5 1 -> Adj17 1 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 0. assume H3: Adj17 5 0.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_1 : Adj17 5 1 -> Adj17 1 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 1. assume H3: Adj17 5 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_5_1_2 : Adj17 5 1 -> Adj17 1 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 2. assume H3: Adj17 5 2.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_3 : Adj17 5 1 -> Adj17 1 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 3. assume H3: Adj17 5 3.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_4 : Adj17 5 1 -> Adj17 1 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 4. assume H3: Adj17 5 4.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_5 : Adj17 5 1 -> Adj17 1 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_1_6 : Adj17 5 1 -> Adj17 1 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 6. assume H3: Adj17 5 6.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_7 : Adj17 5 1 -> Adj17 1 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 7. assume H3: Adj17 5 7.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_8 : Adj17 5 1 -> Adj17 1 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 8. assume H3: Adj17 5 8.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_9 : Adj17 5 1 -> Adj17 1 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 9. assume H3: Adj17 5 9.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_10 : Adj17 5 1 -> Adj17 1 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 10. assume H3: Adj17 5 10.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_11 : Adj17 5 1 -> Adj17 1 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 11. assume H3: Adj17 5 11.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_12 : Adj17 5 1 -> Adj17 1 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 12. assume H3: Adj17 5 12.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_13 : Adj17 5 1 -> Adj17 1 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 13. assume H3: Adj17 5 13.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_14 : Adj17 5 1 -> Adj17 1 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 14. assume H3: Adj17 5 14.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_15 : Adj17 5 1 -> Adj17 1 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 15. assume H3: Adj17 5 15.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_1_16 : Adj17 5 1 -> Adj17 1 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 1. assume H2: Adj17 1 16. assume H3: Adj17 5 16.
exact Adj17_not_5_1 H1.
Qed.

Theorem tf_5_2_0 : Adj17 5 2 -> Adj17 2 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 0. assume H3: Adj17 5 0.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_1 : Adj17 5 2 -> Adj17 2 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 1. assume H3: Adj17 5 1.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_2 : Adj17 5 2 -> Adj17 2 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 2. assume H3: Adj17 5 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_5_2_3 : Adj17 5 2 -> Adj17 2 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 3. assume H3: Adj17 5 3.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_4 : Adj17 5 2 -> Adj17 2 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 4. assume H3: Adj17 5 4.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_5 : Adj17 5 2 -> Adj17 2 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_2_6 : Adj17 5 2 -> Adj17 2 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 6. assume H3: Adj17 5 6.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_7 : Adj17 5 2 -> Adj17 2 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 7. assume H3: Adj17 5 7.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_8 : Adj17 5 2 -> Adj17 2 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 8. assume H3: Adj17 5 8.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_9 : Adj17 5 2 -> Adj17 2 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 9. assume H3: Adj17 5 9.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_10 : Adj17 5 2 -> Adj17 2 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 10. assume H3: Adj17 5 10.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_11 : Adj17 5 2 -> Adj17 2 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 11. assume H3: Adj17 5 11.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_12 : Adj17 5 2 -> Adj17 2 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 12. assume H3: Adj17 5 12.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_13 : Adj17 5 2 -> Adj17 2 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 13. assume H3: Adj17 5 13.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_14 : Adj17 5 2 -> Adj17 2 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 14. assume H3: Adj17 5 14.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_15 : Adj17 5 2 -> Adj17 2 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 15. assume H3: Adj17 5 15.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_2_16 : Adj17 5 2 -> Adj17 2 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 2. assume H2: Adj17 2 16. assume H3: Adj17 5 16.
exact Adj17_not_5_2 H1.
Qed.

Theorem tf_5_3_0 : Adj17 5 3 -> Adj17 3 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 0. assume H3: Adj17 5 0.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_1 : Adj17 5 3 -> Adj17 3 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 1. assume H3: Adj17 5 1.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_2 : Adj17 5 3 -> Adj17 3 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 2. assume H3: Adj17 5 2.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_3 : Adj17 5 3 -> Adj17 3 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 3. assume H3: Adj17 5 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_5_3_4 : Adj17 5 3 -> Adj17 3 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 4. assume H3: Adj17 5 4.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_5 : Adj17 5 3 -> Adj17 3 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_3_6 : Adj17 5 3 -> Adj17 3 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 6. assume H3: Adj17 5 6.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_7 : Adj17 5 3 -> Adj17 3 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 7. assume H3: Adj17 5 7.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_8 : Adj17 5 3 -> Adj17 3 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 8. assume H3: Adj17 5 8.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_9 : Adj17 5 3 -> Adj17 3 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 9. assume H3: Adj17 5 9.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_10 : Adj17 5 3 -> Adj17 3 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 10. assume H3: Adj17 5 10.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_11 : Adj17 5 3 -> Adj17 3 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 11. assume H3: Adj17 5 11.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_12 : Adj17 5 3 -> Adj17 3 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 12. assume H3: Adj17 5 12.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_13 : Adj17 5 3 -> Adj17 3 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 13. assume H3: Adj17 5 13.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_14 : Adj17 5 3 -> Adj17 3 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 14. assume H3: Adj17 5 14.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_15 : Adj17 5 3 -> Adj17 3 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 15. assume H3: Adj17 5 15.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_3_16 : Adj17 5 3 -> Adj17 3 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 3. assume H2: Adj17 3 16. assume H3: Adj17 5 16.
exact Adj17_not_5_3 H1.
Qed.

Theorem tf_5_4_0 : Adj17 5 4 -> Adj17 4 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 0. assume H3: Adj17 5 0.
exact Adj17_not_4_0 H2.
Qed.

Theorem tf_5_4_1 : Adj17 5 4 -> Adj17 4 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 1. assume H3: Adj17 5 1.
exact Adj17_not_4_1 H2.
Qed.

Theorem tf_5_4_2 : Adj17 5 4 -> Adj17 4 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 2. assume H3: Adj17 5 2.
exact Adj17_not_4_2 H2.
Qed.

Theorem tf_5_4_3 : Adj17 5 4 -> Adj17 4 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 3. assume H3: Adj17 5 3.
exact Adj17_not_4_3 H2.
Qed.

Theorem tf_5_4_4 : Adj17 5 4 -> Adj17 4 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 4. assume H3: Adj17 5 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_5_4_5 : Adj17 5 4 -> Adj17 4 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_4_6 : Adj17 5 4 -> Adj17 4 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 6. assume H3: Adj17 5 6.
exact Adj17_not_4_6 H2.
Qed.

Theorem tf_5_4_7 : Adj17 5 4 -> Adj17 4 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 7. assume H3: Adj17 5 7.
exact Adj17_not_5_7 H3.
Qed.

Theorem tf_5_4_8 : Adj17 5 4 -> Adj17 4 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 8. assume H3: Adj17 5 8.
exact Adj17_not_4_8 H2.
Qed.

Theorem tf_5_4_9 : Adj17 5 4 -> Adj17 4 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 9. assume H3: Adj17 5 9.
exact Adj17_not_4_9 H2.
Qed.

Theorem tf_5_4_10 : Adj17 5 4 -> Adj17 4 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 10. assume H3: Adj17 5 10.
exact Adj17_not_4_10 H2.
Qed.

Theorem tf_5_4_11 : Adj17 5 4 -> Adj17 4 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 11. assume H3: Adj17 5 11.
exact Adj17_not_4_11 H2.
Qed.

Theorem tf_5_4_12 : Adj17 5 4 -> Adj17 4 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 12. assume H3: Adj17 5 12.
exact Adj17_not_5_12 H3.
Qed.

Theorem tf_5_4_13 : Adj17 5 4 -> Adj17 4 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 13. assume H3: Adj17 5 13.
exact Adj17_not_4_13 H2.
Qed.

Theorem tf_5_4_14 : Adj17 5 4 -> Adj17 4 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 14. assume H3: Adj17 5 14.
exact Adj17_not_5_14 H3.
Qed.

Theorem tf_5_4_15 : Adj17 5 4 -> Adj17 4 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 15. assume H3: Adj17 5 15.
exact Adj17_not_4_15 H2.
Qed.

Theorem tf_5_4_16 : Adj17 5 4 -> Adj17 4 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 4. assume H2: Adj17 4 16. assume H3: Adj17 5 16.
exact Adj17_not_5_16 H3.
Qed.

Theorem tf_5_5_0 : Adj17 5 5 -> Adj17 5 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 0. assume H3: Adj17 5 0.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_1 : Adj17 5 5 -> Adj17 5 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 1. assume H3: Adj17 5 1.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_2 : Adj17 5 5 -> Adj17 5 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 2. assume H3: Adj17 5 2.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_3 : Adj17 5 5 -> Adj17 5 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 3. assume H3: Adj17 5 3.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_4 : Adj17 5 5 -> Adj17 5 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 4. assume H3: Adj17 5 4.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_5 : Adj17 5 5 -> Adj17 5 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_6 : Adj17 5 5 -> Adj17 5 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 6. assume H3: Adj17 5 6.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_7 : Adj17 5 5 -> Adj17 5 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 7. assume H3: Adj17 5 7.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_8 : Adj17 5 5 -> Adj17 5 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 8. assume H3: Adj17 5 8.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_9 : Adj17 5 5 -> Adj17 5 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 9. assume H3: Adj17 5 9.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_10 : Adj17 5 5 -> Adj17 5 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 10. assume H3: Adj17 5 10.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_11 : Adj17 5 5 -> Adj17 5 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 11. assume H3: Adj17 5 11.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_12 : Adj17 5 5 -> Adj17 5 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 12. assume H3: Adj17 5 12.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_13 : Adj17 5 5 -> Adj17 5 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 13. assume H3: Adj17 5 13.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_14 : Adj17 5 5 -> Adj17 5 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 14. assume H3: Adj17 5 14.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_15 : Adj17 5 5 -> Adj17 5 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 15. assume H3: Adj17 5 15.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_5_16 : Adj17 5 5 -> Adj17 5 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 5. assume H2: Adj17 5 16. assume H3: Adj17 5 16.
exact Adj17_not_5_5 H1.
Qed.

Theorem tf_5_6_0 : Adj17 5 6 -> Adj17 6 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 0. assume H3: Adj17 5 0.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_1 : Adj17 5 6 -> Adj17 6 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 1. assume H3: Adj17 5 1.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_2 : Adj17 5 6 -> Adj17 6 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 2. assume H3: Adj17 5 2.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_3 : Adj17 5 6 -> Adj17 6 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 3. assume H3: Adj17 5 3.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_4 : Adj17 5 6 -> Adj17 6 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 4. assume H3: Adj17 5 4.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_5 : Adj17 5 6 -> Adj17 6 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_6_6 : Adj17 5 6 -> Adj17 6 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 6. assume H3: Adj17 5 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_5_6_7 : Adj17 5 6 -> Adj17 6 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 7. assume H3: Adj17 5 7.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_8 : Adj17 5 6 -> Adj17 6 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 8. assume H3: Adj17 5 8.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_9 : Adj17 5 6 -> Adj17 6 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 9. assume H3: Adj17 5 9.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_10 : Adj17 5 6 -> Adj17 6 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 10. assume H3: Adj17 5 10.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_11 : Adj17 5 6 -> Adj17 6 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 11. assume H3: Adj17 5 11.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_12 : Adj17 5 6 -> Adj17 6 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 12. assume H3: Adj17 5 12.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_13 : Adj17 5 6 -> Adj17 6 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 13. assume H3: Adj17 5 13.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_14 : Adj17 5 6 -> Adj17 6 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 14. assume H3: Adj17 5 14.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_15 : Adj17 5 6 -> Adj17 6 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 15. assume H3: Adj17 5 15.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_6_16 : Adj17 5 6 -> Adj17 6 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 6. assume H2: Adj17 6 16. assume H3: Adj17 5 16.
exact Adj17_not_5_6 H1.
Qed.

Theorem tf_5_7_0 : Adj17 5 7 -> Adj17 7 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 0. assume H3: Adj17 5 0.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_1 : Adj17 5 7 -> Adj17 7 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 1. assume H3: Adj17 5 1.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_2 : Adj17 5 7 -> Adj17 7 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 2. assume H3: Adj17 5 2.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_3 : Adj17 5 7 -> Adj17 7 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 3. assume H3: Adj17 5 3.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_4 : Adj17 5 7 -> Adj17 7 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 4. assume H3: Adj17 5 4.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_5 : Adj17 5 7 -> Adj17 7 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_7_6 : Adj17 5 7 -> Adj17 7 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 6. assume H3: Adj17 5 6.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_7 : Adj17 5 7 -> Adj17 7 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 7. assume H3: Adj17 5 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_5_7_8 : Adj17 5 7 -> Adj17 7 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 8. assume H3: Adj17 5 8.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_9 : Adj17 5 7 -> Adj17 7 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 9. assume H3: Adj17 5 9.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_10 : Adj17 5 7 -> Adj17 7 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 10. assume H3: Adj17 5 10.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_11 : Adj17 5 7 -> Adj17 7 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 11. assume H3: Adj17 5 11.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_12 : Adj17 5 7 -> Adj17 7 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 12. assume H3: Adj17 5 12.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_13 : Adj17 5 7 -> Adj17 7 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 13. assume H3: Adj17 5 13.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_14 : Adj17 5 7 -> Adj17 7 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 14. assume H3: Adj17 5 14.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_15 : Adj17 5 7 -> Adj17 7 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 15. assume H3: Adj17 5 15.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_7_16 : Adj17 5 7 -> Adj17 7 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 7. assume H2: Adj17 7 16. assume H3: Adj17 5 16.
exact Adj17_not_5_7 H1.
Qed.

Theorem tf_5_8_0 : Adj17 5 8 -> Adj17 8 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 0. assume H3: Adj17 5 0.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_1 : Adj17 5 8 -> Adj17 8 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 1. assume H3: Adj17 5 1.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_2 : Adj17 5 8 -> Adj17 8 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 2. assume H3: Adj17 5 2.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_3 : Adj17 5 8 -> Adj17 8 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 3. assume H3: Adj17 5 3.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_4 : Adj17 5 8 -> Adj17 8 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 4. assume H3: Adj17 5 4.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_5 : Adj17 5 8 -> Adj17 8 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_8_6 : Adj17 5 8 -> Adj17 8 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 6. assume H3: Adj17 5 6.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_7 : Adj17 5 8 -> Adj17 8 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 7. assume H3: Adj17 5 7.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_8 : Adj17 5 8 -> Adj17 8 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 8. assume H3: Adj17 5 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_5_8_9 : Adj17 5 8 -> Adj17 8 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 9. assume H3: Adj17 5 9.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_10 : Adj17 5 8 -> Adj17 8 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 10. assume H3: Adj17 5 10.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_11 : Adj17 5 8 -> Adj17 8 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 11. assume H3: Adj17 5 11.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_12 : Adj17 5 8 -> Adj17 8 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 12. assume H3: Adj17 5 12.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_13 : Adj17 5 8 -> Adj17 8 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 13. assume H3: Adj17 5 13.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_14 : Adj17 5 8 -> Adj17 8 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 14. assume H3: Adj17 5 14.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_15 : Adj17 5 8 -> Adj17 8 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 15. assume H3: Adj17 5 15.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_8_16 : Adj17 5 8 -> Adj17 8 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 8. assume H2: Adj17 8 16. assume H3: Adj17 5 16.
exact Adj17_not_5_8 H1.
Qed.

Theorem tf_5_9_0 : Adj17 5 9 -> Adj17 9 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 0. assume H3: Adj17 5 0.
exact Adj17_not_5_0 H3.
Qed.

Theorem tf_5_9_1 : Adj17 5 9 -> Adj17 9 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 1. assume H3: Adj17 5 1.
exact Adj17_not_9_1 H2.
Qed.

Theorem tf_5_9_2 : Adj17 5 9 -> Adj17 9 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 2. assume H3: Adj17 5 2.
exact Adj17_not_9_2 H2.
Qed.

Theorem tf_5_9_3 : Adj17 5 9 -> Adj17 9 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 3. assume H3: Adj17 5 3.
exact Adj17_not_9_3 H2.
Qed.

Theorem tf_5_9_4 : Adj17 5 9 -> Adj17 9 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 4. assume H3: Adj17 5 4.
exact Adj17_not_9_4 H2.
Qed.

Theorem tf_5_9_5 : Adj17 5 9 -> Adj17 9 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_9_6 : Adj17 5 9 -> Adj17 9 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 6. assume H3: Adj17 5 6.
exact Adj17_not_9_6 H2.
Qed.

Theorem tf_5_9_7 : Adj17 5 9 -> Adj17 9 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 7. assume H3: Adj17 5 7.
exact Adj17_not_5_7 H3.
Qed.

Theorem tf_5_9_8 : Adj17 5 9 -> Adj17 9 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 8. assume H3: Adj17 5 8.
exact Adj17_not_5_8 H3.
Qed.

Theorem tf_5_9_9 : Adj17 5 9 -> Adj17 9 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 9. assume H3: Adj17 5 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_5_9_10 : Adj17 5 9 -> Adj17 9 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 10. assume H3: Adj17 5 10.
exact Adj17_not_9_10 H2.
Qed.

Theorem tf_5_9_11 : Adj17 5 9 -> Adj17 9 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 11. assume H3: Adj17 5 11.
exact Adj17_not_9_11 H2.
Qed.

Theorem tf_5_9_12 : Adj17 5 9 -> Adj17 9 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 12. assume H3: Adj17 5 12.
exact Adj17_not_5_12 H3.
Qed.

Theorem tf_5_9_13 : Adj17 5 9 -> Adj17 9 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 13. assume H3: Adj17 5 13.
exact Adj17_not_9_13 H2.
Qed.

Theorem tf_5_9_14 : Adj17 5 9 -> Adj17 9 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 14. assume H3: Adj17 5 14.
exact Adj17_not_9_14 H2.
Qed.

Theorem tf_5_9_15 : Adj17 5 9 -> Adj17 9 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 15. assume H3: Adj17 5 15.
exact Adj17_not_9_15 H2.
Qed.

Theorem tf_5_9_16 : Adj17 5 9 -> Adj17 9 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 9. assume H2: Adj17 9 16. assume H3: Adj17 5 16.
exact Adj17_not_9_16 H2.
Qed.

Theorem tf_5_10_0 : Adj17 5 10 -> Adj17 10 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 0. assume H3: Adj17 5 0.
exact Adj17_not_10_0 H2.
Qed.

Theorem tf_5_10_1 : Adj17 5 10 -> Adj17 10 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 1. assume H3: Adj17 5 1.
exact Adj17_not_10_1 H2.
Qed.

Theorem tf_5_10_2 : Adj17 5 10 -> Adj17 10 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 2. assume H3: Adj17 5 2.
exact Adj17_not_5_2 H3.
Qed.

Theorem tf_5_10_3 : Adj17 5 10 -> Adj17 10 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 3. assume H3: Adj17 5 3.
exact Adj17_not_10_3 H2.
Qed.

Theorem tf_5_10_4 : Adj17 5 10 -> Adj17 10 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 4. assume H3: Adj17 5 4.
exact Adj17_not_10_4 H2.
Qed.

Theorem tf_5_10_5 : Adj17 5 10 -> Adj17 10 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_10_6 : Adj17 5 10 -> Adj17 10 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 6. assume H3: Adj17 5 6.
exact Adj17_not_5_6 H3.
Qed.

Theorem tf_5_10_7 : Adj17 5 10 -> Adj17 10 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 7. assume H3: Adj17 5 7.
exact Adj17_not_5_7 H3.
Qed.

Theorem tf_5_10_8 : Adj17 5 10 -> Adj17 10 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 8. assume H3: Adj17 5 8.
exact Adj17_not_10_8 H2.
Qed.

Theorem tf_5_10_9 : Adj17 5 10 -> Adj17 10 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 9. assume H3: Adj17 5 9.
exact Adj17_not_10_9 H2.
Qed.

Theorem tf_5_10_10 : Adj17 5 10 -> Adj17 10 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 10. assume H3: Adj17 5 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_5_10_11 : Adj17 5 10 -> Adj17 10 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 11. assume H3: Adj17 5 11.
exact Adj17_not_10_11 H2.
Qed.

Theorem tf_5_10_12 : Adj17 5 10 -> Adj17 10 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 12. assume H3: Adj17 5 12.
exact Adj17_not_10_12 H2.
Qed.

Theorem tf_5_10_13 : Adj17 5 10 -> Adj17 10 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 13. assume H3: Adj17 5 13.
exact Adj17_not_10_13 H2.
Qed.

Theorem tf_5_10_14 : Adj17 5 10 -> Adj17 10 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 14. assume H3: Adj17 5 14.
exact Adj17_not_10_14 H2.
Qed.

Theorem tf_5_10_15 : Adj17 5 10 -> Adj17 10 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 15. assume H3: Adj17 5 15.
exact Adj17_not_10_15 H2.
Qed.

Theorem tf_5_10_16 : Adj17 5 10 -> Adj17 10 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 10. assume H2: Adj17 10 16. assume H3: Adj17 5 16.
exact Adj17_not_5_16 H3.
Qed.

Theorem tf_5_11_0 : Adj17 5 11 -> Adj17 11 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 0. assume H3: Adj17 5 0.
exact Adj17_not_11_0 H2.
Qed.

Theorem tf_5_11_1 : Adj17 5 11 -> Adj17 11 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 1. assume H3: Adj17 5 1.
exact Adj17_not_5_1 H3.
Qed.

Theorem tf_5_11_2 : Adj17 5 11 -> Adj17 11 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 2. assume H3: Adj17 5 2.
exact Adj17_not_11_2 H2.
Qed.

Theorem tf_5_11_3 : Adj17 5 11 -> Adj17 11 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 3. assume H3: Adj17 5 3.
exact Adj17_not_11_3 H2.
Qed.

Theorem tf_5_11_4 : Adj17 5 11 -> Adj17 11 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 4. assume H3: Adj17 5 4.
exact Adj17_not_11_4 H2.
Qed.

Theorem tf_5_11_5 : Adj17 5 11 -> Adj17 11 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_11_6 : Adj17 5 11 -> Adj17 11 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 6. assume H3: Adj17 5 6.
exact Adj17_not_5_6 H3.
Qed.

Theorem tf_5_11_7 : Adj17 5 11 -> Adj17 11 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 7. assume H3: Adj17 5 7.
exact Adj17_not_11_7 H2.
Qed.

Theorem tf_5_11_8 : Adj17 5 11 -> Adj17 11 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 8. assume H3: Adj17 5 8.
exact Adj17_not_5_8 H3.
Qed.

Theorem tf_5_11_9 : Adj17 5 11 -> Adj17 11 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 9. assume H3: Adj17 5 9.
exact Adj17_not_11_9 H2.
Qed.

Theorem tf_5_11_10 : Adj17 5 11 -> Adj17 11 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 10. assume H3: Adj17 5 10.
exact Adj17_not_11_10 H2.
Qed.

Theorem tf_5_11_11 : Adj17 5 11 -> Adj17 11 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 11. assume H3: Adj17 5 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_5_11_12 : Adj17 5 11 -> Adj17 11 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 12. assume H3: Adj17 5 12.
exact Adj17_not_11_12 H2.
Qed.

Theorem tf_5_11_13 : Adj17 5 11 -> Adj17 11 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 13. assume H3: Adj17 5 13.
exact Adj17_not_11_13 H2.
Qed.

Theorem tf_5_11_14 : Adj17 5 11 -> Adj17 11 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 14. assume H3: Adj17 5 14.
exact Adj17_not_11_14 H2.
Qed.

Theorem tf_5_11_15 : Adj17 5 11 -> Adj17 11 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 15. assume H3: Adj17 5 15.
exact Adj17_not_5_15 H3.
Qed.

Theorem tf_5_11_16 : Adj17 5 11 -> Adj17 11 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 11. assume H2: Adj17 11 16. assume H3: Adj17 5 16.
exact Adj17_not_11_16 H2.
Qed.

Theorem tf_5_12_0 : Adj17 5 12 -> Adj17 12 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 0. assume H3: Adj17 5 0.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_1 : Adj17 5 12 -> Adj17 12 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 1. assume H3: Adj17 5 1.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_2 : Adj17 5 12 -> Adj17 12 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 2. assume H3: Adj17 5 2.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_3 : Adj17 5 12 -> Adj17 12 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 3. assume H3: Adj17 5 3.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_4 : Adj17 5 12 -> Adj17 12 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 4. assume H3: Adj17 5 4.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_5 : Adj17 5 12 -> Adj17 12 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_12_6 : Adj17 5 12 -> Adj17 12 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 6. assume H3: Adj17 5 6.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_7 : Adj17 5 12 -> Adj17 12 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 7. assume H3: Adj17 5 7.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_8 : Adj17 5 12 -> Adj17 12 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 8. assume H3: Adj17 5 8.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_9 : Adj17 5 12 -> Adj17 12 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 9. assume H3: Adj17 5 9.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_10 : Adj17 5 12 -> Adj17 12 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 10. assume H3: Adj17 5 10.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_11 : Adj17 5 12 -> Adj17 12 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 11. assume H3: Adj17 5 11.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_12 : Adj17 5 12 -> Adj17 12 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 12. assume H3: Adj17 5 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_5_12_13 : Adj17 5 12 -> Adj17 12 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 13. assume H3: Adj17 5 13.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_14 : Adj17 5 12 -> Adj17 12 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 14. assume H3: Adj17 5 14.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_15 : Adj17 5 12 -> Adj17 12 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 15. assume H3: Adj17 5 15.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_12_16 : Adj17 5 12 -> Adj17 12 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 12. assume H2: Adj17 12 16. assume H3: Adj17 5 16.
exact Adj17_not_5_12 H1.
Qed.

Theorem tf_5_13_0 : Adj17 5 13 -> Adj17 13 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 0. assume H3: Adj17 5 0.
exact Adj17_not_13_0 H2.
Qed.

Theorem tf_5_13_1 : Adj17 5 13 -> Adj17 13 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 1. assume H3: Adj17 5 1.
exact Adj17_not_5_1 H3.
Qed.

Theorem tf_5_13_2 : Adj17 5 13 -> Adj17 13 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 2. assume H3: Adj17 5 2.
exact Adj17_not_13_2 H2.
Qed.

Theorem tf_5_13_3 : Adj17 5 13 -> Adj17 13 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 3. assume H3: Adj17 5 3.
exact Adj17_not_5_3 H3.
Qed.

Theorem tf_5_13_4 : Adj17 5 13 -> Adj17 13 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 4. assume H3: Adj17 5 4.
exact Adj17_not_13_4 H2.
Qed.

Theorem tf_5_13_5 : Adj17 5 13 -> Adj17 13 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_13_6 : Adj17 5 13 -> Adj17 13 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 6. assume H3: Adj17 5 6.
exact Adj17_not_13_6 H2.
Qed.

Theorem tf_5_13_7 : Adj17 5 13 -> Adj17 13 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 7. assume H3: Adj17 5 7.
exact Adj17_not_13_7 H2.
Qed.

Theorem tf_5_13_8 : Adj17 5 13 -> Adj17 13 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 8. assume H3: Adj17 5 8.
exact Adj17_not_13_8 H2.
Qed.

Theorem tf_5_13_9 : Adj17 5 13 -> Adj17 13 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 9. assume H3: Adj17 5 9.
exact Adj17_not_13_9 H2.
Qed.

Theorem tf_5_13_10 : Adj17 5 13 -> Adj17 13 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 10. assume H3: Adj17 5 10.
exact Adj17_not_13_10 H2.
Qed.

Theorem tf_5_13_11 : Adj17 5 13 -> Adj17 13 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 11. assume H3: Adj17 5 11.
exact Adj17_not_13_11 H2.
Qed.

Theorem tf_5_13_12 : Adj17 5 13 -> Adj17 13 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 12. assume H3: Adj17 5 12.
exact Adj17_not_5_12 H3.
Qed.

Theorem tf_5_13_13 : Adj17 5 13 -> Adj17 13 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 13. assume H3: Adj17 5 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_5_13_14 : Adj17 5 13 -> Adj17 13 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 14. assume H3: Adj17 5 14.
exact Adj17_not_5_14 H3.
Qed.

Theorem tf_5_13_15 : Adj17 5 13 -> Adj17 13 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 15. assume H3: Adj17 5 15.
exact Adj17_not_13_15 H2.
Qed.

Theorem tf_5_13_16 : Adj17 5 13 -> Adj17 13 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 13. assume H2: Adj17 13 16. assume H3: Adj17 5 16.
exact Adj17_not_13_16 H2.
Qed.

Theorem tf_5_14_0 : Adj17 5 14 -> Adj17 14 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 0. assume H3: Adj17 5 0.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_1 : Adj17 5 14 -> Adj17 14 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 1. assume H3: Adj17 5 1.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_2 : Adj17 5 14 -> Adj17 14 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 2. assume H3: Adj17 5 2.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_3 : Adj17 5 14 -> Adj17 14 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 3. assume H3: Adj17 5 3.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_4 : Adj17 5 14 -> Adj17 14 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 4. assume H3: Adj17 5 4.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_5 : Adj17 5 14 -> Adj17 14 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_14_6 : Adj17 5 14 -> Adj17 14 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 6. assume H3: Adj17 5 6.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_7 : Adj17 5 14 -> Adj17 14 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 7. assume H3: Adj17 5 7.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_8 : Adj17 5 14 -> Adj17 14 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 8. assume H3: Adj17 5 8.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_9 : Adj17 5 14 -> Adj17 14 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 9. assume H3: Adj17 5 9.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_10 : Adj17 5 14 -> Adj17 14 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 10. assume H3: Adj17 5 10.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_11 : Adj17 5 14 -> Adj17 14 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 11. assume H3: Adj17 5 11.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_12 : Adj17 5 14 -> Adj17 14 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 12. assume H3: Adj17 5 12.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_13 : Adj17 5 14 -> Adj17 14 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 13. assume H3: Adj17 5 13.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_14 : Adj17 5 14 -> Adj17 14 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 14. assume H3: Adj17 5 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_5_14_15 : Adj17 5 14 -> Adj17 14 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 15. assume H3: Adj17 5 15.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_14_16 : Adj17 5 14 -> Adj17 14 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 14. assume H2: Adj17 14 16. assume H3: Adj17 5 16.
exact Adj17_not_5_14 H1.
Qed.

Theorem tf_5_15_0 : Adj17 5 15 -> Adj17 15 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 0. assume H3: Adj17 5 0.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_1 : Adj17 5 15 -> Adj17 15 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 1. assume H3: Adj17 5 1.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_2 : Adj17 5 15 -> Adj17 15 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 2. assume H3: Adj17 5 2.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_3 : Adj17 5 15 -> Adj17 15 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 3. assume H3: Adj17 5 3.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_4 : Adj17 5 15 -> Adj17 15 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 4. assume H3: Adj17 5 4.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_5 : Adj17 5 15 -> Adj17 15 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_15_6 : Adj17 5 15 -> Adj17 15 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 6. assume H3: Adj17 5 6.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_7 : Adj17 5 15 -> Adj17 15 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 7. assume H3: Adj17 5 7.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_8 : Adj17 5 15 -> Adj17 15 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 8. assume H3: Adj17 5 8.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_9 : Adj17 5 15 -> Adj17 15 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 9. assume H3: Adj17 5 9.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_10 : Adj17 5 15 -> Adj17 15 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 10. assume H3: Adj17 5 10.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_11 : Adj17 5 15 -> Adj17 15 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 11. assume H3: Adj17 5 11.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_12 : Adj17 5 15 -> Adj17 15 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 12. assume H3: Adj17 5 12.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_13 : Adj17 5 15 -> Adj17 15 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 13. assume H3: Adj17 5 13.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_14 : Adj17 5 15 -> Adj17 15 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 14. assume H3: Adj17 5 14.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_15_15 : Adj17 5 15 -> Adj17 15 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 15. assume H3: Adj17 5 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_5_15_16 : Adj17 5 15 -> Adj17 15 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 15. assume H2: Adj17 15 16. assume H3: Adj17 5 16.
exact Adj17_not_5_15 H1.
Qed.

Theorem tf_5_16_0 : Adj17 5 16 -> Adj17 16 0 -> Adj17 5 0 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 0. assume H3: Adj17 5 0.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_1 : Adj17 5 16 -> Adj17 16 1 -> Adj17 5 1 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 1. assume H3: Adj17 5 1.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_2 : Adj17 5 16 -> Adj17 16 2 -> Adj17 5 2 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 2. assume H3: Adj17 5 2.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_3 : Adj17 5 16 -> Adj17 16 3 -> Adj17 5 3 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 3. assume H3: Adj17 5 3.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_4 : Adj17 5 16 -> Adj17 16 4 -> Adj17 5 4 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 4. assume H3: Adj17 5 4.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_5 : Adj17 5 16 -> Adj17 16 5 -> Adj17 5 5 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 5. assume H3: Adj17 5 5.
exact Adj17_not_5_5 H3.
Qed.

Theorem tf_5_16_6 : Adj17 5 16 -> Adj17 16 6 -> Adj17 5 6 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 6. assume H3: Adj17 5 6.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_7 : Adj17 5 16 -> Adj17 16 7 -> Adj17 5 7 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 7. assume H3: Adj17 5 7.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_8 : Adj17 5 16 -> Adj17 16 8 -> Adj17 5 8 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 8. assume H3: Adj17 5 8.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_9 : Adj17 5 16 -> Adj17 16 9 -> Adj17 5 9 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 9. assume H3: Adj17 5 9.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_10 : Adj17 5 16 -> Adj17 16 10 -> Adj17 5 10 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 10. assume H3: Adj17 5 10.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_11 : Adj17 5 16 -> Adj17 16 11 -> Adj17 5 11 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 11. assume H3: Adj17 5 11.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_12 : Adj17 5 16 -> Adj17 16 12 -> Adj17 5 12 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 12. assume H3: Adj17 5 12.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_13 : Adj17 5 16 -> Adj17 16 13 -> Adj17 5 13 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 13. assume H3: Adj17 5 13.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_14 : Adj17 5 16 -> Adj17 16 14 -> Adj17 5 14 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 14. assume H3: Adj17 5 14.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_15 : Adj17 5 16 -> Adj17 16 15 -> Adj17 5 15 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 15. assume H3: Adj17 5 15.
exact Adj17_not_5_16 H1.
Qed.

Theorem tf_5_16_16 : Adj17 5 16 -> Adj17 16 16 -> Adj17 5 16 -> False.
assume H1: Adj17 5 16. assume H2: Adj17 16 16. assume H3: Adj17 5 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_6_0_0 : Adj17 6 0 -> Adj17 0 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 0. assume H3: Adj17 6 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_6_0_1 : Adj17 6 0 -> Adj17 0 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 1. assume H3: Adj17 6 1.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_2 : Adj17 6 0 -> Adj17 0 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 2. assume H3: Adj17 6 2.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_3 : Adj17 6 0 -> Adj17 0 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 3. assume H3: Adj17 6 3.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_4 : Adj17 6 0 -> Adj17 0 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 4. assume H3: Adj17 6 4.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_5 : Adj17 6 0 -> Adj17 0 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 5. assume H3: Adj17 6 5.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_6 : Adj17 6 0 -> Adj17 0 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_0_7 : Adj17 6 0 -> Adj17 0 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 7. assume H3: Adj17 6 7.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_8 : Adj17 6 0 -> Adj17 0 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 8. assume H3: Adj17 6 8.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_9 : Adj17 6 0 -> Adj17 0 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 9. assume H3: Adj17 6 9.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_10 : Adj17 6 0 -> Adj17 0 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 10. assume H3: Adj17 6 10.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_11 : Adj17 6 0 -> Adj17 0 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 11. assume H3: Adj17 6 11.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_12 : Adj17 6 0 -> Adj17 0 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 12. assume H3: Adj17 6 12.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_13 : Adj17 6 0 -> Adj17 0 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 13. assume H3: Adj17 6 13.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_14 : Adj17 6 0 -> Adj17 0 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 14. assume H3: Adj17 6 14.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_15 : Adj17 6 0 -> Adj17 0 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 15. assume H3: Adj17 6 15.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_0_16 : Adj17 6 0 -> Adj17 0 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 0. assume H2: Adj17 0 16. assume H3: Adj17 6 16.
exact Adj17_not_6_0 H1.
Qed.

Theorem tf_6_1_0 : Adj17 6 1 -> Adj17 1 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 0. assume H3: Adj17 6 0.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_1 : Adj17 6 1 -> Adj17 1 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 1. assume H3: Adj17 6 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_6_1_2 : Adj17 6 1 -> Adj17 1 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 2. assume H3: Adj17 6 2.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_3 : Adj17 6 1 -> Adj17 1 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 3. assume H3: Adj17 6 3.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_4 : Adj17 6 1 -> Adj17 1 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 4. assume H3: Adj17 6 4.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_5 : Adj17 6 1 -> Adj17 1 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 5. assume H3: Adj17 6 5.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_6 : Adj17 6 1 -> Adj17 1 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_1_7 : Adj17 6 1 -> Adj17 1 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 7. assume H3: Adj17 6 7.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_8 : Adj17 6 1 -> Adj17 1 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 8. assume H3: Adj17 6 8.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_9 : Adj17 6 1 -> Adj17 1 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 9. assume H3: Adj17 6 9.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_10 : Adj17 6 1 -> Adj17 1 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 10. assume H3: Adj17 6 10.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_11 : Adj17 6 1 -> Adj17 1 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 11. assume H3: Adj17 6 11.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_12 : Adj17 6 1 -> Adj17 1 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 12. assume H3: Adj17 6 12.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_13 : Adj17 6 1 -> Adj17 1 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 13. assume H3: Adj17 6 13.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_14 : Adj17 6 1 -> Adj17 1 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 14. assume H3: Adj17 6 14.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_15 : Adj17 6 1 -> Adj17 1 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 15. assume H3: Adj17 6 15.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_1_16 : Adj17 6 1 -> Adj17 1 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 1. assume H2: Adj17 1 16. assume H3: Adj17 6 16.
exact Adj17_not_6_1 H1.
Qed.

Theorem tf_6_2_0 : Adj17 6 2 -> Adj17 2 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 0. assume H3: Adj17 6 0.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_1 : Adj17 6 2 -> Adj17 2 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 1. assume H3: Adj17 6 1.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_2 : Adj17 6 2 -> Adj17 2 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 2. assume H3: Adj17 6 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_6_2_3 : Adj17 6 2 -> Adj17 2 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 3. assume H3: Adj17 6 3.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_4 : Adj17 6 2 -> Adj17 2 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 4. assume H3: Adj17 6 4.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_5 : Adj17 6 2 -> Adj17 2 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 5. assume H3: Adj17 6 5.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_6 : Adj17 6 2 -> Adj17 2 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_2_7 : Adj17 6 2 -> Adj17 2 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 7. assume H3: Adj17 6 7.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_8 : Adj17 6 2 -> Adj17 2 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 8. assume H3: Adj17 6 8.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_9 : Adj17 6 2 -> Adj17 2 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 9. assume H3: Adj17 6 9.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_10 : Adj17 6 2 -> Adj17 2 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 10. assume H3: Adj17 6 10.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_11 : Adj17 6 2 -> Adj17 2 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 11. assume H3: Adj17 6 11.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_12 : Adj17 6 2 -> Adj17 2 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 12. assume H3: Adj17 6 12.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_13 : Adj17 6 2 -> Adj17 2 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 13. assume H3: Adj17 6 13.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_14 : Adj17 6 2 -> Adj17 2 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 14. assume H3: Adj17 6 14.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_15 : Adj17 6 2 -> Adj17 2 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 15. assume H3: Adj17 6 15.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_2_16 : Adj17 6 2 -> Adj17 2 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 2. assume H2: Adj17 2 16. assume H3: Adj17 6 16.
exact Adj17_not_6_2 H1.
Qed.

Theorem tf_6_3_0 : Adj17 6 3 -> Adj17 3 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 0. assume H3: Adj17 6 0.
exact Adj17_not_3_0 H2.
Qed.

Theorem tf_6_3_1 : Adj17 6 3 -> Adj17 3 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 1. assume H3: Adj17 6 1.
exact Adj17_not_3_1 H2.
Qed.

Theorem tf_6_3_2 : Adj17 6 3 -> Adj17 3 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 2. assume H3: Adj17 6 2.
exact Adj17_not_3_2 H2.
Qed.

Theorem tf_6_3_3 : Adj17 6 3 -> Adj17 3 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 3. assume H3: Adj17 6 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_6_3_4 : Adj17 6 3 -> Adj17 3 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 4. assume H3: Adj17 6 4.
exact Adj17_not_3_4 H2.
Qed.

Theorem tf_6_3_5 : Adj17 6 3 -> Adj17 3 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 5. assume H3: Adj17 6 5.
exact Adj17_not_3_5 H2.
Qed.

Theorem tf_6_3_6 : Adj17 6 3 -> Adj17 3 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_3_7 : Adj17 6 3 -> Adj17 3 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 7. assume H3: Adj17 6 7.
exact Adj17_not_3_7 H2.
Qed.

Theorem tf_6_3_8 : Adj17 6 3 -> Adj17 3 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 8. assume H3: Adj17 6 8.
exact Adj17_not_6_8 H3.
Qed.

Theorem tf_6_3_9 : Adj17 6 3 -> Adj17 3 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 9. assume H3: Adj17 6 9.
exact Adj17_not_3_9 H2.
Qed.

Theorem tf_6_3_10 : Adj17 6 3 -> Adj17 3 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 10. assume H3: Adj17 6 10.
exact Adj17_not_3_10 H2.
Qed.

Theorem tf_6_3_11 : Adj17 6 3 -> Adj17 3 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 11. assume H3: Adj17 6 11.
exact Adj17_not_3_11 H2.
Qed.

Theorem tf_6_3_12 : Adj17 6 3 -> Adj17 3 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 12. assume H3: Adj17 6 12.
exact Adj17_not_3_12 H2.
Qed.

Theorem tf_6_3_13 : Adj17 6 3 -> Adj17 3 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 13. assume H3: Adj17 6 13.
exact Adj17_not_6_13 H3.
Qed.

Theorem tf_6_3_14 : Adj17 6 3 -> Adj17 3 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 14. assume H3: Adj17 6 14.
exact Adj17_not_3_14 H2.
Qed.

Theorem tf_6_3_15 : Adj17 6 3 -> Adj17 3 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 15. assume H3: Adj17 6 15.
exact Adj17_not_6_15 H3.
Qed.

Theorem tf_6_3_16 : Adj17 6 3 -> Adj17 3 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 3. assume H2: Adj17 3 16. assume H3: Adj17 6 16.
exact Adj17_not_6_16 H3.
Qed.

Theorem tf_6_4_0 : Adj17 6 4 -> Adj17 4 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 0. assume H3: Adj17 6 0.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_1 : Adj17 6 4 -> Adj17 4 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 1. assume H3: Adj17 6 1.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_2 : Adj17 6 4 -> Adj17 4 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 2. assume H3: Adj17 6 2.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_3 : Adj17 6 4 -> Adj17 4 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 3. assume H3: Adj17 6 3.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_4 : Adj17 6 4 -> Adj17 4 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 4. assume H3: Adj17 6 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_6_4_5 : Adj17 6 4 -> Adj17 4 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 5. assume H3: Adj17 6 5.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_6 : Adj17 6 4 -> Adj17 4 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_4_7 : Adj17 6 4 -> Adj17 4 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 7. assume H3: Adj17 6 7.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_8 : Adj17 6 4 -> Adj17 4 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 8. assume H3: Adj17 6 8.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_9 : Adj17 6 4 -> Adj17 4 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 9. assume H3: Adj17 6 9.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_10 : Adj17 6 4 -> Adj17 4 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 10. assume H3: Adj17 6 10.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_11 : Adj17 6 4 -> Adj17 4 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 11. assume H3: Adj17 6 11.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_12 : Adj17 6 4 -> Adj17 4 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 12. assume H3: Adj17 6 12.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_13 : Adj17 6 4 -> Adj17 4 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 13. assume H3: Adj17 6 13.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_14 : Adj17 6 4 -> Adj17 4 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 14. assume H3: Adj17 6 14.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_15 : Adj17 6 4 -> Adj17 4 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 15. assume H3: Adj17 6 15.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_4_16 : Adj17 6 4 -> Adj17 4 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 4. assume H2: Adj17 4 16. assume H3: Adj17 6 16.
exact Adj17_not_6_4 H1.
Qed.

Theorem tf_6_5_0 : Adj17 6 5 -> Adj17 5 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 0. assume H3: Adj17 6 0.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_1 : Adj17 6 5 -> Adj17 5 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 1. assume H3: Adj17 6 1.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_2 : Adj17 6 5 -> Adj17 5 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 2. assume H3: Adj17 6 2.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_3 : Adj17 6 5 -> Adj17 5 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 3. assume H3: Adj17 6 3.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_4 : Adj17 6 5 -> Adj17 5 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 4. assume H3: Adj17 6 4.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_5 : Adj17 6 5 -> Adj17 5 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 5. assume H3: Adj17 6 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_6_5_6 : Adj17 6 5 -> Adj17 5 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_5_7 : Adj17 6 5 -> Adj17 5 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 7. assume H3: Adj17 6 7.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_8 : Adj17 6 5 -> Adj17 5 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 8. assume H3: Adj17 6 8.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_9 : Adj17 6 5 -> Adj17 5 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 9. assume H3: Adj17 6 9.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_10 : Adj17 6 5 -> Adj17 5 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 10. assume H3: Adj17 6 10.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_11 : Adj17 6 5 -> Adj17 5 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 11. assume H3: Adj17 6 11.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_12 : Adj17 6 5 -> Adj17 5 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 12. assume H3: Adj17 6 12.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_13 : Adj17 6 5 -> Adj17 5 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 13. assume H3: Adj17 6 13.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_14 : Adj17 6 5 -> Adj17 5 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 14. assume H3: Adj17 6 14.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_15 : Adj17 6 5 -> Adj17 5 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 15. assume H3: Adj17 6 15.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_5_16 : Adj17 6 5 -> Adj17 5 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 5. assume H2: Adj17 5 16. assume H3: Adj17 6 16.
exact Adj17_not_6_5 H1.
Qed.

Theorem tf_6_6_0 : Adj17 6 6 -> Adj17 6 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 0. assume H3: Adj17 6 0.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_1 : Adj17 6 6 -> Adj17 6 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 1. assume H3: Adj17 6 1.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_2 : Adj17 6 6 -> Adj17 6 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 2. assume H3: Adj17 6 2.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_3 : Adj17 6 6 -> Adj17 6 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 3. assume H3: Adj17 6 3.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_4 : Adj17 6 6 -> Adj17 6 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 4. assume H3: Adj17 6 4.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_5 : Adj17 6 6 -> Adj17 6 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 5. assume H3: Adj17 6 5.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_6 : Adj17 6 6 -> Adj17 6 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_7 : Adj17 6 6 -> Adj17 6 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 7. assume H3: Adj17 6 7.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_8 : Adj17 6 6 -> Adj17 6 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 8. assume H3: Adj17 6 8.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_9 : Adj17 6 6 -> Adj17 6 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 9. assume H3: Adj17 6 9.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_10 : Adj17 6 6 -> Adj17 6 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 10. assume H3: Adj17 6 10.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_11 : Adj17 6 6 -> Adj17 6 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 11. assume H3: Adj17 6 11.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_12 : Adj17 6 6 -> Adj17 6 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 12. assume H3: Adj17 6 12.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_13 : Adj17 6 6 -> Adj17 6 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 13. assume H3: Adj17 6 13.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_14 : Adj17 6 6 -> Adj17 6 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 14. assume H3: Adj17 6 14.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_15 : Adj17 6 6 -> Adj17 6 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 15. assume H3: Adj17 6 15.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_6_16 : Adj17 6 6 -> Adj17 6 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 6. assume H2: Adj17 6 16. assume H3: Adj17 6 16.
exact Adj17_not_6_6 H1.
Qed.

Theorem tf_6_7_0 : Adj17 6 7 -> Adj17 7 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 0. assume H3: Adj17 6 0.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_1 : Adj17 6 7 -> Adj17 7 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 1. assume H3: Adj17 6 1.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_2 : Adj17 6 7 -> Adj17 7 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 2. assume H3: Adj17 6 2.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_3 : Adj17 6 7 -> Adj17 7 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 3. assume H3: Adj17 6 3.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_4 : Adj17 6 7 -> Adj17 7 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 4. assume H3: Adj17 6 4.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_5 : Adj17 6 7 -> Adj17 7 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 5. assume H3: Adj17 6 5.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_6 : Adj17 6 7 -> Adj17 7 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_7_7 : Adj17 6 7 -> Adj17 7 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 7. assume H3: Adj17 6 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_6_7_8 : Adj17 6 7 -> Adj17 7 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 8. assume H3: Adj17 6 8.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_9 : Adj17 6 7 -> Adj17 7 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 9. assume H3: Adj17 6 9.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_10 : Adj17 6 7 -> Adj17 7 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 10. assume H3: Adj17 6 10.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_11 : Adj17 6 7 -> Adj17 7 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 11. assume H3: Adj17 6 11.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_12 : Adj17 6 7 -> Adj17 7 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 12. assume H3: Adj17 6 12.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_13 : Adj17 6 7 -> Adj17 7 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 13. assume H3: Adj17 6 13.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_14 : Adj17 6 7 -> Adj17 7 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 14. assume H3: Adj17 6 14.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_15 : Adj17 6 7 -> Adj17 7 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 15. assume H3: Adj17 6 15.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_7_16 : Adj17 6 7 -> Adj17 7 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 7. assume H2: Adj17 7 16. assume H3: Adj17 6 16.
exact Adj17_not_6_7 H1.
Qed.

Theorem tf_6_8_0 : Adj17 6 8 -> Adj17 8 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 0. assume H3: Adj17 6 0.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_1 : Adj17 6 8 -> Adj17 8 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 1. assume H3: Adj17 6 1.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_2 : Adj17 6 8 -> Adj17 8 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 2. assume H3: Adj17 6 2.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_3 : Adj17 6 8 -> Adj17 8 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 3. assume H3: Adj17 6 3.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_4 : Adj17 6 8 -> Adj17 8 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 4. assume H3: Adj17 6 4.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_5 : Adj17 6 8 -> Adj17 8 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 5. assume H3: Adj17 6 5.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_6 : Adj17 6 8 -> Adj17 8 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_8_7 : Adj17 6 8 -> Adj17 8 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 7. assume H3: Adj17 6 7.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_8 : Adj17 6 8 -> Adj17 8 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 8. assume H3: Adj17 6 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_6_8_9 : Adj17 6 8 -> Adj17 8 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 9. assume H3: Adj17 6 9.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_10 : Adj17 6 8 -> Adj17 8 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 10. assume H3: Adj17 6 10.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_11 : Adj17 6 8 -> Adj17 8 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 11. assume H3: Adj17 6 11.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_12 : Adj17 6 8 -> Adj17 8 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 12. assume H3: Adj17 6 12.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_13 : Adj17 6 8 -> Adj17 8 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 13. assume H3: Adj17 6 13.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_14 : Adj17 6 8 -> Adj17 8 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 14. assume H3: Adj17 6 14.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_15 : Adj17 6 8 -> Adj17 8 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 15. assume H3: Adj17 6 15.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_8_16 : Adj17 6 8 -> Adj17 8 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 8. assume H2: Adj17 8 16. assume H3: Adj17 6 16.
exact Adj17_not_6_8 H1.
Qed.

Theorem tf_6_9_0 : Adj17 6 9 -> Adj17 9 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 0. assume H3: Adj17 6 0.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_1 : Adj17 6 9 -> Adj17 9 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 1. assume H3: Adj17 6 1.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_2 : Adj17 6 9 -> Adj17 9 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 2. assume H3: Adj17 6 2.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_3 : Adj17 6 9 -> Adj17 9 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 3. assume H3: Adj17 6 3.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_4 : Adj17 6 9 -> Adj17 9 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 4. assume H3: Adj17 6 4.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_5 : Adj17 6 9 -> Adj17 9 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 5. assume H3: Adj17 6 5.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_6 : Adj17 6 9 -> Adj17 9 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_9_7 : Adj17 6 9 -> Adj17 9 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 7. assume H3: Adj17 6 7.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_8 : Adj17 6 9 -> Adj17 9 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 8. assume H3: Adj17 6 8.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_9 : Adj17 6 9 -> Adj17 9 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 9. assume H3: Adj17 6 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_6_9_10 : Adj17 6 9 -> Adj17 9 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 10. assume H3: Adj17 6 10.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_11 : Adj17 6 9 -> Adj17 9 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 11. assume H3: Adj17 6 11.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_12 : Adj17 6 9 -> Adj17 9 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 12. assume H3: Adj17 6 12.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_13 : Adj17 6 9 -> Adj17 9 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 13. assume H3: Adj17 6 13.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_14 : Adj17 6 9 -> Adj17 9 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 14. assume H3: Adj17 6 14.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_15 : Adj17 6 9 -> Adj17 9 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 15. assume H3: Adj17 6 15.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_9_16 : Adj17 6 9 -> Adj17 9 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 9. assume H2: Adj17 9 16. assume H3: Adj17 6 16.
exact Adj17_not_6_9 H1.
Qed.

Theorem tf_6_10_0 : Adj17 6 10 -> Adj17 10 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 0. assume H3: Adj17 6 0.
exact Adj17_not_10_0 H2.
Qed.

Theorem tf_6_10_1 : Adj17 6 10 -> Adj17 10 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 1. assume H3: Adj17 6 1.
exact Adj17_not_10_1 H2.
Qed.

Theorem tf_6_10_2 : Adj17 6 10 -> Adj17 10 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 2. assume H3: Adj17 6 2.
exact Adj17_not_6_2 H3.
Qed.

Theorem tf_6_10_3 : Adj17 6 10 -> Adj17 10 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 3. assume H3: Adj17 6 3.
exact Adj17_not_10_3 H2.
Qed.

Theorem tf_6_10_4 : Adj17 6 10 -> Adj17 10 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 4. assume H3: Adj17 6 4.
exact Adj17_not_10_4 H2.
Qed.

Theorem tf_6_10_5 : Adj17 6 10 -> Adj17 10 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 5. assume H3: Adj17 6 5.
exact Adj17_not_6_5 H3.
Qed.

Theorem tf_6_10_6 : Adj17 6 10 -> Adj17 10 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_10_7 : Adj17 6 10 -> Adj17 10 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 7. assume H3: Adj17 6 7.
exact Adj17_not_6_7 H3.
Qed.

Theorem tf_6_10_8 : Adj17 6 10 -> Adj17 10 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 8. assume H3: Adj17 6 8.
exact Adj17_not_10_8 H2.
Qed.

Theorem tf_6_10_9 : Adj17 6 10 -> Adj17 10 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 9. assume H3: Adj17 6 9.
exact Adj17_not_10_9 H2.
Qed.

Theorem tf_6_10_10 : Adj17 6 10 -> Adj17 10 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 10. assume H3: Adj17 6 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_6_10_11 : Adj17 6 10 -> Adj17 10 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 11. assume H3: Adj17 6 11.
exact Adj17_not_10_11 H2.
Qed.

Theorem tf_6_10_12 : Adj17 6 10 -> Adj17 10 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 12. assume H3: Adj17 6 12.
exact Adj17_not_10_12 H2.
Qed.

Theorem tf_6_10_13 : Adj17 6 10 -> Adj17 10 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 13. assume H3: Adj17 6 13.
exact Adj17_not_10_13 H2.
Qed.

Theorem tf_6_10_14 : Adj17 6 10 -> Adj17 10 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 14. assume H3: Adj17 6 14.
exact Adj17_not_10_14 H2.
Qed.

Theorem tf_6_10_15 : Adj17 6 10 -> Adj17 10 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 15. assume H3: Adj17 6 15.
exact Adj17_not_10_15 H2.
Qed.

Theorem tf_6_10_16 : Adj17 6 10 -> Adj17 10 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 10. assume H2: Adj17 10 16. assume H3: Adj17 6 16.
exact Adj17_not_6_16 H3.
Qed.

Theorem tf_6_11_0 : Adj17 6 11 -> Adj17 11 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 0. assume H3: Adj17 6 0.
exact Adj17_not_11_0 H2.
Qed.

Theorem tf_6_11_1 : Adj17 6 11 -> Adj17 11 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 1. assume H3: Adj17 6 1.
exact Adj17_not_6_1 H3.
Qed.

Theorem tf_6_11_2 : Adj17 6 11 -> Adj17 11 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 2. assume H3: Adj17 6 2.
exact Adj17_not_11_2 H2.
Qed.

Theorem tf_6_11_3 : Adj17 6 11 -> Adj17 11 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 3. assume H3: Adj17 6 3.
exact Adj17_not_11_3 H2.
Qed.

Theorem tf_6_11_4 : Adj17 6 11 -> Adj17 11 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 4. assume H3: Adj17 6 4.
exact Adj17_not_11_4 H2.
Qed.

Theorem tf_6_11_5 : Adj17 6 11 -> Adj17 11 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 5. assume H3: Adj17 6 5.
exact Adj17_not_6_5 H3.
Qed.

Theorem tf_6_11_6 : Adj17 6 11 -> Adj17 11 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_11_7 : Adj17 6 11 -> Adj17 11 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 7. assume H3: Adj17 6 7.
exact Adj17_not_11_7 H2.
Qed.

Theorem tf_6_11_8 : Adj17 6 11 -> Adj17 11 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 8. assume H3: Adj17 6 8.
exact Adj17_not_6_8 H3.
Qed.

Theorem tf_6_11_9 : Adj17 6 11 -> Adj17 11 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 9. assume H3: Adj17 6 9.
exact Adj17_not_11_9 H2.
Qed.

Theorem tf_6_11_10 : Adj17 6 11 -> Adj17 11 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 10. assume H3: Adj17 6 10.
exact Adj17_not_11_10 H2.
Qed.

Theorem tf_6_11_11 : Adj17 6 11 -> Adj17 11 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 11. assume H3: Adj17 6 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_6_11_12 : Adj17 6 11 -> Adj17 11 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 12. assume H3: Adj17 6 12.
exact Adj17_not_11_12 H2.
Qed.

Theorem tf_6_11_13 : Adj17 6 11 -> Adj17 11 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 13. assume H3: Adj17 6 13.
exact Adj17_not_11_13 H2.
Qed.

Theorem tf_6_11_14 : Adj17 6 11 -> Adj17 11 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 14. assume H3: Adj17 6 14.
exact Adj17_not_11_14 H2.
Qed.

Theorem tf_6_11_15 : Adj17 6 11 -> Adj17 11 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 15. assume H3: Adj17 6 15.
exact Adj17_not_6_15 H3.
Qed.

Theorem tf_6_11_16 : Adj17 6 11 -> Adj17 11 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 11. assume H2: Adj17 11 16. assume H3: Adj17 6 16.
exact Adj17_not_11_16 H2.
Qed.

Theorem tf_6_12_0 : Adj17 6 12 -> Adj17 12 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 0. assume H3: Adj17 6 0.
exact Adj17_not_12_0 H2.
Qed.

Theorem tf_6_12_1 : Adj17 6 12 -> Adj17 12 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 1. assume H3: Adj17 6 1.
exact Adj17_not_12_1 H2.
Qed.

Theorem tf_6_12_2 : Adj17 6 12 -> Adj17 12 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 2. assume H3: Adj17 6 2.
exact Adj17_not_6_2 H3.
Qed.

Theorem tf_6_12_3 : Adj17 6 12 -> Adj17 12 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 3. assume H3: Adj17 6 3.
exact Adj17_not_12_3 H2.
Qed.

Theorem tf_6_12_4 : Adj17 6 12 -> Adj17 12 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 4. assume H3: Adj17 6 4.
exact Adj17_not_6_4 H3.
Qed.

Theorem tf_6_12_5 : Adj17 6 12 -> Adj17 12 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 5. assume H3: Adj17 6 5.
exact Adj17_not_12_5 H2.
Qed.

Theorem tf_6_12_6 : Adj17 6 12 -> Adj17 12 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_12_7 : Adj17 6 12 -> Adj17 12 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 7. assume H3: Adj17 6 7.
exact Adj17_not_12_7 H2.
Qed.

Theorem tf_6_12_8 : Adj17 6 12 -> Adj17 12 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 8. assume H3: Adj17 6 8.
exact Adj17_not_12_8 H2.
Qed.

Theorem tf_6_12_9 : Adj17 6 12 -> Adj17 12 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 9. assume H3: Adj17 6 9.
exact Adj17_not_6_9 H3.
Qed.

Theorem tf_6_12_10 : Adj17 6 12 -> Adj17 12 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 10. assume H3: Adj17 6 10.
exact Adj17_not_12_10 H2.
Qed.

Theorem tf_6_12_11 : Adj17 6 12 -> Adj17 12 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 11. assume H3: Adj17 6 11.
exact Adj17_not_12_11 H2.
Qed.

Theorem tf_6_12_12 : Adj17 6 12 -> Adj17 12 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 12. assume H3: Adj17 6 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_6_12_13 : Adj17 6 12 -> Adj17 12 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 13. assume H3: Adj17 6 13.
exact Adj17_not_6_13 H3.
Qed.

Theorem tf_6_12_14 : Adj17 6 12 -> Adj17 12 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 14. assume H3: Adj17 6 14.
exact Adj17_not_12_14 H2.
Qed.

Theorem tf_6_12_15 : Adj17 6 12 -> Adj17 12 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 15. assume H3: Adj17 6 15.
exact Adj17_not_12_15 H2.
Qed.

Theorem tf_6_12_16 : Adj17 6 12 -> Adj17 12 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 12. assume H2: Adj17 12 16. assume H3: Adj17 6 16.
exact Adj17_not_12_16 H2.
Qed.

Theorem tf_6_13_0 : Adj17 6 13 -> Adj17 13 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 0. assume H3: Adj17 6 0.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_1 : Adj17 6 13 -> Adj17 13 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 1. assume H3: Adj17 6 1.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_2 : Adj17 6 13 -> Adj17 13 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 2. assume H3: Adj17 6 2.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_3 : Adj17 6 13 -> Adj17 13 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 3. assume H3: Adj17 6 3.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_4 : Adj17 6 13 -> Adj17 13 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 4. assume H3: Adj17 6 4.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_5 : Adj17 6 13 -> Adj17 13 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 5. assume H3: Adj17 6 5.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_6 : Adj17 6 13 -> Adj17 13 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_13_7 : Adj17 6 13 -> Adj17 13 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 7. assume H3: Adj17 6 7.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_8 : Adj17 6 13 -> Adj17 13 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 8. assume H3: Adj17 6 8.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_9 : Adj17 6 13 -> Adj17 13 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 9. assume H3: Adj17 6 9.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_10 : Adj17 6 13 -> Adj17 13 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 10. assume H3: Adj17 6 10.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_11 : Adj17 6 13 -> Adj17 13 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 11. assume H3: Adj17 6 11.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_12 : Adj17 6 13 -> Adj17 13 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 12. assume H3: Adj17 6 12.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_13 : Adj17 6 13 -> Adj17 13 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 13. assume H3: Adj17 6 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_6_13_14 : Adj17 6 13 -> Adj17 13 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 14. assume H3: Adj17 6 14.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_15 : Adj17 6 13 -> Adj17 13 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 15. assume H3: Adj17 6 15.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_13_16 : Adj17 6 13 -> Adj17 13 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 13. assume H2: Adj17 13 16. assume H3: Adj17 6 16.
exact Adj17_not_6_13 H1.
Qed.

Theorem tf_6_14_0 : Adj17 6 14 -> Adj17 14 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 0. assume H3: Adj17 6 0.
exact Adj17_not_6_0 H3.
Qed.

Theorem tf_6_14_1 : Adj17 6 14 -> Adj17 14 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 1. assume H3: Adj17 6 1.
exact Adj17_not_14_1 H2.
Qed.

Theorem tf_6_14_2 : Adj17 6 14 -> Adj17 14 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 2. assume H3: Adj17 6 2.
exact Adj17_not_14_2 H2.
Qed.

Theorem tf_6_14_3 : Adj17 6 14 -> Adj17 14 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 3. assume H3: Adj17 6 3.
exact Adj17_not_14_3 H2.
Qed.

Theorem tf_6_14_4 : Adj17 6 14 -> Adj17 14 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 4. assume H3: Adj17 6 4.
exact Adj17_not_6_4 H3.
Qed.

Theorem tf_6_14_5 : Adj17 6 14 -> Adj17 14 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 5. assume H3: Adj17 6 5.
exact Adj17_not_14_5 H2.
Qed.

Theorem tf_6_14_6 : Adj17 6 14 -> Adj17 14 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_14_7 : Adj17 6 14 -> Adj17 14 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 7. assume H3: Adj17 6 7.
exact Adj17_not_14_7 H2.
Qed.

Theorem tf_6_14_8 : Adj17 6 14 -> Adj17 14 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 8. assume H3: Adj17 6 8.
exact Adj17_not_6_8 H3.
Qed.

Theorem tf_6_14_9 : Adj17 6 14 -> Adj17 14 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 9. assume H3: Adj17 6 9.
exact Adj17_not_14_9 H2.
Qed.

Theorem tf_6_14_10 : Adj17 6 14 -> Adj17 14 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 10. assume H3: Adj17 6 10.
exact Adj17_not_14_10 H2.
Qed.

Theorem tf_6_14_11 : Adj17 6 14 -> Adj17 14 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 11. assume H3: Adj17 6 11.
exact Adj17_not_14_11 H2.
Qed.

Theorem tf_6_14_12 : Adj17 6 14 -> Adj17 14 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 12. assume H3: Adj17 6 12.
exact Adj17_not_14_12 H2.
Qed.

Theorem tf_6_14_13 : Adj17 6 14 -> Adj17 14 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 13. assume H3: Adj17 6 13.
exact Adj17_not_6_13 H3.
Qed.

Theorem tf_6_14_14 : Adj17 6 14 -> Adj17 14 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 14. assume H3: Adj17 6 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_6_14_15 : Adj17 6 14 -> Adj17 14 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 15. assume H3: Adj17 6 15.
exact Adj17_not_14_15 H2.
Qed.

Theorem tf_6_14_16 : Adj17 6 14 -> Adj17 14 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 14. assume H2: Adj17 14 16. assume H3: Adj17 6 16.
exact Adj17_not_14_16 H2.
Qed.

Theorem tf_6_15_0 : Adj17 6 15 -> Adj17 15 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 0. assume H3: Adj17 6 0.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_1 : Adj17 6 15 -> Adj17 15 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 1. assume H3: Adj17 6 1.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_2 : Adj17 6 15 -> Adj17 15 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 2. assume H3: Adj17 6 2.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_3 : Adj17 6 15 -> Adj17 15 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 3. assume H3: Adj17 6 3.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_4 : Adj17 6 15 -> Adj17 15 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 4. assume H3: Adj17 6 4.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_5 : Adj17 6 15 -> Adj17 15 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 5. assume H3: Adj17 6 5.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_6 : Adj17 6 15 -> Adj17 15 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_15_7 : Adj17 6 15 -> Adj17 15 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 7. assume H3: Adj17 6 7.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_8 : Adj17 6 15 -> Adj17 15 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 8. assume H3: Adj17 6 8.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_9 : Adj17 6 15 -> Adj17 15 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 9. assume H3: Adj17 6 9.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_10 : Adj17 6 15 -> Adj17 15 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 10. assume H3: Adj17 6 10.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_11 : Adj17 6 15 -> Adj17 15 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 11. assume H3: Adj17 6 11.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_12 : Adj17 6 15 -> Adj17 15 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 12. assume H3: Adj17 6 12.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_13 : Adj17 6 15 -> Adj17 15 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 13. assume H3: Adj17 6 13.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_14 : Adj17 6 15 -> Adj17 15 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 14. assume H3: Adj17 6 14.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_15_15 : Adj17 6 15 -> Adj17 15 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 15. assume H3: Adj17 6 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_6_15_16 : Adj17 6 15 -> Adj17 15 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 15. assume H2: Adj17 15 16. assume H3: Adj17 6 16.
exact Adj17_not_6_15 H1.
Qed.

Theorem tf_6_16_0 : Adj17 6 16 -> Adj17 16 0 -> Adj17 6 0 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 0. assume H3: Adj17 6 0.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_1 : Adj17 6 16 -> Adj17 16 1 -> Adj17 6 1 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 1. assume H3: Adj17 6 1.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_2 : Adj17 6 16 -> Adj17 16 2 -> Adj17 6 2 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 2. assume H3: Adj17 6 2.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_3 : Adj17 6 16 -> Adj17 16 3 -> Adj17 6 3 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 3. assume H3: Adj17 6 3.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_4 : Adj17 6 16 -> Adj17 16 4 -> Adj17 6 4 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 4. assume H3: Adj17 6 4.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_5 : Adj17 6 16 -> Adj17 16 5 -> Adj17 6 5 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 5. assume H3: Adj17 6 5.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_6 : Adj17 6 16 -> Adj17 16 6 -> Adj17 6 6 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 6. assume H3: Adj17 6 6.
exact Adj17_not_6_6 H3.
Qed.

Theorem tf_6_16_7 : Adj17 6 16 -> Adj17 16 7 -> Adj17 6 7 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 7. assume H3: Adj17 6 7.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_8 : Adj17 6 16 -> Adj17 16 8 -> Adj17 6 8 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 8. assume H3: Adj17 6 8.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_9 : Adj17 6 16 -> Adj17 16 9 -> Adj17 6 9 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 9. assume H3: Adj17 6 9.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_10 : Adj17 6 16 -> Adj17 16 10 -> Adj17 6 10 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 10. assume H3: Adj17 6 10.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_11 : Adj17 6 16 -> Adj17 16 11 -> Adj17 6 11 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 11. assume H3: Adj17 6 11.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_12 : Adj17 6 16 -> Adj17 16 12 -> Adj17 6 12 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 12. assume H3: Adj17 6 12.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_13 : Adj17 6 16 -> Adj17 16 13 -> Adj17 6 13 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 13. assume H3: Adj17 6 13.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_14 : Adj17 6 16 -> Adj17 16 14 -> Adj17 6 14 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 14. assume H3: Adj17 6 14.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_15 : Adj17 6 16 -> Adj17 16 15 -> Adj17 6 15 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 15. assume H3: Adj17 6 15.
exact Adj17_not_6_16 H1.
Qed.

Theorem tf_6_16_16 : Adj17 6 16 -> Adj17 16 16 -> Adj17 6 16 -> False.
assume H1: Adj17 6 16. assume H2: Adj17 16 16. assume H3: Adj17 6 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_7_0_0 : Adj17 7 0 -> Adj17 0 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 0. assume H3: Adj17 7 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_7_0_1 : Adj17 7 0 -> Adj17 0 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 1. assume H3: Adj17 7 1.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_2 : Adj17 7 0 -> Adj17 0 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 2. assume H3: Adj17 7 2.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_3 : Adj17 7 0 -> Adj17 0 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 3. assume H3: Adj17 7 3.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_4 : Adj17 7 0 -> Adj17 0 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 4. assume H3: Adj17 7 4.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_5 : Adj17 7 0 -> Adj17 0 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 5. assume H3: Adj17 7 5.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_6 : Adj17 7 0 -> Adj17 0 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 6. assume H3: Adj17 7 6.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_7 : Adj17 7 0 -> Adj17 0 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_0_8 : Adj17 7 0 -> Adj17 0 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 8. assume H3: Adj17 7 8.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_9 : Adj17 7 0 -> Adj17 0 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 9. assume H3: Adj17 7 9.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_10 : Adj17 7 0 -> Adj17 0 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 10. assume H3: Adj17 7 10.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_11 : Adj17 7 0 -> Adj17 0 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 11. assume H3: Adj17 7 11.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_12 : Adj17 7 0 -> Adj17 0 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 12. assume H3: Adj17 7 12.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_13 : Adj17 7 0 -> Adj17 0 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 13. assume H3: Adj17 7 13.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_14 : Adj17 7 0 -> Adj17 0 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 14. assume H3: Adj17 7 14.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_15 : Adj17 7 0 -> Adj17 0 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 15. assume H3: Adj17 7 15.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_0_16 : Adj17 7 0 -> Adj17 0 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 0. assume H2: Adj17 0 16. assume H3: Adj17 7 16.
exact Adj17_not_7_0 H1.
Qed.

Theorem tf_7_1_0 : Adj17 7 1 -> Adj17 1 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 0. assume H3: Adj17 7 0.
exact Adj17_not_1_0 H2.
Qed.

Theorem tf_7_1_1 : Adj17 7 1 -> Adj17 1 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 1. assume H3: Adj17 7 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_7_1_2 : Adj17 7 1 -> Adj17 1 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 2. assume H3: Adj17 7 2.
exact Adj17_not_1_2 H2.
Qed.

Theorem tf_7_1_3 : Adj17 7 1 -> Adj17 1 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 3. assume H3: Adj17 7 3.
exact Adj17_not_1_3 H2.
Qed.

Theorem tf_7_1_4 : Adj17 7 1 -> Adj17 1 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 4. assume H3: Adj17 7 4.
exact Adj17_not_1_4 H2.
Qed.

Theorem tf_7_1_5 : Adj17 7 1 -> Adj17 1 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 5. assume H3: Adj17 7 5.
exact Adj17_not_1_5 H2.
Qed.

Theorem tf_7_1_6 : Adj17 7 1 -> Adj17 1 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 6. assume H3: Adj17 7 6.
exact Adj17_not_1_6 H2.
Qed.

Theorem tf_7_1_7 : Adj17 7 1 -> Adj17 1 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_1_8 : Adj17 7 1 -> Adj17 1 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 8. assume H3: Adj17 7 8.
exact Adj17_not_1_8 H2.
Qed.

Theorem tf_7_1_9 : Adj17 7 1 -> Adj17 1 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 9. assume H3: Adj17 7 9.
exact Adj17_not_1_9 H2.
Qed.

Theorem tf_7_1_10 : Adj17 7 1 -> Adj17 1 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 10. assume H3: Adj17 7 10.
exact Adj17_not_1_10 H2.
Qed.

Theorem tf_7_1_11 : Adj17 7 1 -> Adj17 1 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 11. assume H3: Adj17 7 11.
exact Adj17_not_7_11 H3.
Qed.

Theorem tf_7_1_12 : Adj17 7 1 -> Adj17 1 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 12. assume H3: Adj17 7 12.
exact Adj17_not_1_12 H2.
Qed.

Theorem tf_7_1_13 : Adj17 7 1 -> Adj17 1 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 13. assume H3: Adj17 7 13.
exact Adj17_not_7_13 H3.
Qed.

Theorem tf_7_1_14 : Adj17 7 1 -> Adj17 1 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 14. assume H3: Adj17 7 14.
exact Adj17_not_1_14 H2.
Qed.

Theorem tf_7_1_15 : Adj17 7 1 -> Adj17 1 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 15. assume H3: Adj17 7 15.
exact Adj17_not_1_15 H2.
Qed.

Theorem tf_7_1_16 : Adj17 7 1 -> Adj17 1 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 1. assume H2: Adj17 1 16. assume H3: Adj17 7 16.
exact Adj17_not_7_16 H3.
Qed.

Theorem tf_7_2_0 : Adj17 7 2 -> Adj17 2 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 0. assume H3: Adj17 7 0.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_1 : Adj17 7 2 -> Adj17 2 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 1. assume H3: Adj17 7 1.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_2 : Adj17 7 2 -> Adj17 2 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 2. assume H3: Adj17 7 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_7_2_3 : Adj17 7 2 -> Adj17 2 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 3. assume H3: Adj17 7 3.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_4 : Adj17 7 2 -> Adj17 2 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 4. assume H3: Adj17 7 4.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_5 : Adj17 7 2 -> Adj17 2 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 5. assume H3: Adj17 7 5.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_6 : Adj17 7 2 -> Adj17 2 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 6. assume H3: Adj17 7 6.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_7 : Adj17 7 2 -> Adj17 2 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_2_8 : Adj17 7 2 -> Adj17 2 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 8. assume H3: Adj17 7 8.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_9 : Adj17 7 2 -> Adj17 2 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 9. assume H3: Adj17 7 9.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_10 : Adj17 7 2 -> Adj17 2 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 10. assume H3: Adj17 7 10.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_11 : Adj17 7 2 -> Adj17 2 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 11. assume H3: Adj17 7 11.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_12 : Adj17 7 2 -> Adj17 2 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 12. assume H3: Adj17 7 12.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_13 : Adj17 7 2 -> Adj17 2 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 13. assume H3: Adj17 7 13.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_14 : Adj17 7 2 -> Adj17 2 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 14. assume H3: Adj17 7 14.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_15 : Adj17 7 2 -> Adj17 2 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 15. assume H3: Adj17 7 15.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_2_16 : Adj17 7 2 -> Adj17 2 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 2. assume H2: Adj17 2 16. assume H3: Adj17 7 16.
exact Adj17_not_7_2 H1.
Qed.

Theorem tf_7_3_0 : Adj17 7 3 -> Adj17 3 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 0. assume H3: Adj17 7 0.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_1 : Adj17 7 3 -> Adj17 3 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 1. assume H3: Adj17 7 1.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_2 : Adj17 7 3 -> Adj17 3 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 2. assume H3: Adj17 7 2.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_3 : Adj17 7 3 -> Adj17 3 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 3. assume H3: Adj17 7 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_7_3_4 : Adj17 7 3 -> Adj17 3 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 4. assume H3: Adj17 7 4.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_5 : Adj17 7 3 -> Adj17 3 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 5. assume H3: Adj17 7 5.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_6 : Adj17 7 3 -> Adj17 3 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 6. assume H3: Adj17 7 6.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_7 : Adj17 7 3 -> Adj17 3 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_3_8 : Adj17 7 3 -> Adj17 3 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 8. assume H3: Adj17 7 8.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_9 : Adj17 7 3 -> Adj17 3 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 9. assume H3: Adj17 7 9.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_10 : Adj17 7 3 -> Adj17 3 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 10. assume H3: Adj17 7 10.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_11 : Adj17 7 3 -> Adj17 3 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 11. assume H3: Adj17 7 11.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_12 : Adj17 7 3 -> Adj17 3 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 12. assume H3: Adj17 7 12.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_13 : Adj17 7 3 -> Adj17 3 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 13. assume H3: Adj17 7 13.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_14 : Adj17 7 3 -> Adj17 3 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 14. assume H3: Adj17 7 14.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_15 : Adj17 7 3 -> Adj17 3 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 15. assume H3: Adj17 7 15.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_3_16 : Adj17 7 3 -> Adj17 3 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 3. assume H2: Adj17 3 16. assume H3: Adj17 7 16.
exact Adj17_not_7_3 H1.
Qed.

Theorem tf_7_4_0 : Adj17 7 4 -> Adj17 4 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 0. assume H3: Adj17 7 0.
exact Adj17_not_4_0 H2.
Qed.

Theorem tf_7_4_1 : Adj17 7 4 -> Adj17 4 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 1. assume H3: Adj17 7 1.
exact Adj17_not_4_1 H2.
Qed.

Theorem tf_7_4_2 : Adj17 7 4 -> Adj17 4 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 2. assume H3: Adj17 7 2.
exact Adj17_not_4_2 H2.
Qed.

Theorem tf_7_4_3 : Adj17 7 4 -> Adj17 4 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 3. assume H3: Adj17 7 3.
exact Adj17_not_4_3 H2.
Qed.

Theorem tf_7_4_4 : Adj17 7 4 -> Adj17 4 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 4. assume H3: Adj17 7 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_7_4_5 : Adj17 7 4 -> Adj17 4 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 5. assume H3: Adj17 7 5.
exact Adj17_not_7_5 H3.
Qed.

Theorem tf_7_4_6 : Adj17 7 4 -> Adj17 4 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 6. assume H3: Adj17 7 6.
exact Adj17_not_4_6 H2.
Qed.

Theorem tf_7_4_7 : Adj17 7 4 -> Adj17 4 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_4_8 : Adj17 7 4 -> Adj17 4 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 8. assume H3: Adj17 7 8.
exact Adj17_not_4_8 H2.
Qed.

Theorem tf_7_4_9 : Adj17 7 4 -> Adj17 4 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 9. assume H3: Adj17 7 9.
exact Adj17_not_4_9 H2.
Qed.

Theorem tf_7_4_10 : Adj17 7 4 -> Adj17 4 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 10. assume H3: Adj17 7 10.
exact Adj17_not_4_10 H2.
Qed.

Theorem tf_7_4_11 : Adj17 7 4 -> Adj17 4 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 11. assume H3: Adj17 7 11.
exact Adj17_not_4_11 H2.
Qed.

Theorem tf_7_4_12 : Adj17 7 4 -> Adj17 4 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 12. assume H3: Adj17 7 12.
exact Adj17_not_7_12 H3.
Qed.

Theorem tf_7_4_13 : Adj17 7 4 -> Adj17 4 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 13. assume H3: Adj17 7 13.
exact Adj17_not_4_13 H2.
Qed.

Theorem tf_7_4_14 : Adj17 7 4 -> Adj17 4 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 14. assume H3: Adj17 7 14.
exact Adj17_not_7_14 H3.
Qed.

Theorem tf_7_4_15 : Adj17 7 4 -> Adj17 4 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 15. assume H3: Adj17 7 15.
exact Adj17_not_4_15 H2.
Qed.

Theorem tf_7_4_16 : Adj17 7 4 -> Adj17 4 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 4. assume H2: Adj17 4 16. assume H3: Adj17 7 16.
exact Adj17_not_7_16 H3.
Qed.

Theorem tf_7_5_0 : Adj17 7 5 -> Adj17 5 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 0. assume H3: Adj17 7 0.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_1 : Adj17 7 5 -> Adj17 5 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 1. assume H3: Adj17 7 1.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_2 : Adj17 7 5 -> Adj17 5 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 2. assume H3: Adj17 7 2.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_3 : Adj17 7 5 -> Adj17 5 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 3. assume H3: Adj17 7 3.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_4 : Adj17 7 5 -> Adj17 5 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 4. assume H3: Adj17 7 4.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_5 : Adj17 7 5 -> Adj17 5 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 5. assume H3: Adj17 7 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_7_5_6 : Adj17 7 5 -> Adj17 5 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 6. assume H3: Adj17 7 6.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_7 : Adj17 7 5 -> Adj17 5 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_5_8 : Adj17 7 5 -> Adj17 5 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 8. assume H3: Adj17 7 8.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_9 : Adj17 7 5 -> Adj17 5 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 9. assume H3: Adj17 7 9.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_10 : Adj17 7 5 -> Adj17 5 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 10. assume H3: Adj17 7 10.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_11 : Adj17 7 5 -> Adj17 5 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 11. assume H3: Adj17 7 11.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_12 : Adj17 7 5 -> Adj17 5 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 12. assume H3: Adj17 7 12.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_13 : Adj17 7 5 -> Adj17 5 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 13. assume H3: Adj17 7 13.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_14 : Adj17 7 5 -> Adj17 5 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 14. assume H3: Adj17 7 14.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_15 : Adj17 7 5 -> Adj17 5 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 15. assume H3: Adj17 7 15.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_5_16 : Adj17 7 5 -> Adj17 5 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 5. assume H2: Adj17 5 16. assume H3: Adj17 7 16.
exact Adj17_not_7_5 H1.
Qed.

Theorem tf_7_6_0 : Adj17 7 6 -> Adj17 6 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 0. assume H3: Adj17 7 0.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_1 : Adj17 7 6 -> Adj17 6 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 1. assume H3: Adj17 7 1.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_2 : Adj17 7 6 -> Adj17 6 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 2. assume H3: Adj17 7 2.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_3 : Adj17 7 6 -> Adj17 6 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 3. assume H3: Adj17 7 3.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_4 : Adj17 7 6 -> Adj17 6 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 4. assume H3: Adj17 7 4.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_5 : Adj17 7 6 -> Adj17 6 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 5. assume H3: Adj17 7 5.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_6 : Adj17 7 6 -> Adj17 6 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 6. assume H3: Adj17 7 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_7_6_7 : Adj17 7 6 -> Adj17 6 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_6_8 : Adj17 7 6 -> Adj17 6 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 8. assume H3: Adj17 7 8.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_9 : Adj17 7 6 -> Adj17 6 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 9. assume H3: Adj17 7 9.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_10 : Adj17 7 6 -> Adj17 6 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 10. assume H3: Adj17 7 10.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_11 : Adj17 7 6 -> Adj17 6 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 11. assume H3: Adj17 7 11.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_12 : Adj17 7 6 -> Adj17 6 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 12. assume H3: Adj17 7 12.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_13 : Adj17 7 6 -> Adj17 6 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 13. assume H3: Adj17 7 13.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_14 : Adj17 7 6 -> Adj17 6 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 14. assume H3: Adj17 7 14.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_15 : Adj17 7 6 -> Adj17 6 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 15. assume H3: Adj17 7 15.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_6_16 : Adj17 7 6 -> Adj17 6 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 6. assume H2: Adj17 6 16. assume H3: Adj17 7 16.
exact Adj17_not_7_6 H1.
Qed.

Theorem tf_7_7_0 : Adj17 7 7 -> Adj17 7 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 0. assume H3: Adj17 7 0.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_1 : Adj17 7 7 -> Adj17 7 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 1. assume H3: Adj17 7 1.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_2 : Adj17 7 7 -> Adj17 7 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 2. assume H3: Adj17 7 2.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_3 : Adj17 7 7 -> Adj17 7 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 3. assume H3: Adj17 7 3.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_4 : Adj17 7 7 -> Adj17 7 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 4. assume H3: Adj17 7 4.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_5 : Adj17 7 7 -> Adj17 7 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 5. assume H3: Adj17 7 5.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_6 : Adj17 7 7 -> Adj17 7 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 6. assume H3: Adj17 7 6.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_7 : Adj17 7 7 -> Adj17 7 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_8 : Adj17 7 7 -> Adj17 7 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 8. assume H3: Adj17 7 8.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_9 : Adj17 7 7 -> Adj17 7 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 9. assume H3: Adj17 7 9.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_10 : Adj17 7 7 -> Adj17 7 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 10. assume H3: Adj17 7 10.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_11 : Adj17 7 7 -> Adj17 7 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 11. assume H3: Adj17 7 11.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_12 : Adj17 7 7 -> Adj17 7 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 12. assume H3: Adj17 7 12.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_13 : Adj17 7 7 -> Adj17 7 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 13. assume H3: Adj17 7 13.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_14 : Adj17 7 7 -> Adj17 7 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 14. assume H3: Adj17 7 14.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_15 : Adj17 7 7 -> Adj17 7 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 15. assume H3: Adj17 7 15.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_7_16 : Adj17 7 7 -> Adj17 7 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 7. assume H2: Adj17 7 16. assume H3: Adj17 7 16.
exact Adj17_not_7_7 H1.
Qed.

Theorem tf_7_8_0 : Adj17 7 8 -> Adj17 8 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 0. assume H3: Adj17 7 0.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_1 : Adj17 7 8 -> Adj17 8 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 1. assume H3: Adj17 7 1.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_2 : Adj17 7 8 -> Adj17 8 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 2. assume H3: Adj17 7 2.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_3 : Adj17 7 8 -> Adj17 8 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 3. assume H3: Adj17 7 3.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_4 : Adj17 7 8 -> Adj17 8 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 4. assume H3: Adj17 7 4.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_5 : Adj17 7 8 -> Adj17 8 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 5. assume H3: Adj17 7 5.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_6 : Adj17 7 8 -> Adj17 8 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 6. assume H3: Adj17 7 6.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_7 : Adj17 7 8 -> Adj17 8 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_8_8 : Adj17 7 8 -> Adj17 8 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 8. assume H3: Adj17 7 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_7_8_9 : Adj17 7 8 -> Adj17 8 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 9. assume H3: Adj17 7 9.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_10 : Adj17 7 8 -> Adj17 8 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 10. assume H3: Adj17 7 10.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_11 : Adj17 7 8 -> Adj17 8 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 11. assume H3: Adj17 7 11.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_12 : Adj17 7 8 -> Adj17 8 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 12. assume H3: Adj17 7 12.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_13 : Adj17 7 8 -> Adj17 8 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 13. assume H3: Adj17 7 13.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_14 : Adj17 7 8 -> Adj17 8 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 14. assume H3: Adj17 7 14.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_15 : Adj17 7 8 -> Adj17 8 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 15. assume H3: Adj17 7 15.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_8_16 : Adj17 7 8 -> Adj17 8 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 8. assume H2: Adj17 8 16. assume H3: Adj17 7 16.
exact Adj17_not_7_8 H1.
Qed.

Theorem tf_7_9_0 : Adj17 7 9 -> Adj17 9 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 0. assume H3: Adj17 7 0.
exact Adj17_not_7_0 H3.
Qed.

Theorem tf_7_9_1 : Adj17 7 9 -> Adj17 9 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 1. assume H3: Adj17 7 1.
exact Adj17_not_9_1 H2.
Qed.

Theorem tf_7_9_2 : Adj17 7 9 -> Adj17 9 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 2. assume H3: Adj17 7 2.
exact Adj17_not_9_2 H2.
Qed.

Theorem tf_7_9_3 : Adj17 7 9 -> Adj17 9 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 3. assume H3: Adj17 7 3.
exact Adj17_not_9_3 H2.
Qed.

Theorem tf_7_9_4 : Adj17 7 9 -> Adj17 9 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 4. assume H3: Adj17 7 4.
exact Adj17_not_9_4 H2.
Qed.

Theorem tf_7_9_5 : Adj17 7 9 -> Adj17 9 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 5. assume H3: Adj17 7 5.
exact Adj17_not_7_5 H3.
Qed.

Theorem tf_7_9_6 : Adj17 7 9 -> Adj17 9 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 6. assume H3: Adj17 7 6.
exact Adj17_not_9_6 H2.
Qed.

Theorem tf_7_9_7 : Adj17 7 9 -> Adj17 9 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_9_8 : Adj17 7 9 -> Adj17 9 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 8. assume H3: Adj17 7 8.
exact Adj17_not_7_8 H3.
Qed.

Theorem tf_7_9_9 : Adj17 7 9 -> Adj17 9 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 9. assume H3: Adj17 7 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_7_9_10 : Adj17 7 9 -> Adj17 9 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 10. assume H3: Adj17 7 10.
exact Adj17_not_9_10 H2.
Qed.

Theorem tf_7_9_11 : Adj17 7 9 -> Adj17 9 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 11. assume H3: Adj17 7 11.
exact Adj17_not_9_11 H2.
Qed.

Theorem tf_7_9_12 : Adj17 7 9 -> Adj17 9 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 12. assume H3: Adj17 7 12.
exact Adj17_not_7_12 H3.
Qed.

Theorem tf_7_9_13 : Adj17 7 9 -> Adj17 9 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 13. assume H3: Adj17 7 13.
exact Adj17_not_9_13 H2.
Qed.

Theorem tf_7_9_14 : Adj17 7 9 -> Adj17 9 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 14. assume H3: Adj17 7 14.
exact Adj17_not_9_14 H2.
Qed.

Theorem tf_7_9_15 : Adj17 7 9 -> Adj17 9 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 15. assume H3: Adj17 7 15.
exact Adj17_not_9_15 H2.
Qed.

Theorem tf_7_9_16 : Adj17 7 9 -> Adj17 9 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 9. assume H2: Adj17 9 16. assume H3: Adj17 7 16.
exact Adj17_not_9_16 H2.
Qed.

Theorem tf_7_10_0 : Adj17 7 10 -> Adj17 10 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 0. assume H3: Adj17 7 0.
exact Adj17_not_10_0 H2.
Qed.

Theorem tf_7_10_1 : Adj17 7 10 -> Adj17 10 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 1. assume H3: Adj17 7 1.
exact Adj17_not_10_1 H2.
Qed.

Theorem tf_7_10_2 : Adj17 7 10 -> Adj17 10 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 2. assume H3: Adj17 7 2.
exact Adj17_not_7_2 H3.
Qed.

Theorem tf_7_10_3 : Adj17 7 10 -> Adj17 10 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 3. assume H3: Adj17 7 3.
exact Adj17_not_10_3 H2.
Qed.

Theorem tf_7_10_4 : Adj17 7 10 -> Adj17 10 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 4. assume H3: Adj17 7 4.
exact Adj17_not_10_4 H2.
Qed.

Theorem tf_7_10_5 : Adj17 7 10 -> Adj17 10 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 5. assume H3: Adj17 7 5.
exact Adj17_not_7_5 H3.
Qed.

Theorem tf_7_10_6 : Adj17 7 10 -> Adj17 10 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 6. assume H3: Adj17 7 6.
exact Adj17_not_7_6 H3.
Qed.

Theorem tf_7_10_7 : Adj17 7 10 -> Adj17 10 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_10_8 : Adj17 7 10 -> Adj17 10 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 8. assume H3: Adj17 7 8.
exact Adj17_not_10_8 H2.
Qed.

Theorem tf_7_10_9 : Adj17 7 10 -> Adj17 10 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 9. assume H3: Adj17 7 9.
exact Adj17_not_10_9 H2.
Qed.

Theorem tf_7_10_10 : Adj17 7 10 -> Adj17 10 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 10. assume H3: Adj17 7 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_7_10_11 : Adj17 7 10 -> Adj17 10 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 11. assume H3: Adj17 7 11.
exact Adj17_not_10_11 H2.
Qed.

Theorem tf_7_10_12 : Adj17 7 10 -> Adj17 10 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 12. assume H3: Adj17 7 12.
exact Adj17_not_10_12 H2.
Qed.

Theorem tf_7_10_13 : Adj17 7 10 -> Adj17 10 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 13. assume H3: Adj17 7 13.
exact Adj17_not_10_13 H2.
Qed.

Theorem tf_7_10_14 : Adj17 7 10 -> Adj17 10 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 14. assume H3: Adj17 7 14.
exact Adj17_not_10_14 H2.
Qed.

Theorem tf_7_10_15 : Adj17 7 10 -> Adj17 10 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 15. assume H3: Adj17 7 15.
exact Adj17_not_10_15 H2.
Qed.

Theorem tf_7_10_16 : Adj17 7 10 -> Adj17 10 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 10. assume H2: Adj17 10 16. assume H3: Adj17 7 16.
exact Adj17_not_7_16 H3.
Qed.

Theorem tf_7_11_0 : Adj17 7 11 -> Adj17 11 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 0. assume H3: Adj17 7 0.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_1 : Adj17 7 11 -> Adj17 11 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 1. assume H3: Adj17 7 1.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_2 : Adj17 7 11 -> Adj17 11 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 2. assume H3: Adj17 7 2.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_3 : Adj17 7 11 -> Adj17 11 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 3. assume H3: Adj17 7 3.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_4 : Adj17 7 11 -> Adj17 11 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 4. assume H3: Adj17 7 4.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_5 : Adj17 7 11 -> Adj17 11 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 5. assume H3: Adj17 7 5.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_6 : Adj17 7 11 -> Adj17 11 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 6. assume H3: Adj17 7 6.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_7 : Adj17 7 11 -> Adj17 11 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_11_8 : Adj17 7 11 -> Adj17 11 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 8. assume H3: Adj17 7 8.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_9 : Adj17 7 11 -> Adj17 11 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 9. assume H3: Adj17 7 9.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_10 : Adj17 7 11 -> Adj17 11 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 10. assume H3: Adj17 7 10.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_11 : Adj17 7 11 -> Adj17 11 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 11. assume H3: Adj17 7 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_7_11_12 : Adj17 7 11 -> Adj17 11 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 12. assume H3: Adj17 7 12.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_13 : Adj17 7 11 -> Adj17 11 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 13. assume H3: Adj17 7 13.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_14 : Adj17 7 11 -> Adj17 11 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 14. assume H3: Adj17 7 14.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_15 : Adj17 7 11 -> Adj17 11 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 15. assume H3: Adj17 7 15.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_11_16 : Adj17 7 11 -> Adj17 11 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 11. assume H2: Adj17 11 16. assume H3: Adj17 7 16.
exact Adj17_not_7_11 H1.
Qed.

Theorem tf_7_12_0 : Adj17 7 12 -> Adj17 12 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 0. assume H3: Adj17 7 0.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_1 : Adj17 7 12 -> Adj17 12 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 1. assume H3: Adj17 7 1.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_2 : Adj17 7 12 -> Adj17 12 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 2. assume H3: Adj17 7 2.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_3 : Adj17 7 12 -> Adj17 12 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 3. assume H3: Adj17 7 3.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_4 : Adj17 7 12 -> Adj17 12 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 4. assume H3: Adj17 7 4.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_5 : Adj17 7 12 -> Adj17 12 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 5. assume H3: Adj17 7 5.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_6 : Adj17 7 12 -> Adj17 12 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 6. assume H3: Adj17 7 6.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_7 : Adj17 7 12 -> Adj17 12 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_12_8 : Adj17 7 12 -> Adj17 12 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 8. assume H3: Adj17 7 8.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_9 : Adj17 7 12 -> Adj17 12 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 9. assume H3: Adj17 7 9.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_10 : Adj17 7 12 -> Adj17 12 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 10. assume H3: Adj17 7 10.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_11 : Adj17 7 12 -> Adj17 12 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 11. assume H3: Adj17 7 11.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_12 : Adj17 7 12 -> Adj17 12 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 12. assume H3: Adj17 7 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_7_12_13 : Adj17 7 12 -> Adj17 12 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 13. assume H3: Adj17 7 13.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_14 : Adj17 7 12 -> Adj17 12 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 14. assume H3: Adj17 7 14.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_15 : Adj17 7 12 -> Adj17 12 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 15. assume H3: Adj17 7 15.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_12_16 : Adj17 7 12 -> Adj17 12 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 12. assume H2: Adj17 12 16. assume H3: Adj17 7 16.
exact Adj17_not_7_12 H1.
Qed.

Theorem tf_7_13_0 : Adj17 7 13 -> Adj17 13 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 0. assume H3: Adj17 7 0.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_1 : Adj17 7 13 -> Adj17 13 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 1. assume H3: Adj17 7 1.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_2 : Adj17 7 13 -> Adj17 13 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 2. assume H3: Adj17 7 2.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_3 : Adj17 7 13 -> Adj17 13 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 3. assume H3: Adj17 7 3.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_4 : Adj17 7 13 -> Adj17 13 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 4. assume H3: Adj17 7 4.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_5 : Adj17 7 13 -> Adj17 13 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 5. assume H3: Adj17 7 5.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_6 : Adj17 7 13 -> Adj17 13 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 6. assume H3: Adj17 7 6.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_7 : Adj17 7 13 -> Adj17 13 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_13_8 : Adj17 7 13 -> Adj17 13 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 8. assume H3: Adj17 7 8.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_9 : Adj17 7 13 -> Adj17 13 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 9. assume H3: Adj17 7 9.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_10 : Adj17 7 13 -> Adj17 13 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 10. assume H3: Adj17 7 10.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_11 : Adj17 7 13 -> Adj17 13 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 11. assume H3: Adj17 7 11.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_12 : Adj17 7 13 -> Adj17 13 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 12. assume H3: Adj17 7 12.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_13 : Adj17 7 13 -> Adj17 13 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 13. assume H3: Adj17 7 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_7_13_14 : Adj17 7 13 -> Adj17 13 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 14. assume H3: Adj17 7 14.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_15 : Adj17 7 13 -> Adj17 13 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 15. assume H3: Adj17 7 15.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_13_16 : Adj17 7 13 -> Adj17 13 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 13. assume H2: Adj17 13 16. assume H3: Adj17 7 16.
exact Adj17_not_7_13 H1.
Qed.

Theorem tf_7_14_0 : Adj17 7 14 -> Adj17 14 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 0. assume H3: Adj17 7 0.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_1 : Adj17 7 14 -> Adj17 14 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 1. assume H3: Adj17 7 1.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_2 : Adj17 7 14 -> Adj17 14 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 2. assume H3: Adj17 7 2.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_3 : Adj17 7 14 -> Adj17 14 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 3. assume H3: Adj17 7 3.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_4 : Adj17 7 14 -> Adj17 14 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 4. assume H3: Adj17 7 4.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_5 : Adj17 7 14 -> Adj17 14 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 5. assume H3: Adj17 7 5.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_6 : Adj17 7 14 -> Adj17 14 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 6. assume H3: Adj17 7 6.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_7 : Adj17 7 14 -> Adj17 14 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_14_8 : Adj17 7 14 -> Adj17 14 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 8. assume H3: Adj17 7 8.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_9 : Adj17 7 14 -> Adj17 14 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 9. assume H3: Adj17 7 9.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_10 : Adj17 7 14 -> Adj17 14 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 10. assume H3: Adj17 7 10.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_11 : Adj17 7 14 -> Adj17 14 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 11. assume H3: Adj17 7 11.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_12 : Adj17 7 14 -> Adj17 14 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 12. assume H3: Adj17 7 12.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_13 : Adj17 7 14 -> Adj17 14 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 13. assume H3: Adj17 7 13.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_14 : Adj17 7 14 -> Adj17 14 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 14. assume H3: Adj17 7 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_7_14_15 : Adj17 7 14 -> Adj17 14 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 15. assume H3: Adj17 7 15.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_14_16 : Adj17 7 14 -> Adj17 14 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 14. assume H2: Adj17 14 16. assume H3: Adj17 7 16.
exact Adj17_not_7_14 H1.
Qed.

Theorem tf_7_15_0 : Adj17 7 15 -> Adj17 15 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 0. assume H3: Adj17 7 0.
exact Adj17_not_7_0 H3.
Qed.

Theorem tf_7_15_1 : Adj17 7 15 -> Adj17 15 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 1. assume H3: Adj17 7 1.
exact Adj17_not_15_1 H2.
Qed.

Theorem tf_7_15_2 : Adj17 7 15 -> Adj17 15 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 2. assume H3: Adj17 7 2.
exact Adj17_not_7_2 H3.
Qed.

Theorem tf_7_15_3 : Adj17 7 15 -> Adj17 15 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 3. assume H3: Adj17 7 3.
exact Adj17_not_7_3 H3.
Qed.

Theorem tf_7_15_4 : Adj17 7 15 -> Adj17 15 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 4. assume H3: Adj17 7 4.
exact Adj17_not_15_4 H2.
Qed.

Theorem tf_7_15_5 : Adj17 7 15 -> Adj17 15 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 5. assume H3: Adj17 7 5.
exact Adj17_not_15_5 H2.
Qed.

Theorem tf_7_15_6 : Adj17 7 15 -> Adj17 15 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 6. assume H3: Adj17 7 6.
exact Adj17_not_15_6 H2.
Qed.

Theorem tf_7_15_7 : Adj17 7 15 -> Adj17 15 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_15_8 : Adj17 7 15 -> Adj17 15 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 8. assume H3: Adj17 7 8.
exact Adj17_not_15_8 H2.
Qed.

Theorem tf_7_15_9 : Adj17 7 15 -> Adj17 15 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 9. assume H3: Adj17 7 9.
exact Adj17_not_15_9 H2.
Qed.

Theorem tf_7_15_10 : Adj17 7 15 -> Adj17 15 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 10. assume H3: Adj17 7 10.
exact Adj17_not_15_10 H2.
Qed.

Theorem tf_7_15_11 : Adj17 7 15 -> Adj17 15 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 11. assume H3: Adj17 7 11.
exact Adj17_not_7_11 H3.
Qed.

Theorem tf_7_15_12 : Adj17 7 15 -> Adj17 15 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 12. assume H3: Adj17 7 12.
exact Adj17_not_15_12 H2.
Qed.

Theorem tf_7_15_13 : Adj17 7 15 -> Adj17 15 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 13. assume H3: Adj17 7 13.
exact Adj17_not_15_13 H2.
Qed.

Theorem tf_7_15_14 : Adj17 7 15 -> Adj17 15 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 14. assume H3: Adj17 7 14.
exact Adj17_not_15_14 H2.
Qed.

Theorem tf_7_15_15 : Adj17 7 15 -> Adj17 15 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 15. assume H3: Adj17 7 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_7_15_16 : Adj17 7 15 -> Adj17 15 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 15. assume H2: Adj17 15 16. assume H3: Adj17 7 16.
exact Adj17_not_15_16 H2.
Qed.

Theorem tf_7_16_0 : Adj17 7 16 -> Adj17 16 0 -> Adj17 7 0 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 0. assume H3: Adj17 7 0.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_1 : Adj17 7 16 -> Adj17 16 1 -> Adj17 7 1 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 1. assume H3: Adj17 7 1.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_2 : Adj17 7 16 -> Adj17 16 2 -> Adj17 7 2 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 2. assume H3: Adj17 7 2.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_3 : Adj17 7 16 -> Adj17 16 3 -> Adj17 7 3 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 3. assume H3: Adj17 7 3.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_4 : Adj17 7 16 -> Adj17 16 4 -> Adj17 7 4 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 4. assume H3: Adj17 7 4.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_5 : Adj17 7 16 -> Adj17 16 5 -> Adj17 7 5 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 5. assume H3: Adj17 7 5.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_6 : Adj17 7 16 -> Adj17 16 6 -> Adj17 7 6 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 6. assume H3: Adj17 7 6.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_7 : Adj17 7 16 -> Adj17 16 7 -> Adj17 7 7 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 7. assume H3: Adj17 7 7.
exact Adj17_not_7_7 H3.
Qed.

Theorem tf_7_16_8 : Adj17 7 16 -> Adj17 16 8 -> Adj17 7 8 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 8. assume H3: Adj17 7 8.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_9 : Adj17 7 16 -> Adj17 16 9 -> Adj17 7 9 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 9. assume H3: Adj17 7 9.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_10 : Adj17 7 16 -> Adj17 16 10 -> Adj17 7 10 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 10. assume H3: Adj17 7 10.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_11 : Adj17 7 16 -> Adj17 16 11 -> Adj17 7 11 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 11. assume H3: Adj17 7 11.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_12 : Adj17 7 16 -> Adj17 16 12 -> Adj17 7 12 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 12. assume H3: Adj17 7 12.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_13 : Adj17 7 16 -> Adj17 16 13 -> Adj17 7 13 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 13. assume H3: Adj17 7 13.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_14 : Adj17 7 16 -> Adj17 16 14 -> Adj17 7 14 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 14. assume H3: Adj17 7 14.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_15 : Adj17 7 16 -> Adj17 16 15 -> Adj17 7 15 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 15. assume H3: Adj17 7 15.
exact Adj17_not_7_16 H1.
Qed.

Theorem tf_7_16_16 : Adj17 7 16 -> Adj17 16 16 -> Adj17 7 16 -> False.
assume H1: Adj17 7 16. assume H2: Adj17 16 16. assume H3: Adj17 7 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_8_0_0 : Adj17 8 0 -> Adj17 0 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 0. assume H3: Adj17 8 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_8_0_1 : Adj17 8 0 -> Adj17 0 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 1. assume H3: Adj17 8 1.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_2 : Adj17 8 0 -> Adj17 0 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 2. assume H3: Adj17 8 2.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_3 : Adj17 8 0 -> Adj17 0 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 3. assume H3: Adj17 8 3.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_4 : Adj17 8 0 -> Adj17 0 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 4. assume H3: Adj17 8 4.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_5 : Adj17 8 0 -> Adj17 0 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 5. assume H3: Adj17 8 5.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_6 : Adj17 8 0 -> Adj17 0 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 6. assume H3: Adj17 8 6.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_7 : Adj17 8 0 -> Adj17 0 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 7. assume H3: Adj17 8 7.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_8 : Adj17 8 0 -> Adj17 0 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_0_9 : Adj17 8 0 -> Adj17 0 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 9. assume H3: Adj17 8 9.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_10 : Adj17 8 0 -> Adj17 0 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 10. assume H3: Adj17 8 10.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_11 : Adj17 8 0 -> Adj17 0 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 11. assume H3: Adj17 8 11.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_12 : Adj17 8 0 -> Adj17 0 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 12. assume H3: Adj17 8 12.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_13 : Adj17 8 0 -> Adj17 0 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 13. assume H3: Adj17 8 13.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_14 : Adj17 8 0 -> Adj17 0 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 14. assume H3: Adj17 8 14.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_15 : Adj17 8 0 -> Adj17 0 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 15. assume H3: Adj17 8 15.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_0_16 : Adj17 8 0 -> Adj17 0 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 0. assume H2: Adj17 0 16. assume H3: Adj17 8 16.
exact Adj17_not_8_0 H1.
Qed.

Theorem tf_8_1_0 : Adj17 8 1 -> Adj17 1 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 0. assume H3: Adj17 8 0.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_1 : Adj17 8 1 -> Adj17 1 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 1. assume H3: Adj17 8 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_8_1_2 : Adj17 8 1 -> Adj17 1 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 2. assume H3: Adj17 8 2.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_3 : Adj17 8 1 -> Adj17 1 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 3. assume H3: Adj17 8 3.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_4 : Adj17 8 1 -> Adj17 1 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 4. assume H3: Adj17 8 4.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_5 : Adj17 8 1 -> Adj17 1 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 5. assume H3: Adj17 8 5.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_6 : Adj17 8 1 -> Adj17 1 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 6. assume H3: Adj17 8 6.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_7 : Adj17 8 1 -> Adj17 1 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 7. assume H3: Adj17 8 7.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_8 : Adj17 8 1 -> Adj17 1 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_1_9 : Adj17 8 1 -> Adj17 1 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 9. assume H3: Adj17 8 9.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_10 : Adj17 8 1 -> Adj17 1 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 10. assume H3: Adj17 8 10.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_11 : Adj17 8 1 -> Adj17 1 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 11. assume H3: Adj17 8 11.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_12 : Adj17 8 1 -> Adj17 1 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 12. assume H3: Adj17 8 12.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_13 : Adj17 8 1 -> Adj17 1 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 13. assume H3: Adj17 8 13.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_14 : Adj17 8 1 -> Adj17 1 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 14. assume H3: Adj17 8 14.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_15 : Adj17 8 1 -> Adj17 1 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 15. assume H3: Adj17 8 15.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_1_16 : Adj17 8 1 -> Adj17 1 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 1. assume H2: Adj17 1 16. assume H3: Adj17 8 16.
exact Adj17_not_8_1 H1.
Qed.

Theorem tf_8_2_0 : Adj17 8 2 -> Adj17 2 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 0. assume H3: Adj17 8 0.
exact Adj17_not_2_0 H2.
Qed.

Theorem tf_8_2_1 : Adj17 8 2 -> Adj17 2 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 1. assume H3: Adj17 8 1.
exact Adj17_not_2_1 H2.
Qed.

Theorem tf_8_2_2 : Adj17 8 2 -> Adj17 2 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 2. assume H3: Adj17 8 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_8_2_3 : Adj17 8 2 -> Adj17 2 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 3. assume H3: Adj17 8 3.
exact Adj17_not_2_3 H2.
Qed.

Theorem tf_8_2_4 : Adj17 8 2 -> Adj17 2 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 4. assume H3: Adj17 8 4.
exact Adj17_not_2_4 H2.
Qed.

Theorem tf_8_2_5 : Adj17 8 2 -> Adj17 2 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 5. assume H3: Adj17 8 5.
exact Adj17_not_2_5 H2.
Qed.

Theorem tf_8_2_6 : Adj17 8 2 -> Adj17 2 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 6. assume H3: Adj17 8 6.
exact Adj17_not_2_6 H2.
Qed.

Theorem tf_8_2_7 : Adj17 8 2 -> Adj17 2 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 7. assume H3: Adj17 8 7.
exact Adj17_not_2_7 H2.
Qed.

Theorem tf_8_2_8 : Adj17 8 2 -> Adj17 2 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_2_9 : Adj17 8 2 -> Adj17 2 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 9. assume H3: Adj17 8 9.
exact Adj17_not_2_9 H2.
Qed.

Theorem tf_8_2_10 : Adj17 8 2 -> Adj17 2 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 10. assume H3: Adj17 8 10.
exact Adj17_not_8_10 H3.
Qed.

Theorem tf_8_2_11 : Adj17 8 2 -> Adj17 2 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 11. assume H3: Adj17 8 11.
exact Adj17_not_2_11 H2.
Qed.

Theorem tf_8_2_12 : Adj17 8 2 -> Adj17 2 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 12. assume H3: Adj17 8 12.
exact Adj17_not_8_12 H3.
Qed.

Theorem tf_8_2_13 : Adj17 8 2 -> Adj17 2 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 13. assume H3: Adj17 8 13.
exact Adj17_not_2_13 H2.
Qed.

Theorem tf_8_2_14 : Adj17 8 2 -> Adj17 2 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 14. assume H3: Adj17 8 14.
exact Adj17_not_2_14 H2.
Qed.

Theorem tf_8_2_15 : Adj17 8 2 -> Adj17 2 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 15. assume H3: Adj17 8 15.
exact Adj17_not_8_15 H3.
Qed.

Theorem tf_8_2_16 : Adj17 8 2 -> Adj17 2 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 2. assume H2: Adj17 2 16. assume H3: Adj17 8 16.
exact Adj17_not_2_16 H2.
Qed.

Theorem tf_8_3_0 : Adj17 8 3 -> Adj17 3 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 0. assume H3: Adj17 8 0.
exact Adj17_not_3_0 H2.
Qed.

Theorem tf_8_3_1 : Adj17 8 3 -> Adj17 3 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 1. assume H3: Adj17 8 1.
exact Adj17_not_3_1 H2.
Qed.

Theorem tf_8_3_2 : Adj17 8 3 -> Adj17 3 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 2. assume H3: Adj17 8 2.
exact Adj17_not_3_2 H2.
Qed.

Theorem tf_8_3_3 : Adj17 8 3 -> Adj17 3 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 3. assume H3: Adj17 8 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_8_3_4 : Adj17 8 3 -> Adj17 3 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 4. assume H3: Adj17 8 4.
exact Adj17_not_3_4 H2.
Qed.

Theorem tf_8_3_5 : Adj17 8 3 -> Adj17 3 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 5. assume H3: Adj17 8 5.
exact Adj17_not_3_5 H2.
Qed.

Theorem tf_8_3_6 : Adj17 8 3 -> Adj17 3 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 6. assume H3: Adj17 8 6.
exact Adj17_not_8_6 H3.
Qed.

Theorem tf_8_3_7 : Adj17 8 3 -> Adj17 3 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 7. assume H3: Adj17 8 7.
exact Adj17_not_3_7 H2.
Qed.

Theorem tf_8_3_8 : Adj17 8 3 -> Adj17 3 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_3_9 : Adj17 8 3 -> Adj17 3 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 9. assume H3: Adj17 8 9.
exact Adj17_not_3_9 H2.
Qed.

Theorem tf_8_3_10 : Adj17 8 3 -> Adj17 3 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 10. assume H3: Adj17 8 10.
exact Adj17_not_3_10 H2.
Qed.

Theorem tf_8_3_11 : Adj17 8 3 -> Adj17 3 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 11. assume H3: Adj17 8 11.
exact Adj17_not_3_11 H2.
Qed.

Theorem tf_8_3_12 : Adj17 8 3 -> Adj17 3 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 12. assume H3: Adj17 8 12.
exact Adj17_not_3_12 H2.
Qed.

Theorem tf_8_3_13 : Adj17 8 3 -> Adj17 3 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 13. assume H3: Adj17 8 13.
exact Adj17_not_8_13 H3.
Qed.

Theorem tf_8_3_14 : Adj17 8 3 -> Adj17 3 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 14. assume H3: Adj17 8 14.
exact Adj17_not_3_14 H2.
Qed.

Theorem tf_8_3_15 : Adj17 8 3 -> Adj17 3 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 15. assume H3: Adj17 8 15.
exact Adj17_not_8_15 H3.
Qed.

Theorem tf_8_3_16 : Adj17 8 3 -> Adj17 3 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 3. assume H2: Adj17 3 16. assume H3: Adj17 8 16.
exact Adj17_not_8_16 H3.
Qed.

Theorem tf_8_4_0 : Adj17 8 4 -> Adj17 4 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 0. assume H3: Adj17 8 0.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_1 : Adj17 8 4 -> Adj17 4 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 1. assume H3: Adj17 8 1.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_2 : Adj17 8 4 -> Adj17 4 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 2. assume H3: Adj17 8 2.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_3 : Adj17 8 4 -> Adj17 4 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 3. assume H3: Adj17 8 3.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_4 : Adj17 8 4 -> Adj17 4 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 4. assume H3: Adj17 8 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_8_4_5 : Adj17 8 4 -> Adj17 4 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 5. assume H3: Adj17 8 5.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_6 : Adj17 8 4 -> Adj17 4 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 6. assume H3: Adj17 8 6.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_7 : Adj17 8 4 -> Adj17 4 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 7. assume H3: Adj17 8 7.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_8 : Adj17 8 4 -> Adj17 4 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_4_9 : Adj17 8 4 -> Adj17 4 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 9. assume H3: Adj17 8 9.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_10 : Adj17 8 4 -> Adj17 4 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 10. assume H3: Adj17 8 10.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_11 : Adj17 8 4 -> Adj17 4 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 11. assume H3: Adj17 8 11.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_12 : Adj17 8 4 -> Adj17 4 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 12. assume H3: Adj17 8 12.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_13 : Adj17 8 4 -> Adj17 4 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 13. assume H3: Adj17 8 13.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_14 : Adj17 8 4 -> Adj17 4 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 14. assume H3: Adj17 8 14.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_15 : Adj17 8 4 -> Adj17 4 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 15. assume H3: Adj17 8 15.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_4_16 : Adj17 8 4 -> Adj17 4 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 4. assume H2: Adj17 4 16. assume H3: Adj17 8 16.
exact Adj17_not_8_4 H1.
Qed.

Theorem tf_8_5_0 : Adj17 8 5 -> Adj17 5 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 0. assume H3: Adj17 8 0.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_1 : Adj17 8 5 -> Adj17 5 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 1. assume H3: Adj17 8 1.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_2 : Adj17 8 5 -> Adj17 5 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 2. assume H3: Adj17 8 2.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_3 : Adj17 8 5 -> Adj17 5 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 3. assume H3: Adj17 8 3.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_4 : Adj17 8 5 -> Adj17 5 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 4. assume H3: Adj17 8 4.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_5 : Adj17 8 5 -> Adj17 5 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 5. assume H3: Adj17 8 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_8_5_6 : Adj17 8 5 -> Adj17 5 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 6. assume H3: Adj17 8 6.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_7 : Adj17 8 5 -> Adj17 5 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 7. assume H3: Adj17 8 7.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_8 : Adj17 8 5 -> Adj17 5 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_5_9 : Adj17 8 5 -> Adj17 5 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 9. assume H3: Adj17 8 9.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_10 : Adj17 8 5 -> Adj17 5 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 10. assume H3: Adj17 8 10.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_11 : Adj17 8 5 -> Adj17 5 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 11. assume H3: Adj17 8 11.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_12 : Adj17 8 5 -> Adj17 5 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 12. assume H3: Adj17 8 12.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_13 : Adj17 8 5 -> Adj17 5 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 13. assume H3: Adj17 8 13.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_14 : Adj17 8 5 -> Adj17 5 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 14. assume H3: Adj17 8 14.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_15 : Adj17 8 5 -> Adj17 5 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 15. assume H3: Adj17 8 15.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_5_16 : Adj17 8 5 -> Adj17 5 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 5. assume H2: Adj17 5 16. assume H3: Adj17 8 16.
exact Adj17_not_8_5 H1.
Qed.

Theorem tf_8_6_0 : Adj17 8 6 -> Adj17 6 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 0. assume H3: Adj17 8 0.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_1 : Adj17 8 6 -> Adj17 6 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 1. assume H3: Adj17 8 1.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_2 : Adj17 8 6 -> Adj17 6 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 2. assume H3: Adj17 8 2.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_3 : Adj17 8 6 -> Adj17 6 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 3. assume H3: Adj17 8 3.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_4 : Adj17 8 6 -> Adj17 6 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 4. assume H3: Adj17 8 4.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_5 : Adj17 8 6 -> Adj17 6 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 5. assume H3: Adj17 8 5.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_6 : Adj17 8 6 -> Adj17 6 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 6. assume H3: Adj17 8 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_8_6_7 : Adj17 8 6 -> Adj17 6 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 7. assume H3: Adj17 8 7.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_8 : Adj17 8 6 -> Adj17 6 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_6_9 : Adj17 8 6 -> Adj17 6 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 9. assume H3: Adj17 8 9.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_10 : Adj17 8 6 -> Adj17 6 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 10. assume H3: Adj17 8 10.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_11 : Adj17 8 6 -> Adj17 6 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 11. assume H3: Adj17 8 11.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_12 : Adj17 8 6 -> Adj17 6 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 12. assume H3: Adj17 8 12.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_13 : Adj17 8 6 -> Adj17 6 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 13. assume H3: Adj17 8 13.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_14 : Adj17 8 6 -> Adj17 6 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 14. assume H3: Adj17 8 14.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_15 : Adj17 8 6 -> Adj17 6 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 15. assume H3: Adj17 8 15.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_6_16 : Adj17 8 6 -> Adj17 6 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 6. assume H2: Adj17 6 16. assume H3: Adj17 8 16.
exact Adj17_not_8_6 H1.
Qed.

Theorem tf_8_7_0 : Adj17 8 7 -> Adj17 7 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 0. assume H3: Adj17 8 0.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_1 : Adj17 8 7 -> Adj17 7 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 1. assume H3: Adj17 8 1.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_2 : Adj17 8 7 -> Adj17 7 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 2. assume H3: Adj17 8 2.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_3 : Adj17 8 7 -> Adj17 7 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 3. assume H3: Adj17 8 3.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_4 : Adj17 8 7 -> Adj17 7 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 4. assume H3: Adj17 8 4.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_5 : Adj17 8 7 -> Adj17 7 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 5. assume H3: Adj17 8 5.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_6 : Adj17 8 7 -> Adj17 7 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 6. assume H3: Adj17 8 6.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_7 : Adj17 8 7 -> Adj17 7 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 7. assume H3: Adj17 8 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_8_7_8 : Adj17 8 7 -> Adj17 7 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_7_9 : Adj17 8 7 -> Adj17 7 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 9. assume H3: Adj17 8 9.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_10 : Adj17 8 7 -> Adj17 7 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 10. assume H3: Adj17 8 10.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_11 : Adj17 8 7 -> Adj17 7 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 11. assume H3: Adj17 8 11.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_12 : Adj17 8 7 -> Adj17 7 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 12. assume H3: Adj17 8 12.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_13 : Adj17 8 7 -> Adj17 7 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 13. assume H3: Adj17 8 13.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_14 : Adj17 8 7 -> Adj17 7 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 14. assume H3: Adj17 8 14.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_15 : Adj17 8 7 -> Adj17 7 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 15. assume H3: Adj17 8 15.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_7_16 : Adj17 8 7 -> Adj17 7 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 7. assume H2: Adj17 7 16. assume H3: Adj17 8 16.
exact Adj17_not_8_7 H1.
Qed.

Theorem tf_8_8_0 : Adj17 8 8 -> Adj17 8 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 0. assume H3: Adj17 8 0.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_1 : Adj17 8 8 -> Adj17 8 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 1. assume H3: Adj17 8 1.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_2 : Adj17 8 8 -> Adj17 8 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 2. assume H3: Adj17 8 2.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_3 : Adj17 8 8 -> Adj17 8 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 3. assume H3: Adj17 8 3.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_4 : Adj17 8 8 -> Adj17 8 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 4. assume H3: Adj17 8 4.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_5 : Adj17 8 8 -> Adj17 8 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 5. assume H3: Adj17 8 5.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_6 : Adj17 8 8 -> Adj17 8 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 6. assume H3: Adj17 8 6.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_7 : Adj17 8 8 -> Adj17 8 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 7. assume H3: Adj17 8 7.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_8 : Adj17 8 8 -> Adj17 8 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_9 : Adj17 8 8 -> Adj17 8 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 9. assume H3: Adj17 8 9.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_10 : Adj17 8 8 -> Adj17 8 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 10. assume H3: Adj17 8 10.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_11 : Adj17 8 8 -> Adj17 8 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 11. assume H3: Adj17 8 11.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_12 : Adj17 8 8 -> Adj17 8 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 12. assume H3: Adj17 8 12.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_13 : Adj17 8 8 -> Adj17 8 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 13. assume H3: Adj17 8 13.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_14 : Adj17 8 8 -> Adj17 8 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 14. assume H3: Adj17 8 14.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_15 : Adj17 8 8 -> Adj17 8 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 15. assume H3: Adj17 8 15.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_8_16 : Adj17 8 8 -> Adj17 8 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 8. assume H2: Adj17 8 16. assume H3: Adj17 8 16.
exact Adj17_not_8_8 H1.
Qed.

Theorem tf_8_9_0 : Adj17 8 9 -> Adj17 9 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 0. assume H3: Adj17 8 0.
exact Adj17_not_8_0 H3.
Qed.

Theorem tf_8_9_1 : Adj17 8 9 -> Adj17 9 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 1. assume H3: Adj17 8 1.
exact Adj17_not_9_1 H2.
Qed.

Theorem tf_8_9_2 : Adj17 8 9 -> Adj17 9 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 2. assume H3: Adj17 8 2.
exact Adj17_not_9_2 H2.
Qed.

Theorem tf_8_9_3 : Adj17 8 9 -> Adj17 9 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 3. assume H3: Adj17 8 3.
exact Adj17_not_9_3 H2.
Qed.

Theorem tf_8_9_4 : Adj17 8 9 -> Adj17 9 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 4. assume H3: Adj17 8 4.
exact Adj17_not_9_4 H2.
Qed.

Theorem tf_8_9_5 : Adj17 8 9 -> Adj17 9 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 5. assume H3: Adj17 8 5.
exact Adj17_not_8_5 H3.
Qed.

Theorem tf_8_9_6 : Adj17 8 9 -> Adj17 9 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 6. assume H3: Adj17 8 6.
exact Adj17_not_9_6 H2.
Qed.

Theorem tf_8_9_7 : Adj17 8 9 -> Adj17 9 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 7. assume H3: Adj17 8 7.
exact Adj17_not_8_7 H3.
Qed.

Theorem tf_8_9_8 : Adj17 8 9 -> Adj17 9 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_9_9 : Adj17 8 9 -> Adj17 9 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 9. assume H3: Adj17 8 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_8_9_10 : Adj17 8 9 -> Adj17 9 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 10. assume H3: Adj17 8 10.
exact Adj17_not_9_10 H2.
Qed.

Theorem tf_8_9_11 : Adj17 8 9 -> Adj17 9 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 11. assume H3: Adj17 8 11.
exact Adj17_not_9_11 H2.
Qed.

Theorem tf_8_9_12 : Adj17 8 9 -> Adj17 9 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 12. assume H3: Adj17 8 12.
exact Adj17_not_8_12 H3.
Qed.

Theorem tf_8_9_13 : Adj17 8 9 -> Adj17 9 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 13. assume H3: Adj17 8 13.
exact Adj17_not_9_13 H2.
Qed.

Theorem tf_8_9_14 : Adj17 8 9 -> Adj17 9 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 14. assume H3: Adj17 8 14.
exact Adj17_not_9_14 H2.
Qed.

Theorem tf_8_9_15 : Adj17 8 9 -> Adj17 9 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 15. assume H3: Adj17 8 15.
exact Adj17_not_9_15 H2.
Qed.

Theorem tf_8_9_16 : Adj17 8 9 -> Adj17 9 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 9. assume H2: Adj17 9 16. assume H3: Adj17 8 16.
exact Adj17_not_9_16 H2.
Qed.

Theorem tf_8_10_0 : Adj17 8 10 -> Adj17 10 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 0. assume H3: Adj17 8 0.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_1 : Adj17 8 10 -> Adj17 10 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 1. assume H3: Adj17 8 1.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_2 : Adj17 8 10 -> Adj17 10 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 2. assume H3: Adj17 8 2.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_3 : Adj17 8 10 -> Adj17 10 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 3. assume H3: Adj17 8 3.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_4 : Adj17 8 10 -> Adj17 10 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 4. assume H3: Adj17 8 4.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_5 : Adj17 8 10 -> Adj17 10 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 5. assume H3: Adj17 8 5.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_6 : Adj17 8 10 -> Adj17 10 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 6. assume H3: Adj17 8 6.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_7 : Adj17 8 10 -> Adj17 10 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 7. assume H3: Adj17 8 7.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_8 : Adj17 8 10 -> Adj17 10 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_10_9 : Adj17 8 10 -> Adj17 10 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 9. assume H3: Adj17 8 9.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_10 : Adj17 8 10 -> Adj17 10 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 10. assume H3: Adj17 8 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_8_10_11 : Adj17 8 10 -> Adj17 10 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 11. assume H3: Adj17 8 11.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_12 : Adj17 8 10 -> Adj17 10 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 12. assume H3: Adj17 8 12.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_13 : Adj17 8 10 -> Adj17 10 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 13. assume H3: Adj17 8 13.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_14 : Adj17 8 10 -> Adj17 10 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 14. assume H3: Adj17 8 14.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_15 : Adj17 8 10 -> Adj17 10 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 15. assume H3: Adj17 8 15.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_10_16 : Adj17 8 10 -> Adj17 10 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 10. assume H2: Adj17 10 16. assume H3: Adj17 8 16.
exact Adj17_not_8_10 H1.
Qed.

Theorem tf_8_11_0 : Adj17 8 11 -> Adj17 11 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 0. assume H3: Adj17 8 0.
exact Adj17_not_11_0 H2.
Qed.

Theorem tf_8_11_1 : Adj17 8 11 -> Adj17 11 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 1. assume H3: Adj17 8 1.
exact Adj17_not_8_1 H3.
Qed.

Theorem tf_8_11_2 : Adj17 8 11 -> Adj17 11 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 2. assume H3: Adj17 8 2.
exact Adj17_not_11_2 H2.
Qed.

Theorem tf_8_11_3 : Adj17 8 11 -> Adj17 11 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 3. assume H3: Adj17 8 3.
exact Adj17_not_11_3 H2.
Qed.

Theorem tf_8_11_4 : Adj17 8 11 -> Adj17 11 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 4. assume H3: Adj17 8 4.
exact Adj17_not_11_4 H2.
Qed.

Theorem tf_8_11_5 : Adj17 8 11 -> Adj17 11 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 5. assume H3: Adj17 8 5.
exact Adj17_not_8_5 H3.
Qed.

Theorem tf_8_11_6 : Adj17 8 11 -> Adj17 11 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 6. assume H3: Adj17 8 6.
exact Adj17_not_8_6 H3.
Qed.

Theorem tf_8_11_7 : Adj17 8 11 -> Adj17 11 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 7. assume H3: Adj17 8 7.
exact Adj17_not_11_7 H2.
Qed.

Theorem tf_8_11_8 : Adj17 8 11 -> Adj17 11 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_11_9 : Adj17 8 11 -> Adj17 11 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 9. assume H3: Adj17 8 9.
exact Adj17_not_11_9 H2.
Qed.

Theorem tf_8_11_10 : Adj17 8 11 -> Adj17 11 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 10. assume H3: Adj17 8 10.
exact Adj17_not_11_10 H2.
Qed.

Theorem tf_8_11_11 : Adj17 8 11 -> Adj17 11 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 11. assume H3: Adj17 8 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_8_11_12 : Adj17 8 11 -> Adj17 11 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 12. assume H3: Adj17 8 12.
exact Adj17_not_11_12 H2.
Qed.

Theorem tf_8_11_13 : Adj17 8 11 -> Adj17 11 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 13. assume H3: Adj17 8 13.
exact Adj17_not_11_13 H2.
Qed.

Theorem tf_8_11_14 : Adj17 8 11 -> Adj17 11 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 14. assume H3: Adj17 8 14.
exact Adj17_not_11_14 H2.
Qed.

Theorem tf_8_11_15 : Adj17 8 11 -> Adj17 11 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 15. assume H3: Adj17 8 15.
exact Adj17_not_8_15 H3.
Qed.

Theorem tf_8_11_16 : Adj17 8 11 -> Adj17 11 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 11. assume H2: Adj17 11 16. assume H3: Adj17 8 16.
exact Adj17_not_11_16 H2.
Qed.

Theorem tf_8_12_0 : Adj17 8 12 -> Adj17 12 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 0. assume H3: Adj17 8 0.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_1 : Adj17 8 12 -> Adj17 12 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 1. assume H3: Adj17 8 1.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_2 : Adj17 8 12 -> Adj17 12 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 2. assume H3: Adj17 8 2.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_3 : Adj17 8 12 -> Adj17 12 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 3. assume H3: Adj17 8 3.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_4 : Adj17 8 12 -> Adj17 12 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 4. assume H3: Adj17 8 4.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_5 : Adj17 8 12 -> Adj17 12 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 5. assume H3: Adj17 8 5.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_6 : Adj17 8 12 -> Adj17 12 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 6. assume H3: Adj17 8 6.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_7 : Adj17 8 12 -> Adj17 12 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 7. assume H3: Adj17 8 7.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_8 : Adj17 8 12 -> Adj17 12 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_12_9 : Adj17 8 12 -> Adj17 12 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 9. assume H3: Adj17 8 9.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_10 : Adj17 8 12 -> Adj17 12 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 10. assume H3: Adj17 8 10.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_11 : Adj17 8 12 -> Adj17 12 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 11. assume H3: Adj17 8 11.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_12 : Adj17 8 12 -> Adj17 12 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 12. assume H3: Adj17 8 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_8_12_13 : Adj17 8 12 -> Adj17 12 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 13. assume H3: Adj17 8 13.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_14 : Adj17 8 12 -> Adj17 12 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 14. assume H3: Adj17 8 14.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_15 : Adj17 8 12 -> Adj17 12 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 15. assume H3: Adj17 8 15.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_12_16 : Adj17 8 12 -> Adj17 12 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 12. assume H2: Adj17 12 16. assume H3: Adj17 8 16.
exact Adj17_not_8_12 H1.
Qed.

Theorem tf_8_13_0 : Adj17 8 13 -> Adj17 13 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 0. assume H3: Adj17 8 0.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_1 : Adj17 8 13 -> Adj17 13 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 1. assume H3: Adj17 8 1.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_2 : Adj17 8 13 -> Adj17 13 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 2. assume H3: Adj17 8 2.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_3 : Adj17 8 13 -> Adj17 13 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 3. assume H3: Adj17 8 3.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_4 : Adj17 8 13 -> Adj17 13 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 4. assume H3: Adj17 8 4.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_5 : Adj17 8 13 -> Adj17 13 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 5. assume H3: Adj17 8 5.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_6 : Adj17 8 13 -> Adj17 13 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 6. assume H3: Adj17 8 6.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_7 : Adj17 8 13 -> Adj17 13 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 7. assume H3: Adj17 8 7.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_8 : Adj17 8 13 -> Adj17 13 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_13_9 : Adj17 8 13 -> Adj17 13 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 9. assume H3: Adj17 8 9.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_10 : Adj17 8 13 -> Adj17 13 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 10. assume H3: Adj17 8 10.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_11 : Adj17 8 13 -> Adj17 13 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 11. assume H3: Adj17 8 11.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_12 : Adj17 8 13 -> Adj17 13 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 12. assume H3: Adj17 8 12.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_13 : Adj17 8 13 -> Adj17 13 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 13. assume H3: Adj17 8 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_8_13_14 : Adj17 8 13 -> Adj17 13 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 14. assume H3: Adj17 8 14.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_15 : Adj17 8 13 -> Adj17 13 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 15. assume H3: Adj17 8 15.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_13_16 : Adj17 8 13 -> Adj17 13 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 13. assume H2: Adj17 13 16. assume H3: Adj17 8 16.
exact Adj17_not_8_13 H1.
Qed.

Theorem tf_8_14_0 : Adj17 8 14 -> Adj17 14 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 0. assume H3: Adj17 8 0.
exact Adj17_not_8_0 H3.
Qed.

Theorem tf_8_14_1 : Adj17 8 14 -> Adj17 14 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 1. assume H3: Adj17 8 1.
exact Adj17_not_14_1 H2.
Qed.

Theorem tf_8_14_2 : Adj17 8 14 -> Adj17 14 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 2. assume H3: Adj17 8 2.
exact Adj17_not_14_2 H2.
Qed.

Theorem tf_8_14_3 : Adj17 8 14 -> Adj17 14 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 3. assume H3: Adj17 8 3.
exact Adj17_not_14_3 H2.
Qed.

Theorem tf_8_14_4 : Adj17 8 14 -> Adj17 14 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 4. assume H3: Adj17 8 4.
exact Adj17_not_8_4 H3.
Qed.

Theorem tf_8_14_5 : Adj17 8 14 -> Adj17 14 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 5. assume H3: Adj17 8 5.
exact Adj17_not_14_5 H2.
Qed.

Theorem tf_8_14_6 : Adj17 8 14 -> Adj17 14 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 6. assume H3: Adj17 8 6.
exact Adj17_not_8_6 H3.
Qed.

Theorem tf_8_14_7 : Adj17 8 14 -> Adj17 14 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 7. assume H3: Adj17 8 7.
exact Adj17_not_14_7 H2.
Qed.

Theorem tf_8_14_8 : Adj17 8 14 -> Adj17 14 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_14_9 : Adj17 8 14 -> Adj17 14 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 9. assume H3: Adj17 8 9.
exact Adj17_not_14_9 H2.
Qed.

Theorem tf_8_14_10 : Adj17 8 14 -> Adj17 14 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 10. assume H3: Adj17 8 10.
exact Adj17_not_14_10 H2.
Qed.

Theorem tf_8_14_11 : Adj17 8 14 -> Adj17 14 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 11. assume H3: Adj17 8 11.
exact Adj17_not_14_11 H2.
Qed.

Theorem tf_8_14_12 : Adj17 8 14 -> Adj17 14 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 12. assume H3: Adj17 8 12.
exact Adj17_not_14_12 H2.
Qed.

Theorem tf_8_14_13 : Adj17 8 14 -> Adj17 14 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 13. assume H3: Adj17 8 13.
exact Adj17_not_8_13 H3.
Qed.

Theorem tf_8_14_14 : Adj17 8 14 -> Adj17 14 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 14. assume H3: Adj17 8 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_8_14_15 : Adj17 8 14 -> Adj17 14 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 15. assume H3: Adj17 8 15.
exact Adj17_not_14_15 H2.
Qed.

Theorem tf_8_14_16 : Adj17 8 14 -> Adj17 14 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 14. assume H2: Adj17 14 16. assume H3: Adj17 8 16.
exact Adj17_not_14_16 H2.
Qed.

Theorem tf_8_15_0 : Adj17 8 15 -> Adj17 15 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 0. assume H3: Adj17 8 0.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_1 : Adj17 8 15 -> Adj17 15 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 1. assume H3: Adj17 8 1.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_2 : Adj17 8 15 -> Adj17 15 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 2. assume H3: Adj17 8 2.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_3 : Adj17 8 15 -> Adj17 15 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 3. assume H3: Adj17 8 3.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_4 : Adj17 8 15 -> Adj17 15 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 4. assume H3: Adj17 8 4.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_5 : Adj17 8 15 -> Adj17 15 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 5. assume H3: Adj17 8 5.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_6 : Adj17 8 15 -> Adj17 15 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 6. assume H3: Adj17 8 6.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_7 : Adj17 8 15 -> Adj17 15 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 7. assume H3: Adj17 8 7.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_8 : Adj17 8 15 -> Adj17 15 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_15_9 : Adj17 8 15 -> Adj17 15 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 9. assume H3: Adj17 8 9.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_10 : Adj17 8 15 -> Adj17 15 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 10. assume H3: Adj17 8 10.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_11 : Adj17 8 15 -> Adj17 15 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 11. assume H3: Adj17 8 11.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_12 : Adj17 8 15 -> Adj17 15 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 12. assume H3: Adj17 8 12.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_13 : Adj17 8 15 -> Adj17 15 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 13. assume H3: Adj17 8 13.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_14 : Adj17 8 15 -> Adj17 15 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 14. assume H3: Adj17 8 14.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_15_15 : Adj17 8 15 -> Adj17 15 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 15. assume H3: Adj17 8 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_8_15_16 : Adj17 8 15 -> Adj17 15 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 15. assume H2: Adj17 15 16. assume H3: Adj17 8 16.
exact Adj17_not_8_15 H1.
Qed.

Theorem tf_8_16_0 : Adj17 8 16 -> Adj17 16 0 -> Adj17 8 0 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 0. assume H3: Adj17 8 0.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_1 : Adj17 8 16 -> Adj17 16 1 -> Adj17 8 1 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 1. assume H3: Adj17 8 1.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_2 : Adj17 8 16 -> Adj17 16 2 -> Adj17 8 2 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 2. assume H3: Adj17 8 2.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_3 : Adj17 8 16 -> Adj17 16 3 -> Adj17 8 3 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 3. assume H3: Adj17 8 3.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_4 : Adj17 8 16 -> Adj17 16 4 -> Adj17 8 4 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 4. assume H3: Adj17 8 4.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_5 : Adj17 8 16 -> Adj17 16 5 -> Adj17 8 5 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 5. assume H3: Adj17 8 5.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_6 : Adj17 8 16 -> Adj17 16 6 -> Adj17 8 6 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 6. assume H3: Adj17 8 6.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_7 : Adj17 8 16 -> Adj17 16 7 -> Adj17 8 7 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 7. assume H3: Adj17 8 7.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_8 : Adj17 8 16 -> Adj17 16 8 -> Adj17 8 8 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 8. assume H3: Adj17 8 8.
exact Adj17_not_8_8 H3.
Qed.

Theorem tf_8_16_9 : Adj17 8 16 -> Adj17 16 9 -> Adj17 8 9 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 9. assume H3: Adj17 8 9.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_10 : Adj17 8 16 -> Adj17 16 10 -> Adj17 8 10 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 10. assume H3: Adj17 8 10.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_11 : Adj17 8 16 -> Adj17 16 11 -> Adj17 8 11 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 11. assume H3: Adj17 8 11.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_12 : Adj17 8 16 -> Adj17 16 12 -> Adj17 8 12 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 12. assume H3: Adj17 8 12.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_13 : Adj17 8 16 -> Adj17 16 13 -> Adj17 8 13 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 13. assume H3: Adj17 8 13.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_14 : Adj17 8 16 -> Adj17 16 14 -> Adj17 8 14 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 14. assume H3: Adj17 8 14.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_15 : Adj17 8 16 -> Adj17 16 15 -> Adj17 8 15 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 15. assume H3: Adj17 8 15.
exact Adj17_not_8_16 H1.
Qed.

Theorem tf_8_16_16 : Adj17 8 16 -> Adj17 16 16 -> Adj17 8 16 -> False.
assume H1: Adj17 8 16. assume H2: Adj17 16 16. assume H3: Adj17 8 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_9_0_0 : Adj17 9 0 -> Adj17 0 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 0. assume H3: Adj17 9 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_9_0_1 : Adj17 9 0 -> Adj17 0 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 1. assume H3: Adj17 9 1.
exact Adj17_not_0_1 H2.
Qed.

Theorem tf_9_0_2 : Adj17 9 0 -> Adj17 0 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 2. assume H3: Adj17 9 2.
exact Adj17_not_0_2 H2.
Qed.

Theorem tf_9_0_3 : Adj17 9 0 -> Adj17 0 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 3. assume H3: Adj17 9 3.
exact Adj17_not_0_3 H2.
Qed.

Theorem tf_9_0_4 : Adj17 9 0 -> Adj17 0 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 4. assume H3: Adj17 9 4.
exact Adj17_not_0_4 H2.
Qed.

Theorem tf_9_0_5 : Adj17 9 0 -> Adj17 0 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 5. assume H3: Adj17 9 5.
exact Adj17_not_0_5 H2.
Qed.

Theorem tf_9_0_6 : Adj17 9 0 -> Adj17 0 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 6. assume H3: Adj17 9 6.
exact Adj17_not_0_6 H2.
Qed.

Theorem tf_9_0_7 : Adj17 9 0 -> Adj17 0 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 7. assume H3: Adj17 9 7.
exact Adj17_not_0_7 H2.
Qed.

Theorem tf_9_0_8 : Adj17 9 0 -> Adj17 0 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 8. assume H3: Adj17 9 8.
exact Adj17_not_0_8 H2.
Qed.

Theorem tf_9_0_9 : Adj17 9 0 -> Adj17 0 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_0_10 : Adj17 9 0 -> Adj17 0 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 10. assume H3: Adj17 9 10.
exact Adj17_not_0_10 H2.
Qed.

Theorem tf_9_0_11 : Adj17 9 0 -> Adj17 0 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 11. assume H3: Adj17 9 11.
exact Adj17_not_0_11 H2.
Qed.

Theorem tf_9_0_12 : Adj17 9 0 -> Adj17 0 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 12. assume H3: Adj17 9 12.
exact Adj17_not_0_12 H2.
Qed.

Theorem tf_9_0_13 : Adj17 9 0 -> Adj17 0 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 13. assume H3: Adj17 9 13.
exact Adj17_not_0_13 H2.
Qed.

Theorem tf_9_0_14 : Adj17 9 0 -> Adj17 0 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 14. assume H3: Adj17 9 14.
exact Adj17_not_9_14 H3.
Qed.

Theorem tf_9_0_15 : Adj17 9 0 -> Adj17 0 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 15. assume H3: Adj17 9 15.
exact Adj17_not_9_15 H3.
Qed.

Theorem tf_9_0_16 : Adj17 9 0 -> Adj17 0 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 0. assume H2: Adj17 0 16. assume H3: Adj17 9 16.
exact Adj17_not_9_16 H3.
Qed.

Theorem tf_9_1_0 : Adj17 9 1 -> Adj17 1 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 0. assume H3: Adj17 9 0.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_1 : Adj17 9 1 -> Adj17 1 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 1. assume H3: Adj17 9 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_9_1_2 : Adj17 9 1 -> Adj17 1 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 2. assume H3: Adj17 9 2.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_3 : Adj17 9 1 -> Adj17 1 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 3. assume H3: Adj17 9 3.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_4 : Adj17 9 1 -> Adj17 1 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 4. assume H3: Adj17 9 4.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_5 : Adj17 9 1 -> Adj17 1 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 5. assume H3: Adj17 9 5.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_6 : Adj17 9 1 -> Adj17 1 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 6. assume H3: Adj17 9 6.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_7 : Adj17 9 1 -> Adj17 1 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 7. assume H3: Adj17 9 7.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_8 : Adj17 9 1 -> Adj17 1 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 8. assume H3: Adj17 9 8.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_9 : Adj17 9 1 -> Adj17 1 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_1_10 : Adj17 9 1 -> Adj17 1 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 10. assume H3: Adj17 9 10.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_11 : Adj17 9 1 -> Adj17 1 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 11. assume H3: Adj17 9 11.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_12 : Adj17 9 1 -> Adj17 1 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 12. assume H3: Adj17 9 12.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_13 : Adj17 9 1 -> Adj17 1 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 13. assume H3: Adj17 9 13.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_14 : Adj17 9 1 -> Adj17 1 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 14. assume H3: Adj17 9 14.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_15 : Adj17 9 1 -> Adj17 1 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 15. assume H3: Adj17 9 15.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_1_16 : Adj17 9 1 -> Adj17 1 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 1. assume H2: Adj17 1 16. assume H3: Adj17 9 16.
exact Adj17_not_9_1 H1.
Qed.

Theorem tf_9_2_0 : Adj17 9 2 -> Adj17 2 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 0. assume H3: Adj17 9 0.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_1 : Adj17 9 2 -> Adj17 2 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 1. assume H3: Adj17 9 1.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_2 : Adj17 9 2 -> Adj17 2 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 2. assume H3: Adj17 9 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_9_2_3 : Adj17 9 2 -> Adj17 2 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 3. assume H3: Adj17 9 3.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_4 : Adj17 9 2 -> Adj17 2 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 4. assume H3: Adj17 9 4.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_5 : Adj17 9 2 -> Adj17 2 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 5. assume H3: Adj17 9 5.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_6 : Adj17 9 2 -> Adj17 2 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 6. assume H3: Adj17 9 6.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_7 : Adj17 9 2 -> Adj17 2 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 7. assume H3: Adj17 9 7.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_8 : Adj17 9 2 -> Adj17 2 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 8. assume H3: Adj17 9 8.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_9 : Adj17 9 2 -> Adj17 2 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_2_10 : Adj17 9 2 -> Adj17 2 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 10. assume H3: Adj17 9 10.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_11 : Adj17 9 2 -> Adj17 2 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 11. assume H3: Adj17 9 11.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_12 : Adj17 9 2 -> Adj17 2 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 12. assume H3: Adj17 9 12.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_13 : Adj17 9 2 -> Adj17 2 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 13. assume H3: Adj17 9 13.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_14 : Adj17 9 2 -> Adj17 2 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 14. assume H3: Adj17 9 14.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_15 : Adj17 9 2 -> Adj17 2 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 15. assume H3: Adj17 9 15.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_2_16 : Adj17 9 2 -> Adj17 2 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 2. assume H2: Adj17 2 16. assume H3: Adj17 9 16.
exact Adj17_not_9_2 H1.
Qed.

Theorem tf_9_3_0 : Adj17 9 3 -> Adj17 3 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 0. assume H3: Adj17 9 0.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_1 : Adj17 9 3 -> Adj17 3 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 1. assume H3: Adj17 9 1.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_2 : Adj17 9 3 -> Adj17 3 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 2. assume H3: Adj17 9 2.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_3 : Adj17 9 3 -> Adj17 3 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 3. assume H3: Adj17 9 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_9_3_4 : Adj17 9 3 -> Adj17 3 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 4. assume H3: Adj17 9 4.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_5 : Adj17 9 3 -> Adj17 3 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 5. assume H3: Adj17 9 5.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_6 : Adj17 9 3 -> Adj17 3 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 6. assume H3: Adj17 9 6.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_7 : Adj17 9 3 -> Adj17 3 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 7. assume H3: Adj17 9 7.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_8 : Adj17 9 3 -> Adj17 3 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 8. assume H3: Adj17 9 8.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_9 : Adj17 9 3 -> Adj17 3 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_3_10 : Adj17 9 3 -> Adj17 3 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 10. assume H3: Adj17 9 10.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_11 : Adj17 9 3 -> Adj17 3 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 11. assume H3: Adj17 9 11.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_12 : Adj17 9 3 -> Adj17 3 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 12. assume H3: Adj17 9 12.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_13 : Adj17 9 3 -> Adj17 3 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 13. assume H3: Adj17 9 13.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_14 : Adj17 9 3 -> Adj17 3 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 14. assume H3: Adj17 9 14.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_15 : Adj17 9 3 -> Adj17 3 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 15. assume H3: Adj17 9 15.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_3_16 : Adj17 9 3 -> Adj17 3 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 3. assume H2: Adj17 3 16. assume H3: Adj17 9 16.
exact Adj17_not_9_3 H1.
Qed.

Theorem tf_9_4_0 : Adj17 9 4 -> Adj17 4 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 0. assume H3: Adj17 9 0.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_1 : Adj17 9 4 -> Adj17 4 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 1. assume H3: Adj17 9 1.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_2 : Adj17 9 4 -> Adj17 4 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 2. assume H3: Adj17 9 2.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_3 : Adj17 9 4 -> Adj17 4 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 3. assume H3: Adj17 9 3.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_4 : Adj17 9 4 -> Adj17 4 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 4. assume H3: Adj17 9 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_9_4_5 : Adj17 9 4 -> Adj17 4 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 5. assume H3: Adj17 9 5.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_6 : Adj17 9 4 -> Adj17 4 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 6. assume H3: Adj17 9 6.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_7 : Adj17 9 4 -> Adj17 4 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 7. assume H3: Adj17 9 7.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_8 : Adj17 9 4 -> Adj17 4 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 8. assume H3: Adj17 9 8.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_9 : Adj17 9 4 -> Adj17 4 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_4_10 : Adj17 9 4 -> Adj17 4 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 10. assume H3: Adj17 9 10.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_11 : Adj17 9 4 -> Adj17 4 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 11. assume H3: Adj17 9 11.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_12 : Adj17 9 4 -> Adj17 4 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 12. assume H3: Adj17 9 12.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_13 : Adj17 9 4 -> Adj17 4 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 13. assume H3: Adj17 9 13.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_14 : Adj17 9 4 -> Adj17 4 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 14. assume H3: Adj17 9 14.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_15 : Adj17 9 4 -> Adj17 4 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 15. assume H3: Adj17 9 15.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_4_16 : Adj17 9 4 -> Adj17 4 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 4. assume H2: Adj17 4 16. assume H3: Adj17 9 16.
exact Adj17_not_9_4 H1.
Qed.

Theorem tf_9_5_0 : Adj17 9 5 -> Adj17 5 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 0. assume H3: Adj17 9 0.
exact Adj17_not_5_0 H2.
Qed.

Theorem tf_9_5_1 : Adj17 9 5 -> Adj17 5 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 1. assume H3: Adj17 9 1.
exact Adj17_not_5_1 H2.
Qed.

Theorem tf_9_5_2 : Adj17 9 5 -> Adj17 5 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 2. assume H3: Adj17 9 2.
exact Adj17_not_5_2 H2.
Qed.

Theorem tf_9_5_3 : Adj17 9 5 -> Adj17 5 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 3. assume H3: Adj17 9 3.
exact Adj17_not_5_3 H2.
Qed.

Theorem tf_9_5_4 : Adj17 9 5 -> Adj17 5 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 4. assume H3: Adj17 9 4.
exact Adj17_not_9_4 H3.
Qed.

Theorem tf_9_5_5 : Adj17 9 5 -> Adj17 5 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 5. assume H3: Adj17 9 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_9_5_6 : Adj17 9 5 -> Adj17 5 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 6. assume H3: Adj17 9 6.
exact Adj17_not_5_6 H2.
Qed.

Theorem tf_9_5_7 : Adj17 9 5 -> Adj17 5 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 7. assume H3: Adj17 9 7.
exact Adj17_not_5_7 H2.
Qed.

Theorem tf_9_5_8 : Adj17 9 5 -> Adj17 5 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 8. assume H3: Adj17 9 8.
exact Adj17_not_5_8 H2.
Qed.

Theorem tf_9_5_9 : Adj17 9 5 -> Adj17 5 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_5_10 : Adj17 9 5 -> Adj17 5 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 10. assume H3: Adj17 9 10.
exact Adj17_not_9_10 H3.
Qed.

Theorem tf_9_5_11 : Adj17 9 5 -> Adj17 5 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 11. assume H3: Adj17 9 11.
exact Adj17_not_9_11 H3.
Qed.

Theorem tf_9_5_12 : Adj17 9 5 -> Adj17 5 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 12. assume H3: Adj17 9 12.
exact Adj17_not_5_12 H2.
Qed.

Theorem tf_9_5_13 : Adj17 9 5 -> Adj17 5 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 13. assume H3: Adj17 9 13.
exact Adj17_not_9_13 H3.
Qed.

Theorem tf_9_5_14 : Adj17 9 5 -> Adj17 5 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 14. assume H3: Adj17 9 14.
exact Adj17_not_5_14 H2.
Qed.

Theorem tf_9_5_15 : Adj17 9 5 -> Adj17 5 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 15. assume H3: Adj17 9 15.
exact Adj17_not_5_15 H2.
Qed.

Theorem tf_9_5_16 : Adj17 9 5 -> Adj17 5 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 5. assume H2: Adj17 5 16. assume H3: Adj17 9 16.
exact Adj17_not_5_16 H2.
Qed.

Theorem tf_9_6_0 : Adj17 9 6 -> Adj17 6 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 0. assume H3: Adj17 9 0.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_1 : Adj17 9 6 -> Adj17 6 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 1. assume H3: Adj17 9 1.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_2 : Adj17 9 6 -> Adj17 6 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 2. assume H3: Adj17 9 2.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_3 : Adj17 9 6 -> Adj17 6 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 3. assume H3: Adj17 9 3.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_4 : Adj17 9 6 -> Adj17 6 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 4. assume H3: Adj17 9 4.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_5 : Adj17 9 6 -> Adj17 6 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 5. assume H3: Adj17 9 5.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_6 : Adj17 9 6 -> Adj17 6 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 6. assume H3: Adj17 9 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_9_6_7 : Adj17 9 6 -> Adj17 6 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 7. assume H3: Adj17 9 7.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_8 : Adj17 9 6 -> Adj17 6 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 8. assume H3: Adj17 9 8.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_9 : Adj17 9 6 -> Adj17 6 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_6_10 : Adj17 9 6 -> Adj17 6 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 10. assume H3: Adj17 9 10.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_11 : Adj17 9 6 -> Adj17 6 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 11. assume H3: Adj17 9 11.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_12 : Adj17 9 6 -> Adj17 6 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 12. assume H3: Adj17 9 12.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_13 : Adj17 9 6 -> Adj17 6 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 13. assume H3: Adj17 9 13.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_14 : Adj17 9 6 -> Adj17 6 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 14. assume H3: Adj17 9 14.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_15 : Adj17 9 6 -> Adj17 6 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 15. assume H3: Adj17 9 15.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_6_16 : Adj17 9 6 -> Adj17 6 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 6. assume H2: Adj17 6 16. assume H3: Adj17 9 16.
exact Adj17_not_9_6 H1.
Qed.

Theorem tf_9_7_0 : Adj17 9 7 -> Adj17 7 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 0. assume H3: Adj17 9 0.
exact Adj17_not_7_0 H2.
Qed.

Theorem tf_9_7_1 : Adj17 9 7 -> Adj17 7 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 1. assume H3: Adj17 9 1.
exact Adj17_not_9_1 H3.
Qed.

Theorem tf_9_7_2 : Adj17 9 7 -> Adj17 7 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 2. assume H3: Adj17 9 2.
exact Adj17_not_7_2 H2.
Qed.

Theorem tf_9_7_3 : Adj17 9 7 -> Adj17 7 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 3. assume H3: Adj17 9 3.
exact Adj17_not_7_3 H2.
Qed.

Theorem tf_9_7_4 : Adj17 9 7 -> Adj17 7 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 4. assume H3: Adj17 9 4.
exact Adj17_not_9_4 H3.
Qed.

Theorem tf_9_7_5 : Adj17 9 7 -> Adj17 7 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 5. assume H3: Adj17 9 5.
exact Adj17_not_7_5 H2.
Qed.

Theorem tf_9_7_6 : Adj17 9 7 -> Adj17 7 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 6. assume H3: Adj17 9 6.
exact Adj17_not_7_6 H2.
Qed.

Theorem tf_9_7_7 : Adj17 9 7 -> Adj17 7 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 7. assume H3: Adj17 9 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_9_7_8 : Adj17 9 7 -> Adj17 7 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 8. assume H3: Adj17 9 8.
exact Adj17_not_7_8 H2.
Qed.

Theorem tf_9_7_9 : Adj17 9 7 -> Adj17 7 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_7_10 : Adj17 9 7 -> Adj17 7 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 10. assume H3: Adj17 9 10.
exact Adj17_not_9_10 H3.
Qed.

Theorem tf_9_7_11 : Adj17 9 7 -> Adj17 7 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 11. assume H3: Adj17 9 11.
exact Adj17_not_7_11 H2.
Qed.

Theorem tf_9_7_12 : Adj17 9 7 -> Adj17 7 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 12. assume H3: Adj17 9 12.
exact Adj17_not_7_12 H2.
Qed.

Theorem tf_9_7_13 : Adj17 9 7 -> Adj17 7 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 13. assume H3: Adj17 9 13.
exact Adj17_not_7_13 H2.
Qed.

Theorem tf_9_7_14 : Adj17 9 7 -> Adj17 7 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 14. assume H3: Adj17 9 14.
exact Adj17_not_7_14 H2.
Qed.

Theorem tf_9_7_15 : Adj17 9 7 -> Adj17 7 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 15. assume H3: Adj17 9 15.
exact Adj17_not_9_15 H3.
Qed.

Theorem tf_9_7_16 : Adj17 9 7 -> Adj17 7 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 7. assume H2: Adj17 7 16. assume H3: Adj17 9 16.
exact Adj17_not_7_16 H2.
Qed.

Theorem tf_9_8_0 : Adj17 9 8 -> Adj17 8 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 0. assume H3: Adj17 9 0.
exact Adj17_not_8_0 H2.
Qed.

Theorem tf_9_8_1 : Adj17 9 8 -> Adj17 8 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 1. assume H3: Adj17 9 1.
exact Adj17_not_8_1 H2.
Qed.

Theorem tf_9_8_2 : Adj17 9 8 -> Adj17 8 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 2. assume H3: Adj17 9 2.
exact Adj17_not_9_2 H3.
Qed.

Theorem tf_9_8_3 : Adj17 9 8 -> Adj17 8 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 3. assume H3: Adj17 9 3.
exact Adj17_not_9_3 H3.
Qed.

Theorem tf_9_8_4 : Adj17 9 8 -> Adj17 8 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 4. assume H3: Adj17 9 4.
exact Adj17_not_8_4 H2.
Qed.

Theorem tf_9_8_5 : Adj17 9 8 -> Adj17 8 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 5. assume H3: Adj17 9 5.
exact Adj17_not_8_5 H2.
Qed.

Theorem tf_9_8_6 : Adj17 9 8 -> Adj17 8 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 6. assume H3: Adj17 9 6.
exact Adj17_not_8_6 H2.
Qed.

Theorem tf_9_8_7 : Adj17 9 8 -> Adj17 8 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 7. assume H3: Adj17 9 7.
exact Adj17_not_8_7 H2.
Qed.

Theorem tf_9_8_8 : Adj17 9 8 -> Adj17 8 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 8. assume H3: Adj17 9 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_9_8_9 : Adj17 9 8 -> Adj17 8 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_8_10 : Adj17 9 8 -> Adj17 8 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 10. assume H3: Adj17 9 10.
exact Adj17_not_8_10 H2.
Qed.

Theorem tf_9_8_11 : Adj17 9 8 -> Adj17 8 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 11. assume H3: Adj17 9 11.
exact Adj17_not_9_11 H3.
Qed.

Theorem tf_9_8_12 : Adj17 9 8 -> Adj17 8 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 12. assume H3: Adj17 9 12.
exact Adj17_not_8_12 H2.
Qed.

Theorem tf_9_8_13 : Adj17 9 8 -> Adj17 8 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 13. assume H3: Adj17 9 13.
exact Adj17_not_8_13 H2.
Qed.

Theorem tf_9_8_14 : Adj17 9 8 -> Adj17 8 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 14. assume H3: Adj17 9 14.
exact Adj17_not_9_14 H3.
Qed.

Theorem tf_9_8_15 : Adj17 9 8 -> Adj17 8 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 15. assume H3: Adj17 9 15.
exact Adj17_not_8_15 H2.
Qed.

Theorem tf_9_8_16 : Adj17 9 8 -> Adj17 8 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 8. assume H2: Adj17 8 16. assume H3: Adj17 9 16.
exact Adj17_not_8_16 H2.
Qed.

Theorem tf_9_9_0 : Adj17 9 9 -> Adj17 9 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 0. assume H3: Adj17 9 0.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_1 : Adj17 9 9 -> Adj17 9 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 1. assume H3: Adj17 9 1.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_2 : Adj17 9 9 -> Adj17 9 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 2. assume H3: Adj17 9 2.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_3 : Adj17 9 9 -> Adj17 9 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 3. assume H3: Adj17 9 3.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_4 : Adj17 9 9 -> Adj17 9 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 4. assume H3: Adj17 9 4.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_5 : Adj17 9 9 -> Adj17 9 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 5. assume H3: Adj17 9 5.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_6 : Adj17 9 9 -> Adj17 9 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 6. assume H3: Adj17 9 6.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_7 : Adj17 9 9 -> Adj17 9 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 7. assume H3: Adj17 9 7.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_8 : Adj17 9 9 -> Adj17 9 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 8. assume H3: Adj17 9 8.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_9 : Adj17 9 9 -> Adj17 9 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_10 : Adj17 9 9 -> Adj17 9 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 10. assume H3: Adj17 9 10.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_11 : Adj17 9 9 -> Adj17 9 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 11. assume H3: Adj17 9 11.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_12 : Adj17 9 9 -> Adj17 9 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 12. assume H3: Adj17 9 12.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_13 : Adj17 9 9 -> Adj17 9 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 13. assume H3: Adj17 9 13.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_14 : Adj17 9 9 -> Adj17 9 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 14. assume H3: Adj17 9 14.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_15 : Adj17 9 9 -> Adj17 9 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 15. assume H3: Adj17 9 15.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_9_16 : Adj17 9 9 -> Adj17 9 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 9. assume H2: Adj17 9 16. assume H3: Adj17 9 16.
exact Adj17_not_9_9 H1.
Qed.

Theorem tf_9_10_0 : Adj17 9 10 -> Adj17 10 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 0. assume H3: Adj17 9 0.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_1 : Adj17 9 10 -> Adj17 10 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 1. assume H3: Adj17 9 1.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_2 : Adj17 9 10 -> Adj17 10 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 2. assume H3: Adj17 9 2.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_3 : Adj17 9 10 -> Adj17 10 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 3. assume H3: Adj17 9 3.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_4 : Adj17 9 10 -> Adj17 10 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 4. assume H3: Adj17 9 4.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_5 : Adj17 9 10 -> Adj17 10 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 5. assume H3: Adj17 9 5.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_6 : Adj17 9 10 -> Adj17 10 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 6. assume H3: Adj17 9 6.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_7 : Adj17 9 10 -> Adj17 10 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 7. assume H3: Adj17 9 7.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_8 : Adj17 9 10 -> Adj17 10 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 8. assume H3: Adj17 9 8.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_9 : Adj17 9 10 -> Adj17 10 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_10_10 : Adj17 9 10 -> Adj17 10 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 10. assume H3: Adj17 9 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_9_10_11 : Adj17 9 10 -> Adj17 10 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 11. assume H3: Adj17 9 11.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_12 : Adj17 9 10 -> Adj17 10 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 12. assume H3: Adj17 9 12.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_13 : Adj17 9 10 -> Adj17 10 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 13. assume H3: Adj17 9 13.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_14 : Adj17 9 10 -> Adj17 10 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 14. assume H3: Adj17 9 14.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_15 : Adj17 9 10 -> Adj17 10 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 15. assume H3: Adj17 9 15.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_10_16 : Adj17 9 10 -> Adj17 10 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 10. assume H2: Adj17 10 16. assume H3: Adj17 9 16.
exact Adj17_not_9_10 H1.
Qed.

Theorem tf_9_11_0 : Adj17 9 11 -> Adj17 11 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 0. assume H3: Adj17 9 0.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_1 : Adj17 9 11 -> Adj17 11 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 1. assume H3: Adj17 9 1.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_2 : Adj17 9 11 -> Adj17 11 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 2. assume H3: Adj17 9 2.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_3 : Adj17 9 11 -> Adj17 11 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 3. assume H3: Adj17 9 3.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_4 : Adj17 9 11 -> Adj17 11 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 4. assume H3: Adj17 9 4.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_5 : Adj17 9 11 -> Adj17 11 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 5. assume H3: Adj17 9 5.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_6 : Adj17 9 11 -> Adj17 11 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 6. assume H3: Adj17 9 6.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_7 : Adj17 9 11 -> Adj17 11 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 7. assume H3: Adj17 9 7.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_8 : Adj17 9 11 -> Adj17 11 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 8. assume H3: Adj17 9 8.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_9 : Adj17 9 11 -> Adj17 11 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_11_10 : Adj17 9 11 -> Adj17 11 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 10. assume H3: Adj17 9 10.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_11 : Adj17 9 11 -> Adj17 11 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 11. assume H3: Adj17 9 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_9_11_12 : Adj17 9 11 -> Adj17 11 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 12. assume H3: Adj17 9 12.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_13 : Adj17 9 11 -> Adj17 11 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 13. assume H3: Adj17 9 13.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_14 : Adj17 9 11 -> Adj17 11 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 14. assume H3: Adj17 9 14.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_15 : Adj17 9 11 -> Adj17 11 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 15. assume H3: Adj17 9 15.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_11_16 : Adj17 9 11 -> Adj17 11 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 11. assume H2: Adj17 11 16. assume H3: Adj17 9 16.
exact Adj17_not_9_11 H1.
Qed.

Theorem tf_9_12_0 : Adj17 9 12 -> Adj17 12 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 0. assume H3: Adj17 9 0.
exact Adj17_not_12_0 H2.
Qed.

Theorem tf_9_12_1 : Adj17 9 12 -> Adj17 12 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 1. assume H3: Adj17 9 1.
exact Adj17_not_12_1 H2.
Qed.

Theorem tf_9_12_2 : Adj17 9 12 -> Adj17 12 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 2. assume H3: Adj17 9 2.
exact Adj17_not_9_2 H3.
Qed.

Theorem tf_9_12_3 : Adj17 9 12 -> Adj17 12 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 3. assume H3: Adj17 9 3.
exact Adj17_not_12_3 H2.
Qed.

Theorem tf_9_12_4 : Adj17 9 12 -> Adj17 12 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 4. assume H3: Adj17 9 4.
exact Adj17_not_9_4 H3.
Qed.

Theorem tf_9_12_5 : Adj17 9 12 -> Adj17 12 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 5. assume H3: Adj17 9 5.
exact Adj17_not_12_5 H2.
Qed.

Theorem tf_9_12_6 : Adj17 9 12 -> Adj17 12 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 6. assume H3: Adj17 9 6.
exact Adj17_not_9_6 H3.
Qed.

Theorem tf_9_12_7 : Adj17 9 12 -> Adj17 12 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 7. assume H3: Adj17 9 7.
exact Adj17_not_12_7 H2.
Qed.

Theorem tf_9_12_8 : Adj17 9 12 -> Adj17 12 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 8. assume H3: Adj17 9 8.
exact Adj17_not_12_8 H2.
Qed.

Theorem tf_9_12_9 : Adj17 9 12 -> Adj17 12 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_12_10 : Adj17 9 12 -> Adj17 12 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 10. assume H3: Adj17 9 10.
exact Adj17_not_12_10 H2.
Qed.

Theorem tf_9_12_11 : Adj17 9 12 -> Adj17 12 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 11. assume H3: Adj17 9 11.
exact Adj17_not_12_11 H2.
Qed.

Theorem tf_9_12_12 : Adj17 9 12 -> Adj17 12 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 12. assume H3: Adj17 9 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_9_12_13 : Adj17 9 12 -> Adj17 12 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 13. assume H3: Adj17 9 13.
exact Adj17_not_9_13 H3.
Qed.

Theorem tf_9_12_14 : Adj17 9 12 -> Adj17 12 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 14. assume H3: Adj17 9 14.
exact Adj17_not_12_14 H2.
Qed.

Theorem tf_9_12_15 : Adj17 9 12 -> Adj17 12 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 15. assume H3: Adj17 9 15.
exact Adj17_not_12_15 H2.
Qed.

Theorem tf_9_12_16 : Adj17 9 12 -> Adj17 12 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 12. assume H2: Adj17 12 16. assume H3: Adj17 9 16.
exact Adj17_not_12_16 H2.
Qed.

Theorem tf_9_13_0 : Adj17 9 13 -> Adj17 13 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 0. assume H3: Adj17 9 0.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_1 : Adj17 9 13 -> Adj17 13 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 1. assume H3: Adj17 9 1.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_2 : Adj17 9 13 -> Adj17 13 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 2. assume H3: Adj17 9 2.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_3 : Adj17 9 13 -> Adj17 13 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 3. assume H3: Adj17 9 3.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_4 : Adj17 9 13 -> Adj17 13 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 4. assume H3: Adj17 9 4.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_5 : Adj17 9 13 -> Adj17 13 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 5. assume H3: Adj17 9 5.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_6 : Adj17 9 13 -> Adj17 13 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 6. assume H3: Adj17 9 6.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_7 : Adj17 9 13 -> Adj17 13 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 7. assume H3: Adj17 9 7.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_8 : Adj17 9 13 -> Adj17 13 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 8. assume H3: Adj17 9 8.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_9 : Adj17 9 13 -> Adj17 13 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_13_10 : Adj17 9 13 -> Adj17 13 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 10. assume H3: Adj17 9 10.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_11 : Adj17 9 13 -> Adj17 13 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 11. assume H3: Adj17 9 11.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_12 : Adj17 9 13 -> Adj17 13 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 12. assume H3: Adj17 9 12.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_13 : Adj17 9 13 -> Adj17 13 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 13. assume H3: Adj17 9 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_9_13_14 : Adj17 9 13 -> Adj17 13 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 14. assume H3: Adj17 9 14.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_15 : Adj17 9 13 -> Adj17 13 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 15. assume H3: Adj17 9 15.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_13_16 : Adj17 9 13 -> Adj17 13 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 13. assume H2: Adj17 13 16. assume H3: Adj17 9 16.
exact Adj17_not_9_13 H1.
Qed.

Theorem tf_9_14_0 : Adj17 9 14 -> Adj17 14 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 0. assume H3: Adj17 9 0.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_1 : Adj17 9 14 -> Adj17 14 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 1. assume H3: Adj17 9 1.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_2 : Adj17 9 14 -> Adj17 14 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 2. assume H3: Adj17 9 2.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_3 : Adj17 9 14 -> Adj17 14 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 3. assume H3: Adj17 9 3.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_4 : Adj17 9 14 -> Adj17 14 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 4. assume H3: Adj17 9 4.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_5 : Adj17 9 14 -> Adj17 14 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 5. assume H3: Adj17 9 5.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_6 : Adj17 9 14 -> Adj17 14 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 6. assume H3: Adj17 9 6.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_7 : Adj17 9 14 -> Adj17 14 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 7. assume H3: Adj17 9 7.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_8 : Adj17 9 14 -> Adj17 14 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 8. assume H3: Adj17 9 8.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_9 : Adj17 9 14 -> Adj17 14 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_14_10 : Adj17 9 14 -> Adj17 14 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 10. assume H3: Adj17 9 10.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_11 : Adj17 9 14 -> Adj17 14 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 11. assume H3: Adj17 9 11.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_12 : Adj17 9 14 -> Adj17 14 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 12. assume H3: Adj17 9 12.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_13 : Adj17 9 14 -> Adj17 14 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 13. assume H3: Adj17 9 13.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_14 : Adj17 9 14 -> Adj17 14 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 14. assume H3: Adj17 9 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_9_14_15 : Adj17 9 14 -> Adj17 14 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 15. assume H3: Adj17 9 15.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_14_16 : Adj17 9 14 -> Adj17 14 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 14. assume H2: Adj17 14 16. assume H3: Adj17 9 16.
exact Adj17_not_9_14 H1.
Qed.

Theorem tf_9_15_0 : Adj17 9 15 -> Adj17 15 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 0. assume H3: Adj17 9 0.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_1 : Adj17 9 15 -> Adj17 15 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 1. assume H3: Adj17 9 1.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_2 : Adj17 9 15 -> Adj17 15 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 2. assume H3: Adj17 9 2.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_3 : Adj17 9 15 -> Adj17 15 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 3. assume H3: Adj17 9 3.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_4 : Adj17 9 15 -> Adj17 15 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 4. assume H3: Adj17 9 4.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_5 : Adj17 9 15 -> Adj17 15 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 5. assume H3: Adj17 9 5.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_6 : Adj17 9 15 -> Adj17 15 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 6. assume H3: Adj17 9 6.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_7 : Adj17 9 15 -> Adj17 15 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 7. assume H3: Adj17 9 7.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_8 : Adj17 9 15 -> Adj17 15 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 8. assume H3: Adj17 9 8.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_9 : Adj17 9 15 -> Adj17 15 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_15_10 : Adj17 9 15 -> Adj17 15 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 10. assume H3: Adj17 9 10.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_11 : Adj17 9 15 -> Adj17 15 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 11. assume H3: Adj17 9 11.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_12 : Adj17 9 15 -> Adj17 15 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 12. assume H3: Adj17 9 12.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_13 : Adj17 9 15 -> Adj17 15 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 13. assume H3: Adj17 9 13.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_14 : Adj17 9 15 -> Adj17 15 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 14. assume H3: Adj17 9 14.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_15_15 : Adj17 9 15 -> Adj17 15 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 15. assume H3: Adj17 9 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_9_15_16 : Adj17 9 15 -> Adj17 15 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 15. assume H2: Adj17 15 16. assume H3: Adj17 9 16.
exact Adj17_not_9_15 H1.
Qed.

Theorem tf_9_16_0 : Adj17 9 16 -> Adj17 16 0 -> Adj17 9 0 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 0. assume H3: Adj17 9 0.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_1 : Adj17 9 16 -> Adj17 16 1 -> Adj17 9 1 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 1. assume H3: Adj17 9 1.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_2 : Adj17 9 16 -> Adj17 16 2 -> Adj17 9 2 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 2. assume H3: Adj17 9 2.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_3 : Adj17 9 16 -> Adj17 16 3 -> Adj17 9 3 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 3. assume H3: Adj17 9 3.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_4 : Adj17 9 16 -> Adj17 16 4 -> Adj17 9 4 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 4. assume H3: Adj17 9 4.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_5 : Adj17 9 16 -> Adj17 16 5 -> Adj17 9 5 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 5. assume H3: Adj17 9 5.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_6 : Adj17 9 16 -> Adj17 16 6 -> Adj17 9 6 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 6. assume H3: Adj17 9 6.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_7 : Adj17 9 16 -> Adj17 16 7 -> Adj17 9 7 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 7. assume H3: Adj17 9 7.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_8 : Adj17 9 16 -> Adj17 16 8 -> Adj17 9 8 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 8. assume H3: Adj17 9 8.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_9 : Adj17 9 16 -> Adj17 16 9 -> Adj17 9 9 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 9. assume H3: Adj17 9 9.
exact Adj17_not_9_9 H3.
Qed.

Theorem tf_9_16_10 : Adj17 9 16 -> Adj17 16 10 -> Adj17 9 10 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 10. assume H3: Adj17 9 10.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_11 : Adj17 9 16 -> Adj17 16 11 -> Adj17 9 11 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 11. assume H3: Adj17 9 11.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_12 : Adj17 9 16 -> Adj17 16 12 -> Adj17 9 12 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 12. assume H3: Adj17 9 12.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_13 : Adj17 9 16 -> Adj17 16 13 -> Adj17 9 13 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 13. assume H3: Adj17 9 13.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_14 : Adj17 9 16 -> Adj17 16 14 -> Adj17 9 14 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 14. assume H3: Adj17 9 14.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_15 : Adj17 9 16 -> Adj17 16 15 -> Adj17 9 15 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 15. assume H3: Adj17 9 15.
exact Adj17_not_9_16 H1.
Qed.

Theorem tf_9_16_16 : Adj17 9 16 -> Adj17 16 16 -> Adj17 9 16 -> False.
assume H1: Adj17 9 16. assume H2: Adj17 16 16. assume H3: Adj17 9 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_10_0_0 : Adj17 10 0 -> Adj17 0 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 0. assume H3: Adj17 10 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_10_0_1 : Adj17 10 0 -> Adj17 0 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 1. assume H3: Adj17 10 1.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_2 : Adj17 10 0 -> Adj17 0 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 2. assume H3: Adj17 10 2.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_3 : Adj17 10 0 -> Adj17 0 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 3. assume H3: Adj17 10 3.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_4 : Adj17 10 0 -> Adj17 0 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 4. assume H3: Adj17 10 4.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_5 : Adj17 10 0 -> Adj17 0 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 5. assume H3: Adj17 10 5.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_6 : Adj17 10 0 -> Adj17 0 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 6. assume H3: Adj17 10 6.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_7 : Adj17 10 0 -> Adj17 0 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 7. assume H3: Adj17 10 7.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_8 : Adj17 10 0 -> Adj17 0 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 8. assume H3: Adj17 10 8.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_9 : Adj17 10 0 -> Adj17 0 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 9. assume H3: Adj17 10 9.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_10 : Adj17 10 0 -> Adj17 0 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_0_11 : Adj17 10 0 -> Adj17 0 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 11. assume H3: Adj17 10 11.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_12 : Adj17 10 0 -> Adj17 0 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 12. assume H3: Adj17 10 12.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_13 : Adj17 10 0 -> Adj17 0 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 13. assume H3: Adj17 10 13.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_14 : Adj17 10 0 -> Adj17 0 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 14. assume H3: Adj17 10 14.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_15 : Adj17 10 0 -> Adj17 0 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 15. assume H3: Adj17 10 15.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_0_16 : Adj17 10 0 -> Adj17 0 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 0. assume H2: Adj17 0 16. assume H3: Adj17 10 16.
exact Adj17_not_10_0 H1.
Qed.

Theorem tf_10_1_0 : Adj17 10 1 -> Adj17 1 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 0. assume H3: Adj17 10 0.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_1 : Adj17 10 1 -> Adj17 1 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 1. assume H3: Adj17 10 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_10_1_2 : Adj17 10 1 -> Adj17 1 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 2. assume H3: Adj17 10 2.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_3 : Adj17 10 1 -> Adj17 1 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 3. assume H3: Adj17 10 3.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_4 : Adj17 10 1 -> Adj17 1 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 4. assume H3: Adj17 10 4.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_5 : Adj17 10 1 -> Adj17 1 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 5. assume H3: Adj17 10 5.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_6 : Adj17 10 1 -> Adj17 1 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 6. assume H3: Adj17 10 6.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_7 : Adj17 10 1 -> Adj17 1 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 7. assume H3: Adj17 10 7.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_8 : Adj17 10 1 -> Adj17 1 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 8. assume H3: Adj17 10 8.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_9 : Adj17 10 1 -> Adj17 1 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 9. assume H3: Adj17 10 9.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_10 : Adj17 10 1 -> Adj17 1 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_1_11 : Adj17 10 1 -> Adj17 1 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 11. assume H3: Adj17 10 11.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_12 : Adj17 10 1 -> Adj17 1 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 12. assume H3: Adj17 10 12.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_13 : Adj17 10 1 -> Adj17 1 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 13. assume H3: Adj17 10 13.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_14 : Adj17 10 1 -> Adj17 1 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 14. assume H3: Adj17 10 14.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_15 : Adj17 10 1 -> Adj17 1 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 15. assume H3: Adj17 10 15.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_1_16 : Adj17 10 1 -> Adj17 1 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 1. assume H2: Adj17 1 16. assume H3: Adj17 10 16.
exact Adj17_not_10_1 H1.
Qed.

Theorem tf_10_2_0 : Adj17 10 2 -> Adj17 2 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 0. assume H3: Adj17 10 0.
exact Adj17_not_2_0 H2.
Qed.

Theorem tf_10_2_1 : Adj17 10 2 -> Adj17 2 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 1. assume H3: Adj17 10 1.
exact Adj17_not_2_1 H2.
Qed.

Theorem tf_10_2_2 : Adj17 10 2 -> Adj17 2 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 2. assume H3: Adj17 10 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_10_2_3 : Adj17 10 2 -> Adj17 2 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 3. assume H3: Adj17 10 3.
exact Adj17_not_2_3 H2.
Qed.

Theorem tf_10_2_4 : Adj17 10 2 -> Adj17 2 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 4. assume H3: Adj17 10 4.
exact Adj17_not_2_4 H2.
Qed.

Theorem tf_10_2_5 : Adj17 10 2 -> Adj17 2 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 5. assume H3: Adj17 10 5.
exact Adj17_not_2_5 H2.
Qed.

Theorem tf_10_2_6 : Adj17 10 2 -> Adj17 2 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 6. assume H3: Adj17 10 6.
exact Adj17_not_2_6 H2.
Qed.

Theorem tf_10_2_7 : Adj17 10 2 -> Adj17 2 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 7. assume H3: Adj17 10 7.
exact Adj17_not_2_7 H2.
Qed.

Theorem tf_10_2_8 : Adj17 10 2 -> Adj17 2 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 8. assume H3: Adj17 10 8.
exact Adj17_not_10_8 H3.
Qed.

Theorem tf_10_2_9 : Adj17 10 2 -> Adj17 2 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 9. assume H3: Adj17 10 9.
exact Adj17_not_2_9 H2.
Qed.

Theorem tf_10_2_10 : Adj17 10 2 -> Adj17 2 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_2_11 : Adj17 10 2 -> Adj17 2 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 11. assume H3: Adj17 10 11.
exact Adj17_not_2_11 H2.
Qed.

Theorem tf_10_2_12 : Adj17 10 2 -> Adj17 2 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 12. assume H3: Adj17 10 12.
exact Adj17_not_10_12 H3.
Qed.

Theorem tf_10_2_13 : Adj17 10 2 -> Adj17 2 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 13. assume H3: Adj17 10 13.
exact Adj17_not_2_13 H2.
Qed.

Theorem tf_10_2_14 : Adj17 10 2 -> Adj17 2 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 14. assume H3: Adj17 10 14.
exact Adj17_not_2_14 H2.
Qed.

Theorem tf_10_2_15 : Adj17 10 2 -> Adj17 2 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 15. assume H3: Adj17 10 15.
exact Adj17_not_10_15 H3.
Qed.

Theorem tf_10_2_16 : Adj17 10 2 -> Adj17 2 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 2. assume H2: Adj17 2 16. assume H3: Adj17 10 16.
exact Adj17_not_2_16 H2.
Qed.

Theorem tf_10_3_0 : Adj17 10 3 -> Adj17 3 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 0. assume H3: Adj17 10 0.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_1 : Adj17 10 3 -> Adj17 3 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 1. assume H3: Adj17 10 1.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_2 : Adj17 10 3 -> Adj17 3 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 2. assume H3: Adj17 10 2.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_3 : Adj17 10 3 -> Adj17 3 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 3. assume H3: Adj17 10 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_10_3_4 : Adj17 10 3 -> Adj17 3 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 4. assume H3: Adj17 10 4.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_5 : Adj17 10 3 -> Adj17 3 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 5. assume H3: Adj17 10 5.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_6 : Adj17 10 3 -> Adj17 3 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 6. assume H3: Adj17 10 6.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_7 : Adj17 10 3 -> Adj17 3 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 7. assume H3: Adj17 10 7.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_8 : Adj17 10 3 -> Adj17 3 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 8. assume H3: Adj17 10 8.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_9 : Adj17 10 3 -> Adj17 3 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 9. assume H3: Adj17 10 9.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_10 : Adj17 10 3 -> Adj17 3 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_3_11 : Adj17 10 3 -> Adj17 3 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 11. assume H3: Adj17 10 11.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_12 : Adj17 10 3 -> Adj17 3 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 12. assume H3: Adj17 10 12.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_13 : Adj17 10 3 -> Adj17 3 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 13. assume H3: Adj17 10 13.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_14 : Adj17 10 3 -> Adj17 3 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 14. assume H3: Adj17 10 14.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_15 : Adj17 10 3 -> Adj17 3 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 15. assume H3: Adj17 10 15.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_3_16 : Adj17 10 3 -> Adj17 3 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 3. assume H2: Adj17 3 16. assume H3: Adj17 10 16.
exact Adj17_not_10_3 H1.
Qed.

Theorem tf_10_4_0 : Adj17 10 4 -> Adj17 4 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 0. assume H3: Adj17 10 0.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_1 : Adj17 10 4 -> Adj17 4 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 1. assume H3: Adj17 10 1.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_2 : Adj17 10 4 -> Adj17 4 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 2. assume H3: Adj17 10 2.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_3 : Adj17 10 4 -> Adj17 4 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 3. assume H3: Adj17 10 3.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_4 : Adj17 10 4 -> Adj17 4 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 4. assume H3: Adj17 10 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_10_4_5 : Adj17 10 4 -> Adj17 4 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 5. assume H3: Adj17 10 5.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_6 : Adj17 10 4 -> Adj17 4 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 6. assume H3: Adj17 10 6.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_7 : Adj17 10 4 -> Adj17 4 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 7. assume H3: Adj17 10 7.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_8 : Adj17 10 4 -> Adj17 4 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 8. assume H3: Adj17 10 8.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_9 : Adj17 10 4 -> Adj17 4 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 9. assume H3: Adj17 10 9.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_10 : Adj17 10 4 -> Adj17 4 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_4_11 : Adj17 10 4 -> Adj17 4 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 11. assume H3: Adj17 10 11.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_12 : Adj17 10 4 -> Adj17 4 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 12. assume H3: Adj17 10 12.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_13 : Adj17 10 4 -> Adj17 4 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 13. assume H3: Adj17 10 13.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_14 : Adj17 10 4 -> Adj17 4 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 14. assume H3: Adj17 10 14.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_15 : Adj17 10 4 -> Adj17 4 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 15. assume H3: Adj17 10 15.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_4_16 : Adj17 10 4 -> Adj17 4 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 4. assume H2: Adj17 4 16. assume H3: Adj17 10 16.
exact Adj17_not_10_4 H1.
Qed.

Theorem tf_10_5_0 : Adj17 10 5 -> Adj17 5 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 0. assume H3: Adj17 10 0.
exact Adj17_not_5_0 H2.
Qed.

Theorem tf_10_5_1 : Adj17 10 5 -> Adj17 5 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 1. assume H3: Adj17 10 1.
exact Adj17_not_5_1 H2.
Qed.

Theorem tf_10_5_2 : Adj17 10 5 -> Adj17 5 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 2. assume H3: Adj17 10 2.
exact Adj17_not_5_2 H2.
Qed.

Theorem tf_10_5_3 : Adj17 10 5 -> Adj17 5 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 3. assume H3: Adj17 10 3.
exact Adj17_not_5_3 H2.
Qed.

Theorem tf_10_5_4 : Adj17 10 5 -> Adj17 5 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 4. assume H3: Adj17 10 4.
exact Adj17_not_10_4 H3.
Qed.

Theorem tf_10_5_5 : Adj17 10 5 -> Adj17 5 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 5. assume H3: Adj17 10 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_10_5_6 : Adj17 10 5 -> Adj17 5 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 6. assume H3: Adj17 10 6.
exact Adj17_not_5_6 H2.
Qed.

Theorem tf_10_5_7 : Adj17 10 5 -> Adj17 5 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 7. assume H3: Adj17 10 7.
exact Adj17_not_5_7 H2.
Qed.

Theorem tf_10_5_8 : Adj17 10 5 -> Adj17 5 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 8. assume H3: Adj17 10 8.
exact Adj17_not_5_8 H2.
Qed.

Theorem tf_10_5_9 : Adj17 10 5 -> Adj17 5 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 9. assume H3: Adj17 10 9.
exact Adj17_not_10_9 H3.
Qed.

Theorem tf_10_5_10 : Adj17 10 5 -> Adj17 5 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_5_11 : Adj17 10 5 -> Adj17 5 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 11. assume H3: Adj17 10 11.
exact Adj17_not_10_11 H3.
Qed.

Theorem tf_10_5_12 : Adj17 10 5 -> Adj17 5 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 12. assume H3: Adj17 10 12.
exact Adj17_not_5_12 H2.
Qed.

Theorem tf_10_5_13 : Adj17 10 5 -> Adj17 5 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 13. assume H3: Adj17 10 13.
exact Adj17_not_10_13 H3.
Qed.

Theorem tf_10_5_14 : Adj17 10 5 -> Adj17 5 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 14. assume H3: Adj17 10 14.
exact Adj17_not_5_14 H2.
Qed.

Theorem tf_10_5_15 : Adj17 10 5 -> Adj17 5 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 15. assume H3: Adj17 10 15.
exact Adj17_not_5_15 H2.
Qed.

Theorem tf_10_5_16 : Adj17 10 5 -> Adj17 5 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 5. assume H2: Adj17 5 16. assume H3: Adj17 10 16.
exact Adj17_not_5_16 H2.
Qed.

Theorem tf_10_6_0 : Adj17 10 6 -> Adj17 6 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 0. assume H3: Adj17 10 0.
exact Adj17_not_6_0 H2.
Qed.

Theorem tf_10_6_1 : Adj17 10 6 -> Adj17 6 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 1. assume H3: Adj17 10 1.
exact Adj17_not_6_1 H2.
Qed.

Theorem tf_10_6_2 : Adj17 10 6 -> Adj17 6 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 2. assume H3: Adj17 10 2.
exact Adj17_not_6_2 H2.
Qed.

Theorem tf_10_6_3 : Adj17 10 6 -> Adj17 6 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 3. assume H3: Adj17 10 3.
exact Adj17_not_10_3 H3.
Qed.

Theorem tf_10_6_4 : Adj17 10 6 -> Adj17 6 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 4. assume H3: Adj17 10 4.
exact Adj17_not_6_4 H2.
Qed.

Theorem tf_10_6_5 : Adj17 10 6 -> Adj17 6 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 5. assume H3: Adj17 10 5.
exact Adj17_not_6_5 H2.
Qed.

Theorem tf_10_6_6 : Adj17 10 6 -> Adj17 6 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 6. assume H3: Adj17 10 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_10_6_7 : Adj17 10 6 -> Adj17 6 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 7. assume H3: Adj17 10 7.
exact Adj17_not_6_7 H2.
Qed.

Theorem tf_10_6_8 : Adj17 10 6 -> Adj17 6 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 8. assume H3: Adj17 10 8.
exact Adj17_not_6_8 H2.
Qed.

Theorem tf_10_6_9 : Adj17 10 6 -> Adj17 6 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 9. assume H3: Adj17 10 9.
exact Adj17_not_6_9 H2.
Qed.

Theorem tf_10_6_10 : Adj17 10 6 -> Adj17 6 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_6_11 : Adj17 10 6 -> Adj17 6 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 11. assume H3: Adj17 10 11.
exact Adj17_not_10_11 H3.
Qed.

Theorem tf_10_6_12 : Adj17 10 6 -> Adj17 6 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 12. assume H3: Adj17 10 12.
exact Adj17_not_10_12 H3.
Qed.

Theorem tf_10_6_13 : Adj17 10 6 -> Adj17 6 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 13. assume H3: Adj17 10 13.
exact Adj17_not_6_13 H2.
Qed.

Theorem tf_10_6_14 : Adj17 10 6 -> Adj17 6 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 14. assume H3: Adj17 10 14.
exact Adj17_not_10_14 H3.
Qed.

Theorem tf_10_6_15 : Adj17 10 6 -> Adj17 6 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 15. assume H3: Adj17 10 15.
exact Adj17_not_6_15 H2.
Qed.

Theorem tf_10_6_16 : Adj17 10 6 -> Adj17 6 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 6. assume H2: Adj17 6 16. assume H3: Adj17 10 16.
exact Adj17_not_6_16 H2.
Qed.

Theorem tf_10_7_0 : Adj17 10 7 -> Adj17 7 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 0. assume H3: Adj17 10 0.
exact Adj17_not_7_0 H2.
Qed.

Theorem tf_10_7_1 : Adj17 10 7 -> Adj17 7 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 1. assume H3: Adj17 10 1.
exact Adj17_not_10_1 H3.
Qed.

Theorem tf_10_7_2 : Adj17 10 7 -> Adj17 7 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 2. assume H3: Adj17 10 2.
exact Adj17_not_7_2 H2.
Qed.

Theorem tf_10_7_3 : Adj17 10 7 -> Adj17 7 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 3. assume H3: Adj17 10 3.
exact Adj17_not_7_3 H2.
Qed.

Theorem tf_10_7_4 : Adj17 10 7 -> Adj17 7 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 4. assume H3: Adj17 10 4.
exact Adj17_not_10_4 H3.
Qed.

Theorem tf_10_7_5 : Adj17 10 7 -> Adj17 7 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 5. assume H3: Adj17 10 5.
exact Adj17_not_7_5 H2.
Qed.

Theorem tf_10_7_6 : Adj17 10 7 -> Adj17 7 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 6. assume H3: Adj17 10 6.
exact Adj17_not_7_6 H2.
Qed.

Theorem tf_10_7_7 : Adj17 10 7 -> Adj17 7 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 7. assume H3: Adj17 10 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_10_7_8 : Adj17 10 7 -> Adj17 7 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 8. assume H3: Adj17 10 8.
exact Adj17_not_7_8 H2.
Qed.

Theorem tf_10_7_9 : Adj17 10 7 -> Adj17 7 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 9. assume H3: Adj17 10 9.
exact Adj17_not_10_9 H3.
Qed.

Theorem tf_10_7_10 : Adj17 10 7 -> Adj17 7 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_7_11 : Adj17 10 7 -> Adj17 7 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 11. assume H3: Adj17 10 11.
exact Adj17_not_7_11 H2.
Qed.

Theorem tf_10_7_12 : Adj17 10 7 -> Adj17 7 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 12. assume H3: Adj17 10 12.
exact Adj17_not_7_12 H2.
Qed.

Theorem tf_10_7_13 : Adj17 10 7 -> Adj17 7 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 13. assume H3: Adj17 10 13.
exact Adj17_not_7_13 H2.
Qed.

Theorem tf_10_7_14 : Adj17 10 7 -> Adj17 7 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 14. assume H3: Adj17 10 14.
exact Adj17_not_7_14 H2.
Qed.

Theorem tf_10_7_15 : Adj17 10 7 -> Adj17 7 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 15. assume H3: Adj17 10 15.
exact Adj17_not_10_15 H3.
Qed.

Theorem tf_10_7_16 : Adj17 10 7 -> Adj17 7 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 7. assume H2: Adj17 7 16. assume H3: Adj17 10 16.
exact Adj17_not_7_16 H2.
Qed.

Theorem tf_10_8_0 : Adj17 10 8 -> Adj17 8 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 0. assume H3: Adj17 10 0.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_1 : Adj17 10 8 -> Adj17 8 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 1. assume H3: Adj17 10 1.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_2 : Adj17 10 8 -> Adj17 8 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 2. assume H3: Adj17 10 2.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_3 : Adj17 10 8 -> Adj17 8 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 3. assume H3: Adj17 10 3.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_4 : Adj17 10 8 -> Adj17 8 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 4. assume H3: Adj17 10 4.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_5 : Adj17 10 8 -> Adj17 8 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 5. assume H3: Adj17 10 5.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_6 : Adj17 10 8 -> Adj17 8 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 6. assume H3: Adj17 10 6.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_7 : Adj17 10 8 -> Adj17 8 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 7. assume H3: Adj17 10 7.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_8 : Adj17 10 8 -> Adj17 8 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 8. assume H3: Adj17 10 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_10_8_9 : Adj17 10 8 -> Adj17 8 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 9. assume H3: Adj17 10 9.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_10 : Adj17 10 8 -> Adj17 8 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_8_11 : Adj17 10 8 -> Adj17 8 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 11. assume H3: Adj17 10 11.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_12 : Adj17 10 8 -> Adj17 8 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 12. assume H3: Adj17 10 12.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_13 : Adj17 10 8 -> Adj17 8 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 13. assume H3: Adj17 10 13.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_14 : Adj17 10 8 -> Adj17 8 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 14. assume H3: Adj17 10 14.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_15 : Adj17 10 8 -> Adj17 8 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 15. assume H3: Adj17 10 15.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_8_16 : Adj17 10 8 -> Adj17 8 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 8. assume H2: Adj17 8 16. assume H3: Adj17 10 16.
exact Adj17_not_10_8 H1.
Qed.

Theorem tf_10_9_0 : Adj17 10 9 -> Adj17 9 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 0. assume H3: Adj17 10 0.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_1 : Adj17 10 9 -> Adj17 9 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 1. assume H3: Adj17 10 1.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_2 : Adj17 10 9 -> Adj17 9 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 2. assume H3: Adj17 10 2.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_3 : Adj17 10 9 -> Adj17 9 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 3. assume H3: Adj17 10 3.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_4 : Adj17 10 9 -> Adj17 9 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 4. assume H3: Adj17 10 4.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_5 : Adj17 10 9 -> Adj17 9 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 5. assume H3: Adj17 10 5.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_6 : Adj17 10 9 -> Adj17 9 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 6. assume H3: Adj17 10 6.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_7 : Adj17 10 9 -> Adj17 9 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 7. assume H3: Adj17 10 7.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_8 : Adj17 10 9 -> Adj17 9 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 8. assume H3: Adj17 10 8.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_9 : Adj17 10 9 -> Adj17 9 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 9. assume H3: Adj17 10 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_10_9_10 : Adj17 10 9 -> Adj17 9 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_9_11 : Adj17 10 9 -> Adj17 9 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 11. assume H3: Adj17 10 11.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_12 : Adj17 10 9 -> Adj17 9 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 12. assume H3: Adj17 10 12.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_13 : Adj17 10 9 -> Adj17 9 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 13. assume H3: Adj17 10 13.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_14 : Adj17 10 9 -> Adj17 9 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 14. assume H3: Adj17 10 14.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_15 : Adj17 10 9 -> Adj17 9 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 15. assume H3: Adj17 10 15.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_9_16 : Adj17 10 9 -> Adj17 9 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 9. assume H2: Adj17 9 16. assume H3: Adj17 10 16.
exact Adj17_not_10_9 H1.
Qed.

Theorem tf_10_10_0 : Adj17 10 10 -> Adj17 10 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 0. assume H3: Adj17 10 0.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_1 : Adj17 10 10 -> Adj17 10 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 1. assume H3: Adj17 10 1.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_2 : Adj17 10 10 -> Adj17 10 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 2. assume H3: Adj17 10 2.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_3 : Adj17 10 10 -> Adj17 10 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 3. assume H3: Adj17 10 3.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_4 : Adj17 10 10 -> Adj17 10 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 4. assume H3: Adj17 10 4.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_5 : Adj17 10 10 -> Adj17 10 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 5. assume H3: Adj17 10 5.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_6 : Adj17 10 10 -> Adj17 10 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 6. assume H3: Adj17 10 6.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_7 : Adj17 10 10 -> Adj17 10 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 7. assume H3: Adj17 10 7.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_8 : Adj17 10 10 -> Adj17 10 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 8. assume H3: Adj17 10 8.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_9 : Adj17 10 10 -> Adj17 10 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 9. assume H3: Adj17 10 9.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_10 : Adj17 10 10 -> Adj17 10 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_11 : Adj17 10 10 -> Adj17 10 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 11. assume H3: Adj17 10 11.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_12 : Adj17 10 10 -> Adj17 10 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 12. assume H3: Adj17 10 12.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_13 : Adj17 10 10 -> Adj17 10 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 13. assume H3: Adj17 10 13.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_14 : Adj17 10 10 -> Adj17 10 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 14. assume H3: Adj17 10 14.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_15 : Adj17 10 10 -> Adj17 10 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 15. assume H3: Adj17 10 15.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_10_16 : Adj17 10 10 -> Adj17 10 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 10. assume H2: Adj17 10 16. assume H3: Adj17 10 16.
exact Adj17_not_10_10 H1.
Qed.

Theorem tf_10_11_0 : Adj17 10 11 -> Adj17 11 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 0. assume H3: Adj17 10 0.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_1 : Adj17 10 11 -> Adj17 11 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 1. assume H3: Adj17 10 1.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_2 : Adj17 10 11 -> Adj17 11 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 2. assume H3: Adj17 10 2.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_3 : Adj17 10 11 -> Adj17 11 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 3. assume H3: Adj17 10 3.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_4 : Adj17 10 11 -> Adj17 11 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 4. assume H3: Adj17 10 4.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_5 : Adj17 10 11 -> Adj17 11 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 5. assume H3: Adj17 10 5.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_6 : Adj17 10 11 -> Adj17 11 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 6. assume H3: Adj17 10 6.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_7 : Adj17 10 11 -> Adj17 11 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 7. assume H3: Adj17 10 7.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_8 : Adj17 10 11 -> Adj17 11 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 8. assume H3: Adj17 10 8.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_9 : Adj17 10 11 -> Adj17 11 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 9. assume H3: Adj17 10 9.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_10 : Adj17 10 11 -> Adj17 11 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_11_11 : Adj17 10 11 -> Adj17 11 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 11. assume H3: Adj17 10 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_10_11_12 : Adj17 10 11 -> Adj17 11 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 12. assume H3: Adj17 10 12.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_13 : Adj17 10 11 -> Adj17 11 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 13. assume H3: Adj17 10 13.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_14 : Adj17 10 11 -> Adj17 11 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 14. assume H3: Adj17 10 14.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_15 : Adj17 10 11 -> Adj17 11 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 15. assume H3: Adj17 10 15.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_11_16 : Adj17 10 11 -> Adj17 11 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 11. assume H2: Adj17 11 16. assume H3: Adj17 10 16.
exact Adj17_not_10_11 H1.
Qed.

Theorem tf_10_12_0 : Adj17 10 12 -> Adj17 12 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 0. assume H3: Adj17 10 0.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_1 : Adj17 10 12 -> Adj17 12 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 1. assume H3: Adj17 10 1.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_2 : Adj17 10 12 -> Adj17 12 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 2. assume H3: Adj17 10 2.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_3 : Adj17 10 12 -> Adj17 12 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 3. assume H3: Adj17 10 3.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_4 : Adj17 10 12 -> Adj17 12 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 4. assume H3: Adj17 10 4.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_5 : Adj17 10 12 -> Adj17 12 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 5. assume H3: Adj17 10 5.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_6 : Adj17 10 12 -> Adj17 12 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 6. assume H3: Adj17 10 6.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_7 : Adj17 10 12 -> Adj17 12 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 7. assume H3: Adj17 10 7.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_8 : Adj17 10 12 -> Adj17 12 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 8. assume H3: Adj17 10 8.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_9 : Adj17 10 12 -> Adj17 12 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 9. assume H3: Adj17 10 9.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_10 : Adj17 10 12 -> Adj17 12 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_12_11 : Adj17 10 12 -> Adj17 12 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 11. assume H3: Adj17 10 11.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_12 : Adj17 10 12 -> Adj17 12 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 12. assume H3: Adj17 10 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_10_12_13 : Adj17 10 12 -> Adj17 12 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 13. assume H3: Adj17 10 13.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_14 : Adj17 10 12 -> Adj17 12 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 14. assume H3: Adj17 10 14.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_15 : Adj17 10 12 -> Adj17 12 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 15. assume H3: Adj17 10 15.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_12_16 : Adj17 10 12 -> Adj17 12 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 12. assume H2: Adj17 12 16. assume H3: Adj17 10 16.
exact Adj17_not_10_12 H1.
Qed.

Theorem tf_10_13_0 : Adj17 10 13 -> Adj17 13 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 0. assume H3: Adj17 10 0.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_1 : Adj17 10 13 -> Adj17 13 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 1. assume H3: Adj17 10 1.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_2 : Adj17 10 13 -> Adj17 13 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 2. assume H3: Adj17 10 2.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_3 : Adj17 10 13 -> Adj17 13 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 3. assume H3: Adj17 10 3.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_4 : Adj17 10 13 -> Adj17 13 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 4. assume H3: Adj17 10 4.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_5 : Adj17 10 13 -> Adj17 13 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 5. assume H3: Adj17 10 5.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_6 : Adj17 10 13 -> Adj17 13 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 6. assume H3: Adj17 10 6.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_7 : Adj17 10 13 -> Adj17 13 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 7. assume H3: Adj17 10 7.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_8 : Adj17 10 13 -> Adj17 13 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 8. assume H3: Adj17 10 8.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_9 : Adj17 10 13 -> Adj17 13 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 9. assume H3: Adj17 10 9.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_10 : Adj17 10 13 -> Adj17 13 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_13_11 : Adj17 10 13 -> Adj17 13 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 11. assume H3: Adj17 10 11.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_12 : Adj17 10 13 -> Adj17 13 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 12. assume H3: Adj17 10 12.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_13 : Adj17 10 13 -> Adj17 13 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 13. assume H3: Adj17 10 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_10_13_14 : Adj17 10 13 -> Adj17 13 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 14. assume H3: Adj17 10 14.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_15 : Adj17 10 13 -> Adj17 13 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 15. assume H3: Adj17 10 15.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_13_16 : Adj17 10 13 -> Adj17 13 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 13. assume H2: Adj17 13 16. assume H3: Adj17 10 16.
exact Adj17_not_10_13 H1.
Qed.

Theorem tf_10_14_0 : Adj17 10 14 -> Adj17 14 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 0. assume H3: Adj17 10 0.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_1 : Adj17 10 14 -> Adj17 14 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 1. assume H3: Adj17 10 1.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_2 : Adj17 10 14 -> Adj17 14 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 2. assume H3: Adj17 10 2.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_3 : Adj17 10 14 -> Adj17 14 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 3. assume H3: Adj17 10 3.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_4 : Adj17 10 14 -> Adj17 14 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 4. assume H3: Adj17 10 4.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_5 : Adj17 10 14 -> Adj17 14 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 5. assume H3: Adj17 10 5.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_6 : Adj17 10 14 -> Adj17 14 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 6. assume H3: Adj17 10 6.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_7 : Adj17 10 14 -> Adj17 14 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 7. assume H3: Adj17 10 7.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_8 : Adj17 10 14 -> Adj17 14 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 8. assume H3: Adj17 10 8.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_9 : Adj17 10 14 -> Adj17 14 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 9. assume H3: Adj17 10 9.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_10 : Adj17 10 14 -> Adj17 14 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_14_11 : Adj17 10 14 -> Adj17 14 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 11. assume H3: Adj17 10 11.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_12 : Adj17 10 14 -> Adj17 14 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 12. assume H3: Adj17 10 12.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_13 : Adj17 10 14 -> Adj17 14 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 13. assume H3: Adj17 10 13.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_14 : Adj17 10 14 -> Adj17 14 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 14. assume H3: Adj17 10 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_10_14_15 : Adj17 10 14 -> Adj17 14 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 15. assume H3: Adj17 10 15.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_14_16 : Adj17 10 14 -> Adj17 14 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 14. assume H2: Adj17 14 16. assume H3: Adj17 10 16.
exact Adj17_not_10_14 H1.
Qed.

Theorem tf_10_15_0 : Adj17 10 15 -> Adj17 15 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 0. assume H3: Adj17 10 0.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_1 : Adj17 10 15 -> Adj17 15 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 1. assume H3: Adj17 10 1.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_2 : Adj17 10 15 -> Adj17 15 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 2. assume H3: Adj17 10 2.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_3 : Adj17 10 15 -> Adj17 15 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 3. assume H3: Adj17 10 3.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_4 : Adj17 10 15 -> Adj17 15 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 4. assume H3: Adj17 10 4.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_5 : Adj17 10 15 -> Adj17 15 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 5. assume H3: Adj17 10 5.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_6 : Adj17 10 15 -> Adj17 15 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 6. assume H3: Adj17 10 6.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_7 : Adj17 10 15 -> Adj17 15 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 7. assume H3: Adj17 10 7.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_8 : Adj17 10 15 -> Adj17 15 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 8. assume H3: Adj17 10 8.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_9 : Adj17 10 15 -> Adj17 15 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 9. assume H3: Adj17 10 9.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_10 : Adj17 10 15 -> Adj17 15 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_15_11 : Adj17 10 15 -> Adj17 15 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 11. assume H3: Adj17 10 11.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_12 : Adj17 10 15 -> Adj17 15 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 12. assume H3: Adj17 10 12.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_13 : Adj17 10 15 -> Adj17 15 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 13. assume H3: Adj17 10 13.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_14 : Adj17 10 15 -> Adj17 15 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 14. assume H3: Adj17 10 14.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_15_15 : Adj17 10 15 -> Adj17 15 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 15. assume H3: Adj17 10 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_10_15_16 : Adj17 10 15 -> Adj17 15 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 15. assume H2: Adj17 15 16. assume H3: Adj17 10 16.
exact Adj17_not_10_15 H1.
Qed.

Theorem tf_10_16_0 : Adj17 10 16 -> Adj17 16 0 -> Adj17 10 0 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 0. assume H3: Adj17 10 0.
exact Adj17_not_10_0 H3.
Qed.

Theorem tf_10_16_1 : Adj17 10 16 -> Adj17 16 1 -> Adj17 10 1 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 1. assume H3: Adj17 10 1.
exact Adj17_not_10_1 H3.
Qed.

Theorem tf_10_16_2 : Adj17 10 16 -> Adj17 16 2 -> Adj17 10 2 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 2. assume H3: Adj17 10 2.
exact Adj17_not_16_2 H2.
Qed.

Theorem tf_10_16_3 : Adj17 10 16 -> Adj17 16 3 -> Adj17 10 3 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 3. assume H3: Adj17 10 3.
exact Adj17_not_10_3 H3.
Qed.

Theorem tf_10_16_4 : Adj17 10 16 -> Adj17 16 4 -> Adj17 10 4 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 4. assume H3: Adj17 10 4.
exact Adj17_not_10_4 H3.
Qed.

Theorem tf_10_16_5 : Adj17 10 16 -> Adj17 16 5 -> Adj17 10 5 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 5. assume H3: Adj17 10 5.
exact Adj17_not_16_5 H2.
Qed.

Theorem tf_10_16_6 : Adj17 10 16 -> Adj17 16 6 -> Adj17 10 6 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 6. assume H3: Adj17 10 6.
exact Adj17_not_16_6 H2.
Qed.

Theorem tf_10_16_7 : Adj17 10 16 -> Adj17 16 7 -> Adj17 10 7 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 7. assume H3: Adj17 10 7.
exact Adj17_not_16_7 H2.
Qed.

Theorem tf_10_16_8 : Adj17 10 16 -> Adj17 16 8 -> Adj17 10 8 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 8. assume H3: Adj17 10 8.
exact Adj17_not_16_8 H2.
Qed.

Theorem tf_10_16_9 : Adj17 10 16 -> Adj17 16 9 -> Adj17 10 9 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 9. assume H3: Adj17 10 9.
exact Adj17_not_16_9 H2.
Qed.

Theorem tf_10_16_10 : Adj17 10 16 -> Adj17 16 10 -> Adj17 10 10 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 10. assume H3: Adj17 10 10.
exact Adj17_not_10_10 H3.
Qed.

Theorem tf_10_16_11 : Adj17 10 16 -> Adj17 16 11 -> Adj17 10 11 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 11. assume H3: Adj17 10 11.
exact Adj17_not_16_11 H2.
Qed.

Theorem tf_10_16_12 : Adj17 10 16 -> Adj17 16 12 -> Adj17 10 12 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 12. assume H3: Adj17 10 12.
exact Adj17_not_16_12 H2.
Qed.

Theorem tf_10_16_13 : Adj17 10 16 -> Adj17 16 13 -> Adj17 10 13 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 13. assume H3: Adj17 10 13.
exact Adj17_not_16_13 H2.
Qed.

Theorem tf_10_16_14 : Adj17 10 16 -> Adj17 16 14 -> Adj17 10 14 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 14. assume H3: Adj17 10 14.
exact Adj17_not_16_14 H2.
Qed.

Theorem tf_10_16_15 : Adj17 10 16 -> Adj17 16 15 -> Adj17 10 15 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 15. assume H3: Adj17 10 15.
exact Adj17_not_16_15 H2.
Qed.

Theorem tf_10_16_16 : Adj17 10 16 -> Adj17 16 16 -> Adj17 10 16 -> False.
assume H1: Adj17 10 16. assume H2: Adj17 16 16. assume H3: Adj17 10 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_11_0_0 : Adj17 11 0 -> Adj17 0 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 0. assume H3: Adj17 11 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_11_0_1 : Adj17 11 0 -> Adj17 0 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 1. assume H3: Adj17 11 1.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_2 : Adj17 11 0 -> Adj17 0 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 2. assume H3: Adj17 11 2.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_3 : Adj17 11 0 -> Adj17 0 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 3. assume H3: Adj17 11 3.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_4 : Adj17 11 0 -> Adj17 0 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 4. assume H3: Adj17 11 4.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_5 : Adj17 11 0 -> Adj17 0 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 5. assume H3: Adj17 11 5.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_6 : Adj17 11 0 -> Adj17 0 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 6. assume H3: Adj17 11 6.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_7 : Adj17 11 0 -> Adj17 0 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 7. assume H3: Adj17 11 7.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_8 : Adj17 11 0 -> Adj17 0 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 8. assume H3: Adj17 11 8.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_9 : Adj17 11 0 -> Adj17 0 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 9. assume H3: Adj17 11 9.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_10 : Adj17 11 0 -> Adj17 0 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 10. assume H3: Adj17 11 10.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_11 : Adj17 11 0 -> Adj17 0 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_0_12 : Adj17 11 0 -> Adj17 0 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 12. assume H3: Adj17 11 12.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_13 : Adj17 11 0 -> Adj17 0 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 13. assume H3: Adj17 11 13.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_14 : Adj17 11 0 -> Adj17 0 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 14. assume H3: Adj17 11 14.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_15 : Adj17 11 0 -> Adj17 0 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 15. assume H3: Adj17 11 15.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_0_16 : Adj17 11 0 -> Adj17 0 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 0. assume H2: Adj17 0 16. assume H3: Adj17 11 16.
exact Adj17_not_11_0 H1.
Qed.

Theorem tf_11_1_0 : Adj17 11 1 -> Adj17 1 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 0. assume H3: Adj17 11 0.
exact Adj17_not_1_0 H2.
Qed.

Theorem tf_11_1_1 : Adj17 11 1 -> Adj17 1 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 1. assume H3: Adj17 11 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_11_1_2 : Adj17 11 1 -> Adj17 1 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 2. assume H3: Adj17 11 2.
exact Adj17_not_1_2 H2.
Qed.

Theorem tf_11_1_3 : Adj17 11 1 -> Adj17 1 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 3. assume H3: Adj17 11 3.
exact Adj17_not_1_3 H2.
Qed.

Theorem tf_11_1_4 : Adj17 11 1 -> Adj17 1 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 4. assume H3: Adj17 11 4.
exact Adj17_not_1_4 H2.
Qed.

Theorem tf_11_1_5 : Adj17 11 1 -> Adj17 1 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 5. assume H3: Adj17 11 5.
exact Adj17_not_1_5 H2.
Qed.

Theorem tf_11_1_6 : Adj17 11 1 -> Adj17 1 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 6. assume H3: Adj17 11 6.
exact Adj17_not_1_6 H2.
Qed.

Theorem tf_11_1_7 : Adj17 11 1 -> Adj17 1 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 7. assume H3: Adj17 11 7.
exact Adj17_not_11_7 H3.
Qed.

Theorem tf_11_1_8 : Adj17 11 1 -> Adj17 1 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 8. assume H3: Adj17 11 8.
exact Adj17_not_1_8 H2.
Qed.

Theorem tf_11_1_9 : Adj17 11 1 -> Adj17 1 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 9. assume H3: Adj17 11 9.
exact Adj17_not_1_9 H2.
Qed.

Theorem tf_11_1_10 : Adj17 11 1 -> Adj17 1 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 10. assume H3: Adj17 11 10.
exact Adj17_not_1_10 H2.
Qed.

Theorem tf_11_1_11 : Adj17 11 1 -> Adj17 1 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_1_12 : Adj17 11 1 -> Adj17 1 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 12. assume H3: Adj17 11 12.
exact Adj17_not_1_12 H2.
Qed.

Theorem tf_11_1_13 : Adj17 11 1 -> Adj17 1 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 13. assume H3: Adj17 11 13.
exact Adj17_not_11_13 H3.
Qed.

Theorem tf_11_1_14 : Adj17 11 1 -> Adj17 1 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 14. assume H3: Adj17 11 14.
exact Adj17_not_1_14 H2.
Qed.

Theorem tf_11_1_15 : Adj17 11 1 -> Adj17 1 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 15. assume H3: Adj17 11 15.
exact Adj17_not_1_15 H2.
Qed.

Theorem tf_11_1_16 : Adj17 11 1 -> Adj17 1 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 1. assume H2: Adj17 1 16. assume H3: Adj17 11 16.
exact Adj17_not_11_16 H3.
Qed.

Theorem tf_11_2_0 : Adj17 11 2 -> Adj17 2 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 0. assume H3: Adj17 11 0.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_1 : Adj17 11 2 -> Adj17 2 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 1. assume H3: Adj17 11 1.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_2 : Adj17 11 2 -> Adj17 2 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 2. assume H3: Adj17 11 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_11_2_3 : Adj17 11 2 -> Adj17 2 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 3. assume H3: Adj17 11 3.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_4 : Adj17 11 2 -> Adj17 2 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 4. assume H3: Adj17 11 4.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_5 : Adj17 11 2 -> Adj17 2 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 5. assume H3: Adj17 11 5.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_6 : Adj17 11 2 -> Adj17 2 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 6. assume H3: Adj17 11 6.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_7 : Adj17 11 2 -> Adj17 2 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 7. assume H3: Adj17 11 7.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_8 : Adj17 11 2 -> Adj17 2 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 8. assume H3: Adj17 11 8.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_9 : Adj17 11 2 -> Adj17 2 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 9. assume H3: Adj17 11 9.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_10 : Adj17 11 2 -> Adj17 2 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 10. assume H3: Adj17 11 10.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_11 : Adj17 11 2 -> Adj17 2 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_2_12 : Adj17 11 2 -> Adj17 2 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 12. assume H3: Adj17 11 12.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_13 : Adj17 11 2 -> Adj17 2 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 13. assume H3: Adj17 11 13.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_14 : Adj17 11 2 -> Adj17 2 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 14. assume H3: Adj17 11 14.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_15 : Adj17 11 2 -> Adj17 2 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 15. assume H3: Adj17 11 15.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_2_16 : Adj17 11 2 -> Adj17 2 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 2. assume H2: Adj17 2 16. assume H3: Adj17 11 16.
exact Adj17_not_11_2 H1.
Qed.

Theorem tf_11_3_0 : Adj17 11 3 -> Adj17 3 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 0. assume H3: Adj17 11 0.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_1 : Adj17 11 3 -> Adj17 3 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 1. assume H3: Adj17 11 1.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_2 : Adj17 11 3 -> Adj17 3 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 2. assume H3: Adj17 11 2.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_3 : Adj17 11 3 -> Adj17 3 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 3. assume H3: Adj17 11 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_11_3_4 : Adj17 11 3 -> Adj17 3 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 4. assume H3: Adj17 11 4.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_5 : Adj17 11 3 -> Adj17 3 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 5. assume H3: Adj17 11 5.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_6 : Adj17 11 3 -> Adj17 3 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 6. assume H3: Adj17 11 6.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_7 : Adj17 11 3 -> Adj17 3 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 7. assume H3: Adj17 11 7.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_8 : Adj17 11 3 -> Adj17 3 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 8. assume H3: Adj17 11 8.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_9 : Adj17 11 3 -> Adj17 3 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 9. assume H3: Adj17 11 9.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_10 : Adj17 11 3 -> Adj17 3 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 10. assume H3: Adj17 11 10.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_11 : Adj17 11 3 -> Adj17 3 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_3_12 : Adj17 11 3 -> Adj17 3 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 12. assume H3: Adj17 11 12.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_13 : Adj17 11 3 -> Adj17 3 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 13. assume H3: Adj17 11 13.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_14 : Adj17 11 3 -> Adj17 3 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 14. assume H3: Adj17 11 14.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_15 : Adj17 11 3 -> Adj17 3 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 15. assume H3: Adj17 11 15.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_3_16 : Adj17 11 3 -> Adj17 3 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 3. assume H2: Adj17 3 16. assume H3: Adj17 11 16.
exact Adj17_not_11_3 H1.
Qed.

Theorem tf_11_4_0 : Adj17 11 4 -> Adj17 4 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 0. assume H3: Adj17 11 0.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_1 : Adj17 11 4 -> Adj17 4 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 1. assume H3: Adj17 11 1.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_2 : Adj17 11 4 -> Adj17 4 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 2. assume H3: Adj17 11 2.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_3 : Adj17 11 4 -> Adj17 4 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 3. assume H3: Adj17 11 3.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_4 : Adj17 11 4 -> Adj17 4 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 4. assume H3: Adj17 11 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_11_4_5 : Adj17 11 4 -> Adj17 4 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 5. assume H3: Adj17 11 5.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_6 : Adj17 11 4 -> Adj17 4 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 6. assume H3: Adj17 11 6.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_7 : Adj17 11 4 -> Adj17 4 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 7. assume H3: Adj17 11 7.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_8 : Adj17 11 4 -> Adj17 4 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 8. assume H3: Adj17 11 8.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_9 : Adj17 11 4 -> Adj17 4 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 9. assume H3: Adj17 11 9.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_10 : Adj17 11 4 -> Adj17 4 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 10. assume H3: Adj17 11 10.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_11 : Adj17 11 4 -> Adj17 4 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_4_12 : Adj17 11 4 -> Adj17 4 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 12. assume H3: Adj17 11 12.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_13 : Adj17 11 4 -> Adj17 4 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 13. assume H3: Adj17 11 13.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_14 : Adj17 11 4 -> Adj17 4 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 14. assume H3: Adj17 11 14.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_15 : Adj17 11 4 -> Adj17 4 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 15. assume H3: Adj17 11 15.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_4_16 : Adj17 11 4 -> Adj17 4 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 4. assume H2: Adj17 4 16. assume H3: Adj17 11 16.
exact Adj17_not_11_4 H1.
Qed.

Theorem tf_11_5_0 : Adj17 11 5 -> Adj17 5 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 0. assume H3: Adj17 11 0.
exact Adj17_not_5_0 H2.
Qed.

Theorem tf_11_5_1 : Adj17 11 5 -> Adj17 5 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 1. assume H3: Adj17 11 1.
exact Adj17_not_5_1 H2.
Qed.

Theorem tf_11_5_2 : Adj17 11 5 -> Adj17 5 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 2. assume H3: Adj17 11 2.
exact Adj17_not_5_2 H2.
Qed.

Theorem tf_11_5_3 : Adj17 11 5 -> Adj17 5 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 3. assume H3: Adj17 11 3.
exact Adj17_not_5_3 H2.
Qed.

Theorem tf_11_5_4 : Adj17 11 5 -> Adj17 5 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 4. assume H3: Adj17 11 4.
exact Adj17_not_11_4 H3.
Qed.

Theorem tf_11_5_5 : Adj17 11 5 -> Adj17 5 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 5. assume H3: Adj17 11 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_11_5_6 : Adj17 11 5 -> Adj17 5 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 6. assume H3: Adj17 11 6.
exact Adj17_not_5_6 H2.
Qed.

Theorem tf_11_5_7 : Adj17 11 5 -> Adj17 5 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 7. assume H3: Adj17 11 7.
exact Adj17_not_5_7 H2.
Qed.

Theorem tf_11_5_8 : Adj17 11 5 -> Adj17 5 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 8. assume H3: Adj17 11 8.
exact Adj17_not_5_8 H2.
Qed.

Theorem tf_11_5_9 : Adj17 11 5 -> Adj17 5 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 9. assume H3: Adj17 11 9.
exact Adj17_not_11_9 H3.
Qed.

Theorem tf_11_5_10 : Adj17 11 5 -> Adj17 5 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 10. assume H3: Adj17 11 10.
exact Adj17_not_11_10 H3.
Qed.

Theorem tf_11_5_11 : Adj17 11 5 -> Adj17 5 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_5_12 : Adj17 11 5 -> Adj17 5 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 12. assume H3: Adj17 11 12.
exact Adj17_not_5_12 H2.
Qed.

Theorem tf_11_5_13 : Adj17 11 5 -> Adj17 5 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 13. assume H3: Adj17 11 13.
exact Adj17_not_11_13 H3.
Qed.

Theorem tf_11_5_14 : Adj17 11 5 -> Adj17 5 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 14. assume H3: Adj17 11 14.
exact Adj17_not_5_14 H2.
Qed.

Theorem tf_11_5_15 : Adj17 11 5 -> Adj17 5 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 15. assume H3: Adj17 11 15.
exact Adj17_not_5_15 H2.
Qed.

Theorem tf_11_5_16 : Adj17 11 5 -> Adj17 5 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 5. assume H2: Adj17 5 16. assume H3: Adj17 11 16.
exact Adj17_not_5_16 H2.
Qed.

Theorem tf_11_6_0 : Adj17 11 6 -> Adj17 6 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 0. assume H3: Adj17 11 0.
exact Adj17_not_6_0 H2.
Qed.

Theorem tf_11_6_1 : Adj17 11 6 -> Adj17 6 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 1. assume H3: Adj17 11 1.
exact Adj17_not_6_1 H2.
Qed.

Theorem tf_11_6_2 : Adj17 11 6 -> Adj17 6 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 2. assume H3: Adj17 11 2.
exact Adj17_not_6_2 H2.
Qed.

Theorem tf_11_6_3 : Adj17 11 6 -> Adj17 6 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 3. assume H3: Adj17 11 3.
exact Adj17_not_11_3 H3.
Qed.

Theorem tf_11_6_4 : Adj17 11 6 -> Adj17 6 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 4. assume H3: Adj17 11 4.
exact Adj17_not_6_4 H2.
Qed.

Theorem tf_11_6_5 : Adj17 11 6 -> Adj17 6 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 5. assume H3: Adj17 11 5.
exact Adj17_not_6_5 H2.
Qed.

Theorem tf_11_6_6 : Adj17 11 6 -> Adj17 6 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 6. assume H3: Adj17 11 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_11_6_7 : Adj17 11 6 -> Adj17 6 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 7. assume H3: Adj17 11 7.
exact Adj17_not_6_7 H2.
Qed.

Theorem tf_11_6_8 : Adj17 11 6 -> Adj17 6 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 8. assume H3: Adj17 11 8.
exact Adj17_not_6_8 H2.
Qed.

Theorem tf_11_6_9 : Adj17 11 6 -> Adj17 6 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 9. assume H3: Adj17 11 9.
exact Adj17_not_6_9 H2.
Qed.

Theorem tf_11_6_10 : Adj17 11 6 -> Adj17 6 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 10. assume H3: Adj17 11 10.
exact Adj17_not_11_10 H3.
Qed.

Theorem tf_11_6_11 : Adj17 11 6 -> Adj17 6 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_6_12 : Adj17 11 6 -> Adj17 6 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 12. assume H3: Adj17 11 12.
exact Adj17_not_11_12 H3.
Qed.

Theorem tf_11_6_13 : Adj17 11 6 -> Adj17 6 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 13. assume H3: Adj17 11 13.
exact Adj17_not_6_13 H2.
Qed.

Theorem tf_11_6_14 : Adj17 11 6 -> Adj17 6 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 14. assume H3: Adj17 11 14.
exact Adj17_not_11_14 H3.
Qed.

Theorem tf_11_6_15 : Adj17 11 6 -> Adj17 6 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 15. assume H3: Adj17 11 15.
exact Adj17_not_6_15 H2.
Qed.

Theorem tf_11_6_16 : Adj17 11 6 -> Adj17 6 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 6. assume H2: Adj17 6 16. assume H3: Adj17 11 16.
exact Adj17_not_6_16 H2.
Qed.

Theorem tf_11_7_0 : Adj17 11 7 -> Adj17 7 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 0. assume H3: Adj17 11 0.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_1 : Adj17 11 7 -> Adj17 7 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 1. assume H3: Adj17 11 1.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_2 : Adj17 11 7 -> Adj17 7 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 2. assume H3: Adj17 11 2.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_3 : Adj17 11 7 -> Adj17 7 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 3. assume H3: Adj17 11 3.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_4 : Adj17 11 7 -> Adj17 7 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 4. assume H3: Adj17 11 4.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_5 : Adj17 11 7 -> Adj17 7 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 5. assume H3: Adj17 11 5.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_6 : Adj17 11 7 -> Adj17 7 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 6. assume H3: Adj17 11 6.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_7 : Adj17 11 7 -> Adj17 7 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 7. assume H3: Adj17 11 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_11_7_8 : Adj17 11 7 -> Adj17 7 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 8. assume H3: Adj17 11 8.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_9 : Adj17 11 7 -> Adj17 7 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 9. assume H3: Adj17 11 9.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_10 : Adj17 11 7 -> Adj17 7 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 10. assume H3: Adj17 11 10.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_11 : Adj17 11 7 -> Adj17 7 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_7_12 : Adj17 11 7 -> Adj17 7 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 12. assume H3: Adj17 11 12.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_13 : Adj17 11 7 -> Adj17 7 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 13. assume H3: Adj17 11 13.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_14 : Adj17 11 7 -> Adj17 7 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 14. assume H3: Adj17 11 14.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_15 : Adj17 11 7 -> Adj17 7 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 15. assume H3: Adj17 11 15.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_7_16 : Adj17 11 7 -> Adj17 7 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 7. assume H2: Adj17 7 16. assume H3: Adj17 11 16.
exact Adj17_not_11_7 H1.
Qed.

Theorem tf_11_8_0 : Adj17 11 8 -> Adj17 8 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 0. assume H3: Adj17 11 0.
exact Adj17_not_8_0 H2.
Qed.

Theorem tf_11_8_1 : Adj17 11 8 -> Adj17 8 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 1. assume H3: Adj17 11 1.
exact Adj17_not_8_1 H2.
Qed.

Theorem tf_11_8_2 : Adj17 11 8 -> Adj17 8 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 2. assume H3: Adj17 11 2.
exact Adj17_not_11_2 H3.
Qed.

Theorem tf_11_8_3 : Adj17 11 8 -> Adj17 8 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 3. assume H3: Adj17 11 3.
exact Adj17_not_11_3 H3.
Qed.

Theorem tf_11_8_4 : Adj17 11 8 -> Adj17 8 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 4. assume H3: Adj17 11 4.
exact Adj17_not_8_4 H2.
Qed.

Theorem tf_11_8_5 : Adj17 11 8 -> Adj17 8 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 5. assume H3: Adj17 11 5.
exact Adj17_not_8_5 H2.
Qed.

Theorem tf_11_8_6 : Adj17 11 8 -> Adj17 8 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 6. assume H3: Adj17 11 6.
exact Adj17_not_8_6 H2.
Qed.

Theorem tf_11_8_7 : Adj17 11 8 -> Adj17 8 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 7. assume H3: Adj17 11 7.
exact Adj17_not_8_7 H2.
Qed.

Theorem tf_11_8_8 : Adj17 11 8 -> Adj17 8 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 8. assume H3: Adj17 11 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_11_8_9 : Adj17 11 8 -> Adj17 8 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 9. assume H3: Adj17 11 9.
exact Adj17_not_11_9 H3.
Qed.

Theorem tf_11_8_10 : Adj17 11 8 -> Adj17 8 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 10. assume H3: Adj17 11 10.
exact Adj17_not_8_10 H2.
Qed.

Theorem tf_11_8_11 : Adj17 11 8 -> Adj17 8 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_8_12 : Adj17 11 8 -> Adj17 8 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 12. assume H3: Adj17 11 12.
exact Adj17_not_8_12 H2.
Qed.

Theorem tf_11_8_13 : Adj17 11 8 -> Adj17 8 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 13. assume H3: Adj17 11 13.
exact Adj17_not_8_13 H2.
Qed.

Theorem tf_11_8_14 : Adj17 11 8 -> Adj17 8 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 14. assume H3: Adj17 11 14.
exact Adj17_not_11_14 H3.
Qed.

Theorem tf_11_8_15 : Adj17 11 8 -> Adj17 8 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 15. assume H3: Adj17 11 15.
exact Adj17_not_8_15 H2.
Qed.

Theorem tf_11_8_16 : Adj17 11 8 -> Adj17 8 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 8. assume H2: Adj17 8 16. assume H3: Adj17 11 16.
exact Adj17_not_8_16 H2.
Qed.

Theorem tf_11_9_0 : Adj17 11 9 -> Adj17 9 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 0. assume H3: Adj17 11 0.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_1 : Adj17 11 9 -> Adj17 9 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 1. assume H3: Adj17 11 1.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_2 : Adj17 11 9 -> Adj17 9 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 2. assume H3: Adj17 11 2.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_3 : Adj17 11 9 -> Adj17 9 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 3. assume H3: Adj17 11 3.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_4 : Adj17 11 9 -> Adj17 9 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 4. assume H3: Adj17 11 4.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_5 : Adj17 11 9 -> Adj17 9 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 5. assume H3: Adj17 11 5.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_6 : Adj17 11 9 -> Adj17 9 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 6. assume H3: Adj17 11 6.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_7 : Adj17 11 9 -> Adj17 9 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 7. assume H3: Adj17 11 7.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_8 : Adj17 11 9 -> Adj17 9 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 8. assume H3: Adj17 11 8.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_9 : Adj17 11 9 -> Adj17 9 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 9. assume H3: Adj17 11 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_11_9_10 : Adj17 11 9 -> Adj17 9 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 10. assume H3: Adj17 11 10.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_11 : Adj17 11 9 -> Adj17 9 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_9_12 : Adj17 11 9 -> Adj17 9 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 12. assume H3: Adj17 11 12.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_13 : Adj17 11 9 -> Adj17 9 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 13. assume H3: Adj17 11 13.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_14 : Adj17 11 9 -> Adj17 9 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 14. assume H3: Adj17 11 14.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_15 : Adj17 11 9 -> Adj17 9 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 15. assume H3: Adj17 11 15.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_9_16 : Adj17 11 9 -> Adj17 9 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 9. assume H2: Adj17 9 16. assume H3: Adj17 11 16.
exact Adj17_not_11_9 H1.
Qed.

Theorem tf_11_10_0 : Adj17 11 10 -> Adj17 10 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 0. assume H3: Adj17 11 0.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_1 : Adj17 11 10 -> Adj17 10 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 1. assume H3: Adj17 11 1.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_2 : Adj17 11 10 -> Adj17 10 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 2. assume H3: Adj17 11 2.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_3 : Adj17 11 10 -> Adj17 10 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 3. assume H3: Adj17 11 3.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_4 : Adj17 11 10 -> Adj17 10 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 4. assume H3: Adj17 11 4.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_5 : Adj17 11 10 -> Adj17 10 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 5. assume H3: Adj17 11 5.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_6 : Adj17 11 10 -> Adj17 10 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 6. assume H3: Adj17 11 6.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_7 : Adj17 11 10 -> Adj17 10 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 7. assume H3: Adj17 11 7.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_8 : Adj17 11 10 -> Adj17 10 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 8. assume H3: Adj17 11 8.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_9 : Adj17 11 10 -> Adj17 10 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 9. assume H3: Adj17 11 9.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_10 : Adj17 11 10 -> Adj17 10 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 10. assume H3: Adj17 11 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_11_10_11 : Adj17 11 10 -> Adj17 10 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_10_12 : Adj17 11 10 -> Adj17 10 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 12. assume H3: Adj17 11 12.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_13 : Adj17 11 10 -> Adj17 10 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 13. assume H3: Adj17 11 13.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_14 : Adj17 11 10 -> Adj17 10 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 14. assume H3: Adj17 11 14.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_15 : Adj17 11 10 -> Adj17 10 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 15. assume H3: Adj17 11 15.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_10_16 : Adj17 11 10 -> Adj17 10 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 10. assume H2: Adj17 10 16. assume H3: Adj17 11 16.
exact Adj17_not_11_10 H1.
Qed.

Theorem tf_11_11_0 : Adj17 11 11 -> Adj17 11 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 0. assume H3: Adj17 11 0.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_1 : Adj17 11 11 -> Adj17 11 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 1. assume H3: Adj17 11 1.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_2 : Adj17 11 11 -> Adj17 11 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 2. assume H3: Adj17 11 2.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_3 : Adj17 11 11 -> Adj17 11 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 3. assume H3: Adj17 11 3.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_4 : Adj17 11 11 -> Adj17 11 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 4. assume H3: Adj17 11 4.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_5 : Adj17 11 11 -> Adj17 11 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 5. assume H3: Adj17 11 5.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_6 : Adj17 11 11 -> Adj17 11 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 6. assume H3: Adj17 11 6.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_7 : Adj17 11 11 -> Adj17 11 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 7. assume H3: Adj17 11 7.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_8 : Adj17 11 11 -> Adj17 11 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 8. assume H3: Adj17 11 8.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_9 : Adj17 11 11 -> Adj17 11 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 9. assume H3: Adj17 11 9.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_10 : Adj17 11 11 -> Adj17 11 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 10. assume H3: Adj17 11 10.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_11 : Adj17 11 11 -> Adj17 11 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_12 : Adj17 11 11 -> Adj17 11 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 12. assume H3: Adj17 11 12.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_13 : Adj17 11 11 -> Adj17 11 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 13. assume H3: Adj17 11 13.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_14 : Adj17 11 11 -> Adj17 11 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 14. assume H3: Adj17 11 14.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_15 : Adj17 11 11 -> Adj17 11 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 15. assume H3: Adj17 11 15.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_11_16 : Adj17 11 11 -> Adj17 11 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 11. assume H2: Adj17 11 16. assume H3: Adj17 11 16.
exact Adj17_not_11_11 H1.
Qed.

Theorem tf_11_12_0 : Adj17 11 12 -> Adj17 12 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 0. assume H3: Adj17 11 0.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_1 : Adj17 11 12 -> Adj17 12 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 1. assume H3: Adj17 11 1.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_2 : Adj17 11 12 -> Adj17 12 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 2. assume H3: Adj17 11 2.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_3 : Adj17 11 12 -> Adj17 12 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 3. assume H3: Adj17 11 3.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_4 : Adj17 11 12 -> Adj17 12 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 4. assume H3: Adj17 11 4.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_5 : Adj17 11 12 -> Adj17 12 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 5. assume H3: Adj17 11 5.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_6 : Adj17 11 12 -> Adj17 12 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 6. assume H3: Adj17 11 6.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_7 : Adj17 11 12 -> Adj17 12 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 7. assume H3: Adj17 11 7.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_8 : Adj17 11 12 -> Adj17 12 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 8. assume H3: Adj17 11 8.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_9 : Adj17 11 12 -> Adj17 12 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 9. assume H3: Adj17 11 9.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_10 : Adj17 11 12 -> Adj17 12 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 10. assume H3: Adj17 11 10.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_11 : Adj17 11 12 -> Adj17 12 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_12_12 : Adj17 11 12 -> Adj17 12 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 12. assume H3: Adj17 11 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_11_12_13 : Adj17 11 12 -> Adj17 12 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 13. assume H3: Adj17 11 13.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_14 : Adj17 11 12 -> Adj17 12 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 14. assume H3: Adj17 11 14.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_15 : Adj17 11 12 -> Adj17 12 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 15. assume H3: Adj17 11 15.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_12_16 : Adj17 11 12 -> Adj17 12 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 12. assume H2: Adj17 12 16. assume H3: Adj17 11 16.
exact Adj17_not_11_12 H1.
Qed.

Theorem tf_11_13_0 : Adj17 11 13 -> Adj17 13 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 0. assume H3: Adj17 11 0.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_1 : Adj17 11 13 -> Adj17 13 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 1. assume H3: Adj17 11 1.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_2 : Adj17 11 13 -> Adj17 13 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 2. assume H3: Adj17 11 2.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_3 : Adj17 11 13 -> Adj17 13 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 3. assume H3: Adj17 11 3.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_4 : Adj17 11 13 -> Adj17 13 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 4. assume H3: Adj17 11 4.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_5 : Adj17 11 13 -> Adj17 13 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 5. assume H3: Adj17 11 5.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_6 : Adj17 11 13 -> Adj17 13 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 6. assume H3: Adj17 11 6.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_7 : Adj17 11 13 -> Adj17 13 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 7. assume H3: Adj17 11 7.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_8 : Adj17 11 13 -> Adj17 13 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 8. assume H3: Adj17 11 8.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_9 : Adj17 11 13 -> Adj17 13 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 9. assume H3: Adj17 11 9.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_10 : Adj17 11 13 -> Adj17 13 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 10. assume H3: Adj17 11 10.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_11 : Adj17 11 13 -> Adj17 13 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_13_12 : Adj17 11 13 -> Adj17 13 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 12. assume H3: Adj17 11 12.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_13 : Adj17 11 13 -> Adj17 13 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 13. assume H3: Adj17 11 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_11_13_14 : Adj17 11 13 -> Adj17 13 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 14. assume H3: Adj17 11 14.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_15 : Adj17 11 13 -> Adj17 13 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 15. assume H3: Adj17 11 15.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_13_16 : Adj17 11 13 -> Adj17 13 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 13. assume H2: Adj17 13 16. assume H3: Adj17 11 16.
exact Adj17_not_11_13 H1.
Qed.

Theorem tf_11_14_0 : Adj17 11 14 -> Adj17 14 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 0. assume H3: Adj17 11 0.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_1 : Adj17 11 14 -> Adj17 14 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 1. assume H3: Adj17 11 1.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_2 : Adj17 11 14 -> Adj17 14 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 2. assume H3: Adj17 11 2.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_3 : Adj17 11 14 -> Adj17 14 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 3. assume H3: Adj17 11 3.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_4 : Adj17 11 14 -> Adj17 14 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 4. assume H3: Adj17 11 4.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_5 : Adj17 11 14 -> Adj17 14 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 5. assume H3: Adj17 11 5.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_6 : Adj17 11 14 -> Adj17 14 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 6. assume H3: Adj17 11 6.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_7 : Adj17 11 14 -> Adj17 14 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 7. assume H3: Adj17 11 7.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_8 : Adj17 11 14 -> Adj17 14 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 8. assume H3: Adj17 11 8.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_9 : Adj17 11 14 -> Adj17 14 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 9. assume H3: Adj17 11 9.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_10 : Adj17 11 14 -> Adj17 14 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 10. assume H3: Adj17 11 10.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_11 : Adj17 11 14 -> Adj17 14 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_14_12 : Adj17 11 14 -> Adj17 14 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 12. assume H3: Adj17 11 12.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_13 : Adj17 11 14 -> Adj17 14 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 13. assume H3: Adj17 11 13.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_14 : Adj17 11 14 -> Adj17 14 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 14. assume H3: Adj17 11 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_11_14_15 : Adj17 11 14 -> Adj17 14 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 15. assume H3: Adj17 11 15.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_14_16 : Adj17 11 14 -> Adj17 14 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 14. assume H2: Adj17 14 16. assume H3: Adj17 11 16.
exact Adj17_not_11_14 H1.
Qed.

Theorem tf_11_15_0 : Adj17 11 15 -> Adj17 15 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 0. assume H3: Adj17 11 0.
exact Adj17_not_11_0 H3.
Qed.

Theorem tf_11_15_1 : Adj17 11 15 -> Adj17 15 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 1. assume H3: Adj17 11 1.
exact Adj17_not_15_1 H2.
Qed.

Theorem tf_11_15_2 : Adj17 11 15 -> Adj17 15 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 2. assume H3: Adj17 11 2.
exact Adj17_not_11_2 H3.
Qed.

Theorem tf_11_15_3 : Adj17 11 15 -> Adj17 15 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 3. assume H3: Adj17 11 3.
exact Adj17_not_11_3 H3.
Qed.

Theorem tf_11_15_4 : Adj17 11 15 -> Adj17 15 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 4. assume H3: Adj17 11 4.
exact Adj17_not_15_4 H2.
Qed.

Theorem tf_11_15_5 : Adj17 11 15 -> Adj17 15 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 5. assume H3: Adj17 11 5.
exact Adj17_not_15_5 H2.
Qed.

Theorem tf_11_15_6 : Adj17 11 15 -> Adj17 15 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 6. assume H3: Adj17 11 6.
exact Adj17_not_15_6 H2.
Qed.

Theorem tf_11_15_7 : Adj17 11 15 -> Adj17 15 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 7. assume H3: Adj17 11 7.
exact Adj17_not_11_7 H3.
Qed.

Theorem tf_11_15_8 : Adj17 11 15 -> Adj17 15 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 8. assume H3: Adj17 11 8.
exact Adj17_not_15_8 H2.
Qed.

Theorem tf_11_15_9 : Adj17 11 15 -> Adj17 15 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 9. assume H3: Adj17 11 9.
exact Adj17_not_15_9 H2.
Qed.

Theorem tf_11_15_10 : Adj17 11 15 -> Adj17 15 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 10. assume H3: Adj17 11 10.
exact Adj17_not_15_10 H2.
Qed.

Theorem tf_11_15_11 : Adj17 11 15 -> Adj17 15 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_15_12 : Adj17 11 15 -> Adj17 15 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 12. assume H3: Adj17 11 12.
exact Adj17_not_15_12 H2.
Qed.

Theorem tf_11_15_13 : Adj17 11 15 -> Adj17 15 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 13. assume H3: Adj17 11 13.
exact Adj17_not_15_13 H2.
Qed.

Theorem tf_11_15_14 : Adj17 11 15 -> Adj17 15 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 14. assume H3: Adj17 11 14.
exact Adj17_not_15_14 H2.
Qed.

Theorem tf_11_15_15 : Adj17 11 15 -> Adj17 15 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 15. assume H3: Adj17 11 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_11_15_16 : Adj17 11 15 -> Adj17 15 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 15. assume H2: Adj17 15 16. assume H3: Adj17 11 16.
exact Adj17_not_15_16 H2.
Qed.

Theorem tf_11_16_0 : Adj17 11 16 -> Adj17 16 0 -> Adj17 11 0 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 0. assume H3: Adj17 11 0.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_1 : Adj17 11 16 -> Adj17 16 1 -> Adj17 11 1 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 1. assume H3: Adj17 11 1.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_2 : Adj17 11 16 -> Adj17 16 2 -> Adj17 11 2 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 2. assume H3: Adj17 11 2.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_3 : Adj17 11 16 -> Adj17 16 3 -> Adj17 11 3 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 3. assume H3: Adj17 11 3.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_4 : Adj17 11 16 -> Adj17 16 4 -> Adj17 11 4 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 4. assume H3: Adj17 11 4.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_5 : Adj17 11 16 -> Adj17 16 5 -> Adj17 11 5 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 5. assume H3: Adj17 11 5.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_6 : Adj17 11 16 -> Adj17 16 6 -> Adj17 11 6 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 6. assume H3: Adj17 11 6.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_7 : Adj17 11 16 -> Adj17 16 7 -> Adj17 11 7 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 7. assume H3: Adj17 11 7.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_8 : Adj17 11 16 -> Adj17 16 8 -> Adj17 11 8 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 8. assume H3: Adj17 11 8.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_9 : Adj17 11 16 -> Adj17 16 9 -> Adj17 11 9 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 9. assume H3: Adj17 11 9.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_10 : Adj17 11 16 -> Adj17 16 10 -> Adj17 11 10 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 10. assume H3: Adj17 11 10.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_11 : Adj17 11 16 -> Adj17 16 11 -> Adj17 11 11 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 11. assume H3: Adj17 11 11.
exact Adj17_not_11_11 H3.
Qed.

Theorem tf_11_16_12 : Adj17 11 16 -> Adj17 16 12 -> Adj17 11 12 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 12. assume H3: Adj17 11 12.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_13 : Adj17 11 16 -> Adj17 16 13 -> Adj17 11 13 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 13. assume H3: Adj17 11 13.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_14 : Adj17 11 16 -> Adj17 16 14 -> Adj17 11 14 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 14. assume H3: Adj17 11 14.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_15 : Adj17 11 16 -> Adj17 16 15 -> Adj17 11 15 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 15. assume H3: Adj17 11 15.
exact Adj17_not_11_16 H1.
Qed.

Theorem tf_11_16_16 : Adj17 11 16 -> Adj17 16 16 -> Adj17 11 16 -> False.
assume H1: Adj17 11 16. assume H2: Adj17 16 16. assume H3: Adj17 11 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_12_0_0 : Adj17 12 0 -> Adj17 0 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 0. assume H3: Adj17 12 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_12_0_1 : Adj17 12 0 -> Adj17 0 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 1. assume H3: Adj17 12 1.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_2 : Adj17 12 0 -> Adj17 0 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 2. assume H3: Adj17 12 2.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_3 : Adj17 12 0 -> Adj17 0 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 3. assume H3: Adj17 12 3.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_4 : Adj17 12 0 -> Adj17 0 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 4. assume H3: Adj17 12 4.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_5 : Adj17 12 0 -> Adj17 0 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 5. assume H3: Adj17 12 5.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_6 : Adj17 12 0 -> Adj17 0 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 6. assume H3: Adj17 12 6.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_7 : Adj17 12 0 -> Adj17 0 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 7. assume H3: Adj17 12 7.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_8 : Adj17 12 0 -> Adj17 0 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 8. assume H3: Adj17 12 8.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_9 : Adj17 12 0 -> Adj17 0 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 9. assume H3: Adj17 12 9.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_10 : Adj17 12 0 -> Adj17 0 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 10. assume H3: Adj17 12 10.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_11 : Adj17 12 0 -> Adj17 0 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 11. assume H3: Adj17 12 11.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_12 : Adj17 12 0 -> Adj17 0 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_0_13 : Adj17 12 0 -> Adj17 0 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 13. assume H3: Adj17 12 13.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_14 : Adj17 12 0 -> Adj17 0 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 14. assume H3: Adj17 12 14.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_15 : Adj17 12 0 -> Adj17 0 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 15. assume H3: Adj17 12 15.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_0_16 : Adj17 12 0 -> Adj17 0 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 0. assume H2: Adj17 0 16. assume H3: Adj17 12 16.
exact Adj17_not_12_0 H1.
Qed.

Theorem tf_12_1_0 : Adj17 12 1 -> Adj17 1 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 0. assume H3: Adj17 12 0.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_1 : Adj17 12 1 -> Adj17 1 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 1. assume H3: Adj17 12 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_12_1_2 : Adj17 12 1 -> Adj17 1 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 2. assume H3: Adj17 12 2.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_3 : Adj17 12 1 -> Adj17 1 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 3. assume H3: Adj17 12 3.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_4 : Adj17 12 1 -> Adj17 1 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 4. assume H3: Adj17 12 4.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_5 : Adj17 12 1 -> Adj17 1 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 5. assume H3: Adj17 12 5.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_6 : Adj17 12 1 -> Adj17 1 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 6. assume H3: Adj17 12 6.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_7 : Adj17 12 1 -> Adj17 1 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 7. assume H3: Adj17 12 7.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_8 : Adj17 12 1 -> Adj17 1 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 8. assume H3: Adj17 12 8.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_9 : Adj17 12 1 -> Adj17 1 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 9. assume H3: Adj17 12 9.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_10 : Adj17 12 1 -> Adj17 1 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 10. assume H3: Adj17 12 10.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_11 : Adj17 12 1 -> Adj17 1 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 11. assume H3: Adj17 12 11.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_12 : Adj17 12 1 -> Adj17 1 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_1_13 : Adj17 12 1 -> Adj17 1 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 13. assume H3: Adj17 12 13.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_14 : Adj17 12 1 -> Adj17 1 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 14. assume H3: Adj17 12 14.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_15 : Adj17 12 1 -> Adj17 1 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 15. assume H3: Adj17 12 15.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_1_16 : Adj17 12 1 -> Adj17 1 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 1. assume H2: Adj17 1 16. assume H3: Adj17 12 16.
exact Adj17_not_12_1 H1.
Qed.

Theorem tf_12_2_0 : Adj17 12 2 -> Adj17 2 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 0. assume H3: Adj17 12 0.
exact Adj17_not_2_0 H2.
Qed.

Theorem tf_12_2_1 : Adj17 12 2 -> Adj17 2 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 1. assume H3: Adj17 12 1.
exact Adj17_not_2_1 H2.
Qed.

Theorem tf_12_2_2 : Adj17 12 2 -> Adj17 2 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 2. assume H3: Adj17 12 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_12_2_3 : Adj17 12 2 -> Adj17 2 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 3. assume H3: Adj17 12 3.
exact Adj17_not_2_3 H2.
Qed.

Theorem tf_12_2_4 : Adj17 12 2 -> Adj17 2 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 4. assume H3: Adj17 12 4.
exact Adj17_not_2_4 H2.
Qed.

Theorem tf_12_2_5 : Adj17 12 2 -> Adj17 2 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 5. assume H3: Adj17 12 5.
exact Adj17_not_2_5 H2.
Qed.

Theorem tf_12_2_6 : Adj17 12 2 -> Adj17 2 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 6. assume H3: Adj17 12 6.
exact Adj17_not_2_6 H2.
Qed.

Theorem tf_12_2_7 : Adj17 12 2 -> Adj17 2 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 7. assume H3: Adj17 12 7.
exact Adj17_not_2_7 H2.
Qed.

Theorem tf_12_2_8 : Adj17 12 2 -> Adj17 2 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 8. assume H3: Adj17 12 8.
exact Adj17_not_12_8 H3.
Qed.

Theorem tf_12_2_9 : Adj17 12 2 -> Adj17 2 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 9. assume H3: Adj17 12 9.
exact Adj17_not_2_9 H2.
Qed.

Theorem tf_12_2_10 : Adj17 12 2 -> Adj17 2 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 10. assume H3: Adj17 12 10.
exact Adj17_not_12_10 H3.
Qed.

Theorem tf_12_2_11 : Adj17 12 2 -> Adj17 2 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 11. assume H3: Adj17 12 11.
exact Adj17_not_2_11 H2.
Qed.

Theorem tf_12_2_12 : Adj17 12 2 -> Adj17 2 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_2_13 : Adj17 12 2 -> Adj17 2 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 13. assume H3: Adj17 12 13.
exact Adj17_not_2_13 H2.
Qed.

Theorem tf_12_2_14 : Adj17 12 2 -> Adj17 2 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 14. assume H3: Adj17 12 14.
exact Adj17_not_2_14 H2.
Qed.

Theorem tf_12_2_15 : Adj17 12 2 -> Adj17 2 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 15. assume H3: Adj17 12 15.
exact Adj17_not_12_15 H3.
Qed.

Theorem tf_12_2_16 : Adj17 12 2 -> Adj17 2 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 2. assume H2: Adj17 2 16. assume H3: Adj17 12 16.
exact Adj17_not_2_16 H2.
Qed.

Theorem tf_12_3_0 : Adj17 12 3 -> Adj17 3 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 0. assume H3: Adj17 12 0.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_1 : Adj17 12 3 -> Adj17 3 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 1. assume H3: Adj17 12 1.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_2 : Adj17 12 3 -> Adj17 3 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 2. assume H3: Adj17 12 2.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_3 : Adj17 12 3 -> Adj17 3 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 3. assume H3: Adj17 12 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_12_3_4 : Adj17 12 3 -> Adj17 3 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 4. assume H3: Adj17 12 4.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_5 : Adj17 12 3 -> Adj17 3 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 5. assume H3: Adj17 12 5.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_6 : Adj17 12 3 -> Adj17 3 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 6. assume H3: Adj17 12 6.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_7 : Adj17 12 3 -> Adj17 3 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 7. assume H3: Adj17 12 7.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_8 : Adj17 12 3 -> Adj17 3 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 8. assume H3: Adj17 12 8.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_9 : Adj17 12 3 -> Adj17 3 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 9. assume H3: Adj17 12 9.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_10 : Adj17 12 3 -> Adj17 3 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 10. assume H3: Adj17 12 10.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_11 : Adj17 12 3 -> Adj17 3 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 11. assume H3: Adj17 12 11.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_12 : Adj17 12 3 -> Adj17 3 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_3_13 : Adj17 12 3 -> Adj17 3 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 13. assume H3: Adj17 12 13.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_14 : Adj17 12 3 -> Adj17 3 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 14. assume H3: Adj17 12 14.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_15 : Adj17 12 3 -> Adj17 3 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 15. assume H3: Adj17 12 15.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_3_16 : Adj17 12 3 -> Adj17 3 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 3. assume H2: Adj17 3 16. assume H3: Adj17 12 16.
exact Adj17_not_12_3 H1.
Qed.

Theorem tf_12_4_0 : Adj17 12 4 -> Adj17 4 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 0. assume H3: Adj17 12 0.
exact Adj17_not_4_0 H2.
Qed.

Theorem tf_12_4_1 : Adj17 12 4 -> Adj17 4 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 1. assume H3: Adj17 12 1.
exact Adj17_not_4_1 H2.
Qed.

Theorem tf_12_4_2 : Adj17 12 4 -> Adj17 4 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 2. assume H3: Adj17 12 2.
exact Adj17_not_4_2 H2.
Qed.

Theorem tf_12_4_3 : Adj17 12 4 -> Adj17 4 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 3. assume H3: Adj17 12 3.
exact Adj17_not_4_3 H2.
Qed.

Theorem tf_12_4_4 : Adj17 12 4 -> Adj17 4 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 4. assume H3: Adj17 12 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_12_4_5 : Adj17 12 4 -> Adj17 4 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 5. assume H3: Adj17 12 5.
exact Adj17_not_12_5 H3.
Qed.

Theorem tf_12_4_6 : Adj17 12 4 -> Adj17 4 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 6. assume H3: Adj17 12 6.
exact Adj17_not_4_6 H2.
Qed.

Theorem tf_12_4_7 : Adj17 12 4 -> Adj17 4 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 7. assume H3: Adj17 12 7.
exact Adj17_not_12_7 H3.
Qed.

Theorem tf_12_4_8 : Adj17 12 4 -> Adj17 4 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 8. assume H3: Adj17 12 8.
exact Adj17_not_4_8 H2.
Qed.

Theorem tf_12_4_9 : Adj17 12 4 -> Adj17 4 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 9. assume H3: Adj17 12 9.
exact Adj17_not_4_9 H2.
Qed.

Theorem tf_12_4_10 : Adj17 12 4 -> Adj17 4 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 10. assume H3: Adj17 12 10.
exact Adj17_not_4_10 H2.
Qed.

Theorem tf_12_4_11 : Adj17 12 4 -> Adj17 4 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 11. assume H3: Adj17 12 11.
exact Adj17_not_4_11 H2.
Qed.

Theorem tf_12_4_12 : Adj17 12 4 -> Adj17 4 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_4_13 : Adj17 12 4 -> Adj17 4 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 13. assume H3: Adj17 12 13.
exact Adj17_not_4_13 H2.
Qed.

Theorem tf_12_4_14 : Adj17 12 4 -> Adj17 4 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 14. assume H3: Adj17 12 14.
exact Adj17_not_12_14 H3.
Qed.

Theorem tf_12_4_15 : Adj17 12 4 -> Adj17 4 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 15. assume H3: Adj17 12 15.
exact Adj17_not_4_15 H2.
Qed.

Theorem tf_12_4_16 : Adj17 12 4 -> Adj17 4 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 4. assume H2: Adj17 4 16. assume H3: Adj17 12 16.
exact Adj17_not_12_16 H3.
Qed.

Theorem tf_12_5_0 : Adj17 12 5 -> Adj17 5 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 0. assume H3: Adj17 12 0.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_1 : Adj17 12 5 -> Adj17 5 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 1. assume H3: Adj17 12 1.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_2 : Adj17 12 5 -> Adj17 5 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 2. assume H3: Adj17 12 2.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_3 : Adj17 12 5 -> Adj17 5 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 3. assume H3: Adj17 12 3.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_4 : Adj17 12 5 -> Adj17 5 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 4. assume H3: Adj17 12 4.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_5 : Adj17 12 5 -> Adj17 5 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 5. assume H3: Adj17 12 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_12_5_6 : Adj17 12 5 -> Adj17 5 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 6. assume H3: Adj17 12 6.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_7 : Adj17 12 5 -> Adj17 5 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 7. assume H3: Adj17 12 7.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_8 : Adj17 12 5 -> Adj17 5 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 8. assume H3: Adj17 12 8.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_9 : Adj17 12 5 -> Adj17 5 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 9. assume H3: Adj17 12 9.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_10 : Adj17 12 5 -> Adj17 5 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 10. assume H3: Adj17 12 10.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_11 : Adj17 12 5 -> Adj17 5 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 11. assume H3: Adj17 12 11.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_12 : Adj17 12 5 -> Adj17 5 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_5_13 : Adj17 12 5 -> Adj17 5 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 13. assume H3: Adj17 12 13.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_14 : Adj17 12 5 -> Adj17 5 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 14. assume H3: Adj17 12 14.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_15 : Adj17 12 5 -> Adj17 5 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 15. assume H3: Adj17 12 15.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_5_16 : Adj17 12 5 -> Adj17 5 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 5. assume H2: Adj17 5 16. assume H3: Adj17 12 16.
exact Adj17_not_12_5 H1.
Qed.

Theorem tf_12_6_0 : Adj17 12 6 -> Adj17 6 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 0. assume H3: Adj17 12 0.
exact Adj17_not_6_0 H2.
Qed.

Theorem tf_12_6_1 : Adj17 12 6 -> Adj17 6 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 1. assume H3: Adj17 12 1.
exact Adj17_not_6_1 H2.
Qed.

Theorem tf_12_6_2 : Adj17 12 6 -> Adj17 6 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 2. assume H3: Adj17 12 2.
exact Adj17_not_6_2 H2.
Qed.

Theorem tf_12_6_3 : Adj17 12 6 -> Adj17 6 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 3. assume H3: Adj17 12 3.
exact Adj17_not_12_3 H3.
Qed.

Theorem tf_12_6_4 : Adj17 12 6 -> Adj17 6 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 4. assume H3: Adj17 12 4.
exact Adj17_not_6_4 H2.
Qed.

Theorem tf_12_6_5 : Adj17 12 6 -> Adj17 6 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 5. assume H3: Adj17 12 5.
exact Adj17_not_6_5 H2.
Qed.

Theorem tf_12_6_6 : Adj17 12 6 -> Adj17 6 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 6. assume H3: Adj17 12 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_12_6_7 : Adj17 12 6 -> Adj17 6 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 7. assume H3: Adj17 12 7.
exact Adj17_not_6_7 H2.
Qed.

Theorem tf_12_6_8 : Adj17 12 6 -> Adj17 6 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 8. assume H3: Adj17 12 8.
exact Adj17_not_6_8 H2.
Qed.

Theorem tf_12_6_9 : Adj17 12 6 -> Adj17 6 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 9. assume H3: Adj17 12 9.
exact Adj17_not_6_9 H2.
Qed.

Theorem tf_12_6_10 : Adj17 12 6 -> Adj17 6 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 10. assume H3: Adj17 12 10.
exact Adj17_not_12_10 H3.
Qed.

Theorem tf_12_6_11 : Adj17 12 6 -> Adj17 6 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 11. assume H3: Adj17 12 11.
exact Adj17_not_12_11 H3.
Qed.

Theorem tf_12_6_12 : Adj17 12 6 -> Adj17 6 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_6_13 : Adj17 12 6 -> Adj17 6 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 13. assume H3: Adj17 12 13.
exact Adj17_not_6_13 H2.
Qed.

Theorem tf_12_6_14 : Adj17 12 6 -> Adj17 6 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 14. assume H3: Adj17 12 14.
exact Adj17_not_12_14 H3.
Qed.

Theorem tf_12_6_15 : Adj17 12 6 -> Adj17 6 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 15. assume H3: Adj17 12 15.
exact Adj17_not_6_15 H2.
Qed.

Theorem tf_12_6_16 : Adj17 12 6 -> Adj17 6 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 6. assume H2: Adj17 6 16. assume H3: Adj17 12 16.
exact Adj17_not_6_16 H2.
Qed.

Theorem tf_12_7_0 : Adj17 12 7 -> Adj17 7 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 0. assume H3: Adj17 12 0.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_1 : Adj17 12 7 -> Adj17 7 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 1. assume H3: Adj17 12 1.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_2 : Adj17 12 7 -> Adj17 7 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 2. assume H3: Adj17 12 2.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_3 : Adj17 12 7 -> Adj17 7 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 3. assume H3: Adj17 12 3.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_4 : Adj17 12 7 -> Adj17 7 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 4. assume H3: Adj17 12 4.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_5 : Adj17 12 7 -> Adj17 7 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 5. assume H3: Adj17 12 5.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_6 : Adj17 12 7 -> Adj17 7 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 6. assume H3: Adj17 12 6.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_7 : Adj17 12 7 -> Adj17 7 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 7. assume H3: Adj17 12 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_12_7_8 : Adj17 12 7 -> Adj17 7 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 8. assume H3: Adj17 12 8.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_9 : Adj17 12 7 -> Adj17 7 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 9. assume H3: Adj17 12 9.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_10 : Adj17 12 7 -> Adj17 7 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 10. assume H3: Adj17 12 10.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_11 : Adj17 12 7 -> Adj17 7 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 11. assume H3: Adj17 12 11.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_12 : Adj17 12 7 -> Adj17 7 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_7_13 : Adj17 12 7 -> Adj17 7 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 13. assume H3: Adj17 12 13.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_14 : Adj17 12 7 -> Adj17 7 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 14. assume H3: Adj17 12 14.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_15 : Adj17 12 7 -> Adj17 7 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 15. assume H3: Adj17 12 15.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_7_16 : Adj17 12 7 -> Adj17 7 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 7. assume H2: Adj17 7 16. assume H3: Adj17 12 16.
exact Adj17_not_12_7 H1.
Qed.

Theorem tf_12_8_0 : Adj17 12 8 -> Adj17 8 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 0. assume H3: Adj17 12 0.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_1 : Adj17 12 8 -> Adj17 8 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 1. assume H3: Adj17 12 1.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_2 : Adj17 12 8 -> Adj17 8 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 2. assume H3: Adj17 12 2.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_3 : Adj17 12 8 -> Adj17 8 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 3. assume H3: Adj17 12 3.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_4 : Adj17 12 8 -> Adj17 8 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 4. assume H3: Adj17 12 4.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_5 : Adj17 12 8 -> Adj17 8 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 5. assume H3: Adj17 12 5.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_6 : Adj17 12 8 -> Adj17 8 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 6. assume H3: Adj17 12 6.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_7 : Adj17 12 8 -> Adj17 8 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 7. assume H3: Adj17 12 7.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_8 : Adj17 12 8 -> Adj17 8 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 8. assume H3: Adj17 12 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_12_8_9 : Adj17 12 8 -> Adj17 8 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 9. assume H3: Adj17 12 9.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_10 : Adj17 12 8 -> Adj17 8 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 10. assume H3: Adj17 12 10.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_11 : Adj17 12 8 -> Adj17 8 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 11. assume H3: Adj17 12 11.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_12 : Adj17 12 8 -> Adj17 8 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_8_13 : Adj17 12 8 -> Adj17 8 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 13. assume H3: Adj17 12 13.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_14 : Adj17 12 8 -> Adj17 8 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 14. assume H3: Adj17 12 14.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_15 : Adj17 12 8 -> Adj17 8 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 15. assume H3: Adj17 12 15.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_8_16 : Adj17 12 8 -> Adj17 8 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 8. assume H2: Adj17 8 16. assume H3: Adj17 12 16.
exact Adj17_not_12_8 H1.
Qed.

Theorem tf_12_9_0 : Adj17 12 9 -> Adj17 9 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 0. assume H3: Adj17 12 0.
exact Adj17_not_12_0 H3.
Qed.

Theorem tf_12_9_1 : Adj17 12 9 -> Adj17 9 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 1. assume H3: Adj17 12 1.
exact Adj17_not_9_1 H2.
Qed.

Theorem tf_12_9_2 : Adj17 12 9 -> Adj17 9 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 2. assume H3: Adj17 12 2.
exact Adj17_not_9_2 H2.
Qed.

Theorem tf_12_9_3 : Adj17 12 9 -> Adj17 9 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 3. assume H3: Adj17 12 3.
exact Adj17_not_9_3 H2.
Qed.

Theorem tf_12_9_4 : Adj17 12 9 -> Adj17 9 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 4. assume H3: Adj17 12 4.
exact Adj17_not_9_4 H2.
Qed.

Theorem tf_12_9_5 : Adj17 12 9 -> Adj17 9 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 5. assume H3: Adj17 12 5.
exact Adj17_not_12_5 H3.
Qed.

Theorem tf_12_9_6 : Adj17 12 9 -> Adj17 9 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 6. assume H3: Adj17 12 6.
exact Adj17_not_9_6 H2.
Qed.

Theorem tf_12_9_7 : Adj17 12 9 -> Adj17 9 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 7. assume H3: Adj17 12 7.
exact Adj17_not_12_7 H3.
Qed.

Theorem tf_12_9_8 : Adj17 12 9 -> Adj17 9 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 8. assume H3: Adj17 12 8.
exact Adj17_not_12_8 H3.
Qed.

Theorem tf_12_9_9 : Adj17 12 9 -> Adj17 9 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 9. assume H3: Adj17 12 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_12_9_10 : Adj17 12 9 -> Adj17 9 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 10. assume H3: Adj17 12 10.
exact Adj17_not_9_10 H2.
Qed.

Theorem tf_12_9_11 : Adj17 12 9 -> Adj17 9 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 11. assume H3: Adj17 12 11.
exact Adj17_not_9_11 H2.
Qed.

Theorem tf_12_9_12 : Adj17 12 9 -> Adj17 9 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_9_13 : Adj17 12 9 -> Adj17 9 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 13. assume H3: Adj17 12 13.
exact Adj17_not_9_13 H2.
Qed.

Theorem tf_12_9_14 : Adj17 12 9 -> Adj17 9 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 14. assume H3: Adj17 12 14.
exact Adj17_not_9_14 H2.
Qed.

Theorem tf_12_9_15 : Adj17 12 9 -> Adj17 9 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 15. assume H3: Adj17 12 15.
exact Adj17_not_9_15 H2.
Qed.

Theorem tf_12_9_16 : Adj17 12 9 -> Adj17 9 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 9. assume H2: Adj17 9 16. assume H3: Adj17 12 16.
exact Adj17_not_9_16 H2.
Qed.

Theorem tf_12_10_0 : Adj17 12 10 -> Adj17 10 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 0. assume H3: Adj17 12 0.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_1 : Adj17 12 10 -> Adj17 10 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 1. assume H3: Adj17 12 1.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_2 : Adj17 12 10 -> Adj17 10 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 2. assume H3: Adj17 12 2.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_3 : Adj17 12 10 -> Adj17 10 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 3. assume H3: Adj17 12 3.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_4 : Adj17 12 10 -> Adj17 10 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 4. assume H3: Adj17 12 4.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_5 : Adj17 12 10 -> Adj17 10 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 5. assume H3: Adj17 12 5.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_6 : Adj17 12 10 -> Adj17 10 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 6. assume H3: Adj17 12 6.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_7 : Adj17 12 10 -> Adj17 10 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 7. assume H3: Adj17 12 7.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_8 : Adj17 12 10 -> Adj17 10 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 8. assume H3: Adj17 12 8.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_9 : Adj17 12 10 -> Adj17 10 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 9. assume H3: Adj17 12 9.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_10 : Adj17 12 10 -> Adj17 10 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 10. assume H3: Adj17 12 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_12_10_11 : Adj17 12 10 -> Adj17 10 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 11. assume H3: Adj17 12 11.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_12 : Adj17 12 10 -> Adj17 10 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_10_13 : Adj17 12 10 -> Adj17 10 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 13. assume H3: Adj17 12 13.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_14 : Adj17 12 10 -> Adj17 10 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 14. assume H3: Adj17 12 14.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_15 : Adj17 12 10 -> Adj17 10 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 15. assume H3: Adj17 12 15.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_10_16 : Adj17 12 10 -> Adj17 10 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 10. assume H2: Adj17 10 16. assume H3: Adj17 12 16.
exact Adj17_not_12_10 H1.
Qed.

Theorem tf_12_11_0 : Adj17 12 11 -> Adj17 11 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 0. assume H3: Adj17 12 0.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_1 : Adj17 12 11 -> Adj17 11 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 1. assume H3: Adj17 12 1.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_2 : Adj17 12 11 -> Adj17 11 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 2. assume H3: Adj17 12 2.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_3 : Adj17 12 11 -> Adj17 11 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 3. assume H3: Adj17 12 3.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_4 : Adj17 12 11 -> Adj17 11 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 4. assume H3: Adj17 12 4.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_5 : Adj17 12 11 -> Adj17 11 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 5. assume H3: Adj17 12 5.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_6 : Adj17 12 11 -> Adj17 11 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 6. assume H3: Adj17 12 6.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_7 : Adj17 12 11 -> Adj17 11 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 7. assume H3: Adj17 12 7.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_8 : Adj17 12 11 -> Adj17 11 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 8. assume H3: Adj17 12 8.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_9 : Adj17 12 11 -> Adj17 11 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 9. assume H3: Adj17 12 9.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_10 : Adj17 12 11 -> Adj17 11 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 10. assume H3: Adj17 12 10.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_11 : Adj17 12 11 -> Adj17 11 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 11. assume H3: Adj17 12 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_12_11_12 : Adj17 12 11 -> Adj17 11 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_11_13 : Adj17 12 11 -> Adj17 11 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 13. assume H3: Adj17 12 13.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_14 : Adj17 12 11 -> Adj17 11 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 14. assume H3: Adj17 12 14.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_15 : Adj17 12 11 -> Adj17 11 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 15. assume H3: Adj17 12 15.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_11_16 : Adj17 12 11 -> Adj17 11 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 11. assume H2: Adj17 11 16. assume H3: Adj17 12 16.
exact Adj17_not_12_11 H1.
Qed.

Theorem tf_12_12_0 : Adj17 12 12 -> Adj17 12 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 0. assume H3: Adj17 12 0.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_1 : Adj17 12 12 -> Adj17 12 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 1. assume H3: Adj17 12 1.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_2 : Adj17 12 12 -> Adj17 12 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 2. assume H3: Adj17 12 2.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_3 : Adj17 12 12 -> Adj17 12 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 3. assume H3: Adj17 12 3.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_4 : Adj17 12 12 -> Adj17 12 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 4. assume H3: Adj17 12 4.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_5 : Adj17 12 12 -> Adj17 12 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 5. assume H3: Adj17 12 5.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_6 : Adj17 12 12 -> Adj17 12 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 6. assume H3: Adj17 12 6.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_7 : Adj17 12 12 -> Adj17 12 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 7. assume H3: Adj17 12 7.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_8 : Adj17 12 12 -> Adj17 12 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 8. assume H3: Adj17 12 8.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_9 : Adj17 12 12 -> Adj17 12 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 9. assume H3: Adj17 12 9.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_10 : Adj17 12 12 -> Adj17 12 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 10. assume H3: Adj17 12 10.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_11 : Adj17 12 12 -> Adj17 12 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 11. assume H3: Adj17 12 11.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_12 : Adj17 12 12 -> Adj17 12 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_13 : Adj17 12 12 -> Adj17 12 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 13. assume H3: Adj17 12 13.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_14 : Adj17 12 12 -> Adj17 12 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 14. assume H3: Adj17 12 14.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_15 : Adj17 12 12 -> Adj17 12 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 15. assume H3: Adj17 12 15.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_12_16 : Adj17 12 12 -> Adj17 12 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 12. assume H2: Adj17 12 16. assume H3: Adj17 12 16.
exact Adj17_not_12_12 H1.
Qed.

Theorem tf_12_13_0 : Adj17 12 13 -> Adj17 13 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 0. assume H3: Adj17 12 0.
exact Adj17_not_13_0 H2.
Qed.

Theorem tf_12_13_1 : Adj17 12 13 -> Adj17 13 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 1. assume H3: Adj17 12 1.
exact Adj17_not_12_1 H3.
Qed.

Theorem tf_12_13_2 : Adj17 12 13 -> Adj17 13 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 2. assume H3: Adj17 12 2.
exact Adj17_not_13_2 H2.
Qed.

Theorem tf_12_13_3 : Adj17 12 13 -> Adj17 13 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 3. assume H3: Adj17 12 3.
exact Adj17_not_12_3 H3.
Qed.

Theorem tf_12_13_4 : Adj17 12 13 -> Adj17 13 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 4. assume H3: Adj17 12 4.
exact Adj17_not_13_4 H2.
Qed.

Theorem tf_12_13_5 : Adj17 12 13 -> Adj17 13 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 5. assume H3: Adj17 12 5.
exact Adj17_not_12_5 H3.
Qed.

Theorem tf_12_13_6 : Adj17 12 13 -> Adj17 13 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 6. assume H3: Adj17 12 6.
exact Adj17_not_13_6 H2.
Qed.

Theorem tf_12_13_7 : Adj17 12 13 -> Adj17 13 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 7. assume H3: Adj17 12 7.
exact Adj17_not_13_7 H2.
Qed.

Theorem tf_12_13_8 : Adj17 12 13 -> Adj17 13 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 8. assume H3: Adj17 12 8.
exact Adj17_not_13_8 H2.
Qed.

Theorem tf_12_13_9 : Adj17 12 13 -> Adj17 13 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 9. assume H3: Adj17 12 9.
exact Adj17_not_13_9 H2.
Qed.

Theorem tf_12_13_10 : Adj17 12 13 -> Adj17 13 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 10. assume H3: Adj17 12 10.
exact Adj17_not_13_10 H2.
Qed.

Theorem tf_12_13_11 : Adj17 12 13 -> Adj17 13 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 11. assume H3: Adj17 12 11.
exact Adj17_not_13_11 H2.
Qed.

Theorem tf_12_13_12 : Adj17 12 13 -> Adj17 13 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_13_13 : Adj17 12 13 -> Adj17 13 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 13. assume H3: Adj17 12 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_12_13_14 : Adj17 12 13 -> Adj17 13 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 14. assume H3: Adj17 12 14.
exact Adj17_not_12_14 H3.
Qed.

Theorem tf_12_13_15 : Adj17 12 13 -> Adj17 13 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 15. assume H3: Adj17 12 15.
exact Adj17_not_13_15 H2.
Qed.

Theorem tf_12_13_16 : Adj17 12 13 -> Adj17 13 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 13. assume H2: Adj17 13 16. assume H3: Adj17 12 16.
exact Adj17_not_13_16 H2.
Qed.

Theorem tf_12_14_0 : Adj17 12 14 -> Adj17 14 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 0. assume H3: Adj17 12 0.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_1 : Adj17 12 14 -> Adj17 14 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 1. assume H3: Adj17 12 1.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_2 : Adj17 12 14 -> Adj17 14 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 2. assume H3: Adj17 12 2.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_3 : Adj17 12 14 -> Adj17 14 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 3. assume H3: Adj17 12 3.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_4 : Adj17 12 14 -> Adj17 14 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 4. assume H3: Adj17 12 4.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_5 : Adj17 12 14 -> Adj17 14 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 5. assume H3: Adj17 12 5.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_6 : Adj17 12 14 -> Adj17 14 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 6. assume H3: Adj17 12 6.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_7 : Adj17 12 14 -> Adj17 14 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 7. assume H3: Adj17 12 7.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_8 : Adj17 12 14 -> Adj17 14 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 8. assume H3: Adj17 12 8.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_9 : Adj17 12 14 -> Adj17 14 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 9. assume H3: Adj17 12 9.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_10 : Adj17 12 14 -> Adj17 14 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 10. assume H3: Adj17 12 10.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_11 : Adj17 12 14 -> Adj17 14 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 11. assume H3: Adj17 12 11.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_12 : Adj17 12 14 -> Adj17 14 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_14_13 : Adj17 12 14 -> Adj17 14 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 13. assume H3: Adj17 12 13.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_14 : Adj17 12 14 -> Adj17 14 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 14. assume H3: Adj17 12 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_12_14_15 : Adj17 12 14 -> Adj17 14 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 15. assume H3: Adj17 12 15.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_14_16 : Adj17 12 14 -> Adj17 14 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 14. assume H2: Adj17 14 16. assume H3: Adj17 12 16.
exact Adj17_not_12_14 H1.
Qed.

Theorem tf_12_15_0 : Adj17 12 15 -> Adj17 15 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 0. assume H3: Adj17 12 0.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_1 : Adj17 12 15 -> Adj17 15 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 1. assume H3: Adj17 12 1.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_2 : Adj17 12 15 -> Adj17 15 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 2. assume H3: Adj17 12 2.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_3 : Adj17 12 15 -> Adj17 15 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 3. assume H3: Adj17 12 3.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_4 : Adj17 12 15 -> Adj17 15 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 4. assume H3: Adj17 12 4.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_5 : Adj17 12 15 -> Adj17 15 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 5. assume H3: Adj17 12 5.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_6 : Adj17 12 15 -> Adj17 15 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 6. assume H3: Adj17 12 6.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_7 : Adj17 12 15 -> Adj17 15 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 7. assume H3: Adj17 12 7.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_8 : Adj17 12 15 -> Adj17 15 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 8. assume H3: Adj17 12 8.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_9 : Adj17 12 15 -> Adj17 15 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 9. assume H3: Adj17 12 9.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_10 : Adj17 12 15 -> Adj17 15 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 10. assume H3: Adj17 12 10.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_11 : Adj17 12 15 -> Adj17 15 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 11. assume H3: Adj17 12 11.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_12 : Adj17 12 15 -> Adj17 15 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_15_13 : Adj17 12 15 -> Adj17 15 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 13. assume H3: Adj17 12 13.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_14 : Adj17 12 15 -> Adj17 15 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 14. assume H3: Adj17 12 14.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_15_15 : Adj17 12 15 -> Adj17 15 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 15. assume H3: Adj17 12 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_12_15_16 : Adj17 12 15 -> Adj17 15 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 15. assume H2: Adj17 15 16. assume H3: Adj17 12 16.
exact Adj17_not_12_15 H1.
Qed.

Theorem tf_12_16_0 : Adj17 12 16 -> Adj17 16 0 -> Adj17 12 0 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 0. assume H3: Adj17 12 0.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_1 : Adj17 12 16 -> Adj17 16 1 -> Adj17 12 1 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 1. assume H3: Adj17 12 1.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_2 : Adj17 12 16 -> Adj17 16 2 -> Adj17 12 2 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 2. assume H3: Adj17 12 2.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_3 : Adj17 12 16 -> Adj17 16 3 -> Adj17 12 3 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 3. assume H3: Adj17 12 3.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_4 : Adj17 12 16 -> Adj17 16 4 -> Adj17 12 4 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 4. assume H3: Adj17 12 4.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_5 : Adj17 12 16 -> Adj17 16 5 -> Adj17 12 5 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 5. assume H3: Adj17 12 5.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_6 : Adj17 12 16 -> Adj17 16 6 -> Adj17 12 6 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 6. assume H3: Adj17 12 6.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_7 : Adj17 12 16 -> Adj17 16 7 -> Adj17 12 7 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 7. assume H3: Adj17 12 7.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_8 : Adj17 12 16 -> Adj17 16 8 -> Adj17 12 8 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 8. assume H3: Adj17 12 8.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_9 : Adj17 12 16 -> Adj17 16 9 -> Adj17 12 9 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 9. assume H3: Adj17 12 9.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_10 : Adj17 12 16 -> Adj17 16 10 -> Adj17 12 10 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 10. assume H3: Adj17 12 10.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_11 : Adj17 12 16 -> Adj17 16 11 -> Adj17 12 11 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 11. assume H3: Adj17 12 11.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_12 : Adj17 12 16 -> Adj17 16 12 -> Adj17 12 12 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 12. assume H3: Adj17 12 12.
exact Adj17_not_12_12 H3.
Qed.

Theorem tf_12_16_13 : Adj17 12 16 -> Adj17 16 13 -> Adj17 12 13 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 13. assume H3: Adj17 12 13.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_14 : Adj17 12 16 -> Adj17 16 14 -> Adj17 12 14 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 14. assume H3: Adj17 12 14.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_15 : Adj17 12 16 -> Adj17 16 15 -> Adj17 12 15 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 15. assume H3: Adj17 12 15.
exact Adj17_not_12_16 H1.
Qed.

Theorem tf_12_16_16 : Adj17 12 16 -> Adj17 16 16 -> Adj17 12 16 -> False.
assume H1: Adj17 12 16. assume H2: Adj17 16 16. assume H3: Adj17 12 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_13_0_0 : Adj17 13 0 -> Adj17 0 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 0. assume H3: Adj17 13 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_13_0_1 : Adj17 13 0 -> Adj17 0 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 1. assume H3: Adj17 13 1.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_2 : Adj17 13 0 -> Adj17 0 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 2. assume H3: Adj17 13 2.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_3 : Adj17 13 0 -> Adj17 0 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 3. assume H3: Adj17 13 3.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_4 : Adj17 13 0 -> Adj17 0 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 4. assume H3: Adj17 13 4.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_5 : Adj17 13 0 -> Adj17 0 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 5. assume H3: Adj17 13 5.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_6 : Adj17 13 0 -> Adj17 0 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 6. assume H3: Adj17 13 6.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_7 : Adj17 13 0 -> Adj17 0 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 7. assume H3: Adj17 13 7.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_8 : Adj17 13 0 -> Adj17 0 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 8. assume H3: Adj17 13 8.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_9 : Adj17 13 0 -> Adj17 0 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 9. assume H3: Adj17 13 9.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_10 : Adj17 13 0 -> Adj17 0 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 10. assume H3: Adj17 13 10.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_11 : Adj17 13 0 -> Adj17 0 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 11. assume H3: Adj17 13 11.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_12 : Adj17 13 0 -> Adj17 0 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 12. assume H3: Adj17 13 12.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_13 : Adj17 13 0 -> Adj17 0 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_0_14 : Adj17 13 0 -> Adj17 0 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 14. assume H3: Adj17 13 14.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_15 : Adj17 13 0 -> Adj17 0 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 15. assume H3: Adj17 13 15.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_0_16 : Adj17 13 0 -> Adj17 0 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 0. assume H2: Adj17 0 16. assume H3: Adj17 13 16.
exact Adj17_not_13_0 H1.
Qed.

Theorem tf_13_1_0 : Adj17 13 1 -> Adj17 1 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 0. assume H3: Adj17 13 0.
exact Adj17_not_1_0 H2.
Qed.

Theorem tf_13_1_1 : Adj17 13 1 -> Adj17 1 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 1. assume H3: Adj17 13 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_13_1_2 : Adj17 13 1 -> Adj17 1 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 2. assume H3: Adj17 13 2.
exact Adj17_not_1_2 H2.
Qed.

Theorem tf_13_1_3 : Adj17 13 1 -> Adj17 1 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 3. assume H3: Adj17 13 3.
exact Adj17_not_1_3 H2.
Qed.

Theorem tf_13_1_4 : Adj17 13 1 -> Adj17 1 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 4. assume H3: Adj17 13 4.
exact Adj17_not_1_4 H2.
Qed.

Theorem tf_13_1_5 : Adj17 13 1 -> Adj17 1 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 5. assume H3: Adj17 13 5.
exact Adj17_not_1_5 H2.
Qed.

Theorem tf_13_1_6 : Adj17 13 1 -> Adj17 1 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 6. assume H3: Adj17 13 6.
exact Adj17_not_1_6 H2.
Qed.

Theorem tf_13_1_7 : Adj17 13 1 -> Adj17 1 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 7. assume H3: Adj17 13 7.
exact Adj17_not_13_7 H3.
Qed.

Theorem tf_13_1_8 : Adj17 13 1 -> Adj17 1 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 8. assume H3: Adj17 13 8.
exact Adj17_not_1_8 H2.
Qed.

Theorem tf_13_1_9 : Adj17 13 1 -> Adj17 1 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 9. assume H3: Adj17 13 9.
exact Adj17_not_1_9 H2.
Qed.

Theorem tf_13_1_10 : Adj17 13 1 -> Adj17 1 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 10. assume H3: Adj17 13 10.
exact Adj17_not_1_10 H2.
Qed.

Theorem tf_13_1_11 : Adj17 13 1 -> Adj17 1 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 11. assume H3: Adj17 13 11.
exact Adj17_not_13_11 H3.
Qed.

Theorem tf_13_1_12 : Adj17 13 1 -> Adj17 1 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 12. assume H3: Adj17 13 12.
exact Adj17_not_1_12 H2.
Qed.

Theorem tf_13_1_13 : Adj17 13 1 -> Adj17 1 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_1_14 : Adj17 13 1 -> Adj17 1 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 14. assume H3: Adj17 13 14.
exact Adj17_not_1_14 H2.
Qed.

Theorem tf_13_1_15 : Adj17 13 1 -> Adj17 1 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 15. assume H3: Adj17 13 15.
exact Adj17_not_1_15 H2.
Qed.

Theorem tf_13_1_16 : Adj17 13 1 -> Adj17 1 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 1. assume H2: Adj17 1 16. assume H3: Adj17 13 16.
exact Adj17_not_13_16 H3.
Qed.

Theorem tf_13_2_0 : Adj17 13 2 -> Adj17 2 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 0. assume H3: Adj17 13 0.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_1 : Adj17 13 2 -> Adj17 2 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 1. assume H3: Adj17 13 1.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_2 : Adj17 13 2 -> Adj17 2 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 2. assume H3: Adj17 13 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_13_2_3 : Adj17 13 2 -> Adj17 2 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 3. assume H3: Adj17 13 3.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_4 : Adj17 13 2 -> Adj17 2 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 4. assume H3: Adj17 13 4.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_5 : Adj17 13 2 -> Adj17 2 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 5. assume H3: Adj17 13 5.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_6 : Adj17 13 2 -> Adj17 2 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 6. assume H3: Adj17 13 6.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_7 : Adj17 13 2 -> Adj17 2 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 7. assume H3: Adj17 13 7.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_8 : Adj17 13 2 -> Adj17 2 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 8. assume H3: Adj17 13 8.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_9 : Adj17 13 2 -> Adj17 2 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 9. assume H3: Adj17 13 9.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_10 : Adj17 13 2 -> Adj17 2 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 10. assume H3: Adj17 13 10.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_11 : Adj17 13 2 -> Adj17 2 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 11. assume H3: Adj17 13 11.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_12 : Adj17 13 2 -> Adj17 2 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 12. assume H3: Adj17 13 12.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_13 : Adj17 13 2 -> Adj17 2 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_2_14 : Adj17 13 2 -> Adj17 2 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 14. assume H3: Adj17 13 14.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_15 : Adj17 13 2 -> Adj17 2 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 15. assume H3: Adj17 13 15.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_2_16 : Adj17 13 2 -> Adj17 2 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 2. assume H2: Adj17 2 16. assume H3: Adj17 13 16.
exact Adj17_not_13_2 H1.
Qed.

Theorem tf_13_3_0 : Adj17 13 3 -> Adj17 3 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 0. assume H3: Adj17 13 0.
exact Adj17_not_3_0 H2.
Qed.

Theorem tf_13_3_1 : Adj17 13 3 -> Adj17 3 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 1. assume H3: Adj17 13 1.
exact Adj17_not_3_1 H2.
Qed.

Theorem tf_13_3_2 : Adj17 13 3 -> Adj17 3 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 2. assume H3: Adj17 13 2.
exact Adj17_not_3_2 H2.
Qed.

Theorem tf_13_3_3 : Adj17 13 3 -> Adj17 3 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 3. assume H3: Adj17 13 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_13_3_4 : Adj17 13 3 -> Adj17 3 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 4. assume H3: Adj17 13 4.
exact Adj17_not_3_4 H2.
Qed.

Theorem tf_13_3_5 : Adj17 13 3 -> Adj17 3 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 5. assume H3: Adj17 13 5.
exact Adj17_not_3_5 H2.
Qed.

Theorem tf_13_3_6 : Adj17 13 3 -> Adj17 3 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 6. assume H3: Adj17 13 6.
exact Adj17_not_13_6 H3.
Qed.

Theorem tf_13_3_7 : Adj17 13 3 -> Adj17 3 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 7. assume H3: Adj17 13 7.
exact Adj17_not_3_7 H2.
Qed.

Theorem tf_13_3_8 : Adj17 13 3 -> Adj17 3 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 8. assume H3: Adj17 13 8.
exact Adj17_not_13_8 H3.
Qed.

Theorem tf_13_3_9 : Adj17 13 3 -> Adj17 3 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 9. assume H3: Adj17 13 9.
exact Adj17_not_3_9 H2.
Qed.

Theorem tf_13_3_10 : Adj17 13 3 -> Adj17 3 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 10. assume H3: Adj17 13 10.
exact Adj17_not_3_10 H2.
Qed.

Theorem tf_13_3_11 : Adj17 13 3 -> Adj17 3 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 11. assume H3: Adj17 13 11.
exact Adj17_not_3_11 H2.
Qed.

Theorem tf_13_3_12 : Adj17 13 3 -> Adj17 3 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 12. assume H3: Adj17 13 12.
exact Adj17_not_3_12 H2.
Qed.

Theorem tf_13_3_13 : Adj17 13 3 -> Adj17 3 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_3_14 : Adj17 13 3 -> Adj17 3 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 14. assume H3: Adj17 13 14.
exact Adj17_not_3_14 H2.
Qed.

Theorem tf_13_3_15 : Adj17 13 3 -> Adj17 3 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 15. assume H3: Adj17 13 15.
exact Adj17_not_13_15 H3.
Qed.

Theorem tf_13_3_16 : Adj17 13 3 -> Adj17 3 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 3. assume H2: Adj17 3 16. assume H3: Adj17 13 16.
exact Adj17_not_13_16 H3.
Qed.

Theorem tf_13_4_0 : Adj17 13 4 -> Adj17 4 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 0. assume H3: Adj17 13 0.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_1 : Adj17 13 4 -> Adj17 4 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 1. assume H3: Adj17 13 1.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_2 : Adj17 13 4 -> Adj17 4 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 2. assume H3: Adj17 13 2.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_3 : Adj17 13 4 -> Adj17 4 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 3. assume H3: Adj17 13 3.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_4 : Adj17 13 4 -> Adj17 4 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 4. assume H3: Adj17 13 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_13_4_5 : Adj17 13 4 -> Adj17 4 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 5. assume H3: Adj17 13 5.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_6 : Adj17 13 4 -> Adj17 4 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 6. assume H3: Adj17 13 6.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_7 : Adj17 13 4 -> Adj17 4 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 7. assume H3: Adj17 13 7.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_8 : Adj17 13 4 -> Adj17 4 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 8. assume H3: Adj17 13 8.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_9 : Adj17 13 4 -> Adj17 4 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 9. assume H3: Adj17 13 9.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_10 : Adj17 13 4 -> Adj17 4 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 10. assume H3: Adj17 13 10.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_11 : Adj17 13 4 -> Adj17 4 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 11. assume H3: Adj17 13 11.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_12 : Adj17 13 4 -> Adj17 4 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 12. assume H3: Adj17 13 12.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_13 : Adj17 13 4 -> Adj17 4 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_4_14 : Adj17 13 4 -> Adj17 4 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 14. assume H3: Adj17 13 14.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_15 : Adj17 13 4 -> Adj17 4 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 15. assume H3: Adj17 13 15.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_4_16 : Adj17 13 4 -> Adj17 4 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 4. assume H2: Adj17 4 16. assume H3: Adj17 13 16.
exact Adj17_not_13_4 H1.
Qed.

Theorem tf_13_5_0 : Adj17 13 5 -> Adj17 5 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 0. assume H3: Adj17 13 0.
exact Adj17_not_5_0 H2.
Qed.

Theorem tf_13_5_1 : Adj17 13 5 -> Adj17 5 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 1. assume H3: Adj17 13 1.
exact Adj17_not_5_1 H2.
Qed.

Theorem tf_13_5_2 : Adj17 13 5 -> Adj17 5 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 2. assume H3: Adj17 13 2.
exact Adj17_not_5_2 H2.
Qed.

Theorem tf_13_5_3 : Adj17 13 5 -> Adj17 5 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 3. assume H3: Adj17 13 3.
exact Adj17_not_5_3 H2.
Qed.

Theorem tf_13_5_4 : Adj17 13 5 -> Adj17 5 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 4. assume H3: Adj17 13 4.
exact Adj17_not_13_4 H3.
Qed.

Theorem tf_13_5_5 : Adj17 13 5 -> Adj17 5 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 5. assume H3: Adj17 13 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_13_5_6 : Adj17 13 5 -> Adj17 5 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 6. assume H3: Adj17 13 6.
exact Adj17_not_5_6 H2.
Qed.

Theorem tf_13_5_7 : Adj17 13 5 -> Adj17 5 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 7. assume H3: Adj17 13 7.
exact Adj17_not_5_7 H2.
Qed.

Theorem tf_13_5_8 : Adj17 13 5 -> Adj17 5 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 8. assume H3: Adj17 13 8.
exact Adj17_not_5_8 H2.
Qed.

Theorem tf_13_5_9 : Adj17 13 5 -> Adj17 5 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 9. assume H3: Adj17 13 9.
exact Adj17_not_13_9 H3.
Qed.

Theorem tf_13_5_10 : Adj17 13 5 -> Adj17 5 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 10. assume H3: Adj17 13 10.
exact Adj17_not_13_10 H3.
Qed.

Theorem tf_13_5_11 : Adj17 13 5 -> Adj17 5 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 11. assume H3: Adj17 13 11.
exact Adj17_not_13_11 H3.
Qed.

Theorem tf_13_5_12 : Adj17 13 5 -> Adj17 5 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 12. assume H3: Adj17 13 12.
exact Adj17_not_5_12 H2.
Qed.

Theorem tf_13_5_13 : Adj17 13 5 -> Adj17 5 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_5_14 : Adj17 13 5 -> Adj17 5 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 14. assume H3: Adj17 13 14.
exact Adj17_not_5_14 H2.
Qed.

Theorem tf_13_5_15 : Adj17 13 5 -> Adj17 5 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 15. assume H3: Adj17 13 15.
exact Adj17_not_5_15 H2.
Qed.

Theorem tf_13_5_16 : Adj17 13 5 -> Adj17 5 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 5. assume H2: Adj17 5 16. assume H3: Adj17 13 16.
exact Adj17_not_5_16 H2.
Qed.

Theorem tf_13_6_0 : Adj17 13 6 -> Adj17 6 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 0. assume H3: Adj17 13 0.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_1 : Adj17 13 6 -> Adj17 6 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 1. assume H3: Adj17 13 1.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_2 : Adj17 13 6 -> Adj17 6 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 2. assume H3: Adj17 13 2.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_3 : Adj17 13 6 -> Adj17 6 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 3. assume H3: Adj17 13 3.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_4 : Adj17 13 6 -> Adj17 6 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 4. assume H3: Adj17 13 4.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_5 : Adj17 13 6 -> Adj17 6 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 5. assume H3: Adj17 13 5.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_6 : Adj17 13 6 -> Adj17 6 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 6. assume H3: Adj17 13 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_13_6_7 : Adj17 13 6 -> Adj17 6 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 7. assume H3: Adj17 13 7.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_8 : Adj17 13 6 -> Adj17 6 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 8. assume H3: Adj17 13 8.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_9 : Adj17 13 6 -> Adj17 6 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 9. assume H3: Adj17 13 9.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_10 : Adj17 13 6 -> Adj17 6 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 10. assume H3: Adj17 13 10.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_11 : Adj17 13 6 -> Adj17 6 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 11. assume H3: Adj17 13 11.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_12 : Adj17 13 6 -> Adj17 6 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 12. assume H3: Adj17 13 12.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_13 : Adj17 13 6 -> Adj17 6 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_6_14 : Adj17 13 6 -> Adj17 6 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 14. assume H3: Adj17 13 14.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_15 : Adj17 13 6 -> Adj17 6 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 15. assume H3: Adj17 13 15.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_6_16 : Adj17 13 6 -> Adj17 6 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 6. assume H2: Adj17 6 16. assume H3: Adj17 13 16.
exact Adj17_not_13_6 H1.
Qed.

Theorem tf_13_7_0 : Adj17 13 7 -> Adj17 7 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 0. assume H3: Adj17 13 0.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_1 : Adj17 13 7 -> Adj17 7 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 1. assume H3: Adj17 13 1.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_2 : Adj17 13 7 -> Adj17 7 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 2. assume H3: Adj17 13 2.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_3 : Adj17 13 7 -> Adj17 7 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 3. assume H3: Adj17 13 3.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_4 : Adj17 13 7 -> Adj17 7 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 4. assume H3: Adj17 13 4.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_5 : Adj17 13 7 -> Adj17 7 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 5. assume H3: Adj17 13 5.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_6 : Adj17 13 7 -> Adj17 7 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 6. assume H3: Adj17 13 6.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_7 : Adj17 13 7 -> Adj17 7 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 7. assume H3: Adj17 13 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_13_7_8 : Adj17 13 7 -> Adj17 7 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 8. assume H3: Adj17 13 8.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_9 : Adj17 13 7 -> Adj17 7 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 9. assume H3: Adj17 13 9.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_10 : Adj17 13 7 -> Adj17 7 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 10. assume H3: Adj17 13 10.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_11 : Adj17 13 7 -> Adj17 7 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 11. assume H3: Adj17 13 11.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_12 : Adj17 13 7 -> Adj17 7 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 12. assume H3: Adj17 13 12.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_13 : Adj17 13 7 -> Adj17 7 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_7_14 : Adj17 13 7 -> Adj17 7 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 14. assume H3: Adj17 13 14.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_15 : Adj17 13 7 -> Adj17 7 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 15. assume H3: Adj17 13 15.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_7_16 : Adj17 13 7 -> Adj17 7 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 7. assume H2: Adj17 7 16. assume H3: Adj17 13 16.
exact Adj17_not_13_7 H1.
Qed.

Theorem tf_13_8_0 : Adj17 13 8 -> Adj17 8 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 0. assume H3: Adj17 13 0.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_1 : Adj17 13 8 -> Adj17 8 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 1. assume H3: Adj17 13 1.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_2 : Adj17 13 8 -> Adj17 8 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 2. assume H3: Adj17 13 2.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_3 : Adj17 13 8 -> Adj17 8 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 3. assume H3: Adj17 13 3.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_4 : Adj17 13 8 -> Adj17 8 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 4. assume H3: Adj17 13 4.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_5 : Adj17 13 8 -> Adj17 8 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 5. assume H3: Adj17 13 5.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_6 : Adj17 13 8 -> Adj17 8 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 6. assume H3: Adj17 13 6.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_7 : Adj17 13 8 -> Adj17 8 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 7. assume H3: Adj17 13 7.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_8 : Adj17 13 8 -> Adj17 8 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 8. assume H3: Adj17 13 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_13_8_9 : Adj17 13 8 -> Adj17 8 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 9. assume H3: Adj17 13 9.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_10 : Adj17 13 8 -> Adj17 8 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 10. assume H3: Adj17 13 10.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_11 : Adj17 13 8 -> Adj17 8 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 11. assume H3: Adj17 13 11.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_12 : Adj17 13 8 -> Adj17 8 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 12. assume H3: Adj17 13 12.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_13 : Adj17 13 8 -> Adj17 8 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_8_14 : Adj17 13 8 -> Adj17 8 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 14. assume H3: Adj17 13 14.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_15 : Adj17 13 8 -> Adj17 8 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 15. assume H3: Adj17 13 15.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_8_16 : Adj17 13 8 -> Adj17 8 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 8. assume H2: Adj17 8 16. assume H3: Adj17 13 16.
exact Adj17_not_13_8 H1.
Qed.

Theorem tf_13_9_0 : Adj17 13 9 -> Adj17 9 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 0. assume H3: Adj17 13 0.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_1 : Adj17 13 9 -> Adj17 9 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 1. assume H3: Adj17 13 1.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_2 : Adj17 13 9 -> Adj17 9 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 2. assume H3: Adj17 13 2.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_3 : Adj17 13 9 -> Adj17 9 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 3. assume H3: Adj17 13 3.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_4 : Adj17 13 9 -> Adj17 9 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 4. assume H3: Adj17 13 4.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_5 : Adj17 13 9 -> Adj17 9 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 5. assume H3: Adj17 13 5.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_6 : Adj17 13 9 -> Adj17 9 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 6. assume H3: Adj17 13 6.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_7 : Adj17 13 9 -> Adj17 9 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 7. assume H3: Adj17 13 7.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_8 : Adj17 13 9 -> Adj17 9 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 8. assume H3: Adj17 13 8.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_9 : Adj17 13 9 -> Adj17 9 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 9. assume H3: Adj17 13 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_13_9_10 : Adj17 13 9 -> Adj17 9 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 10. assume H3: Adj17 13 10.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_11 : Adj17 13 9 -> Adj17 9 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 11. assume H3: Adj17 13 11.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_12 : Adj17 13 9 -> Adj17 9 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 12. assume H3: Adj17 13 12.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_13 : Adj17 13 9 -> Adj17 9 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_9_14 : Adj17 13 9 -> Adj17 9 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 14. assume H3: Adj17 13 14.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_15 : Adj17 13 9 -> Adj17 9 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 15. assume H3: Adj17 13 15.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_9_16 : Adj17 13 9 -> Adj17 9 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 9. assume H2: Adj17 9 16. assume H3: Adj17 13 16.
exact Adj17_not_13_9 H1.
Qed.

Theorem tf_13_10_0 : Adj17 13 10 -> Adj17 10 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 0. assume H3: Adj17 13 0.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_1 : Adj17 13 10 -> Adj17 10 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 1. assume H3: Adj17 13 1.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_2 : Adj17 13 10 -> Adj17 10 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 2. assume H3: Adj17 13 2.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_3 : Adj17 13 10 -> Adj17 10 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 3. assume H3: Adj17 13 3.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_4 : Adj17 13 10 -> Adj17 10 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 4. assume H3: Adj17 13 4.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_5 : Adj17 13 10 -> Adj17 10 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 5. assume H3: Adj17 13 5.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_6 : Adj17 13 10 -> Adj17 10 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 6. assume H3: Adj17 13 6.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_7 : Adj17 13 10 -> Adj17 10 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 7. assume H3: Adj17 13 7.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_8 : Adj17 13 10 -> Adj17 10 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 8. assume H3: Adj17 13 8.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_9 : Adj17 13 10 -> Adj17 10 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 9. assume H3: Adj17 13 9.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_10 : Adj17 13 10 -> Adj17 10 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 10. assume H3: Adj17 13 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_13_10_11 : Adj17 13 10 -> Adj17 10 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 11. assume H3: Adj17 13 11.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_12 : Adj17 13 10 -> Adj17 10 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 12. assume H3: Adj17 13 12.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_13 : Adj17 13 10 -> Adj17 10 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_10_14 : Adj17 13 10 -> Adj17 10 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 14. assume H3: Adj17 13 14.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_15 : Adj17 13 10 -> Adj17 10 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 15. assume H3: Adj17 13 15.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_10_16 : Adj17 13 10 -> Adj17 10 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 10. assume H2: Adj17 10 16. assume H3: Adj17 13 16.
exact Adj17_not_13_10 H1.
Qed.

Theorem tf_13_11_0 : Adj17 13 11 -> Adj17 11 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 0. assume H3: Adj17 13 0.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_1 : Adj17 13 11 -> Adj17 11 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 1. assume H3: Adj17 13 1.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_2 : Adj17 13 11 -> Adj17 11 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 2. assume H3: Adj17 13 2.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_3 : Adj17 13 11 -> Adj17 11 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 3. assume H3: Adj17 13 3.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_4 : Adj17 13 11 -> Adj17 11 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 4. assume H3: Adj17 13 4.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_5 : Adj17 13 11 -> Adj17 11 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 5. assume H3: Adj17 13 5.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_6 : Adj17 13 11 -> Adj17 11 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 6. assume H3: Adj17 13 6.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_7 : Adj17 13 11 -> Adj17 11 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 7. assume H3: Adj17 13 7.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_8 : Adj17 13 11 -> Adj17 11 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 8. assume H3: Adj17 13 8.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_9 : Adj17 13 11 -> Adj17 11 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 9. assume H3: Adj17 13 9.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_10 : Adj17 13 11 -> Adj17 11 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 10. assume H3: Adj17 13 10.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_11 : Adj17 13 11 -> Adj17 11 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 11. assume H3: Adj17 13 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_13_11_12 : Adj17 13 11 -> Adj17 11 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 12. assume H3: Adj17 13 12.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_13 : Adj17 13 11 -> Adj17 11 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_11_14 : Adj17 13 11 -> Adj17 11 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 14. assume H3: Adj17 13 14.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_15 : Adj17 13 11 -> Adj17 11 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 15. assume H3: Adj17 13 15.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_11_16 : Adj17 13 11 -> Adj17 11 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 11. assume H2: Adj17 11 16. assume H3: Adj17 13 16.
exact Adj17_not_13_11 H1.
Qed.

Theorem tf_13_12_0 : Adj17 13 12 -> Adj17 12 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 0. assume H3: Adj17 13 0.
exact Adj17_not_12_0 H2.
Qed.

Theorem tf_13_12_1 : Adj17 13 12 -> Adj17 12 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 1. assume H3: Adj17 13 1.
exact Adj17_not_12_1 H2.
Qed.

Theorem tf_13_12_2 : Adj17 13 12 -> Adj17 12 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 2. assume H3: Adj17 13 2.
exact Adj17_not_13_2 H3.
Qed.

Theorem tf_13_12_3 : Adj17 13 12 -> Adj17 12 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 3. assume H3: Adj17 13 3.
exact Adj17_not_12_3 H2.
Qed.

Theorem tf_13_12_4 : Adj17 13 12 -> Adj17 12 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 4. assume H3: Adj17 13 4.
exact Adj17_not_13_4 H3.
Qed.

Theorem tf_13_12_5 : Adj17 13 12 -> Adj17 12 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 5. assume H3: Adj17 13 5.
exact Adj17_not_12_5 H2.
Qed.

Theorem tf_13_12_6 : Adj17 13 12 -> Adj17 12 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 6. assume H3: Adj17 13 6.
exact Adj17_not_13_6 H3.
Qed.

Theorem tf_13_12_7 : Adj17 13 12 -> Adj17 12 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 7. assume H3: Adj17 13 7.
exact Adj17_not_12_7 H2.
Qed.

Theorem tf_13_12_8 : Adj17 13 12 -> Adj17 12 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 8. assume H3: Adj17 13 8.
exact Adj17_not_12_8 H2.
Qed.

Theorem tf_13_12_9 : Adj17 13 12 -> Adj17 12 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 9. assume H3: Adj17 13 9.
exact Adj17_not_13_9 H3.
Qed.

Theorem tf_13_12_10 : Adj17 13 12 -> Adj17 12 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 10. assume H3: Adj17 13 10.
exact Adj17_not_12_10 H2.
Qed.

Theorem tf_13_12_11 : Adj17 13 12 -> Adj17 12 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 11. assume H3: Adj17 13 11.
exact Adj17_not_12_11 H2.
Qed.

Theorem tf_13_12_12 : Adj17 13 12 -> Adj17 12 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 12. assume H3: Adj17 13 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_13_12_13 : Adj17 13 12 -> Adj17 12 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_12_14 : Adj17 13 12 -> Adj17 12 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 14. assume H3: Adj17 13 14.
exact Adj17_not_12_14 H2.
Qed.

Theorem tf_13_12_15 : Adj17 13 12 -> Adj17 12 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 15. assume H3: Adj17 13 15.
exact Adj17_not_12_15 H2.
Qed.

Theorem tf_13_12_16 : Adj17 13 12 -> Adj17 12 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 12. assume H2: Adj17 12 16. assume H3: Adj17 13 16.
exact Adj17_not_12_16 H2.
Qed.

Theorem tf_13_13_0 : Adj17 13 13 -> Adj17 13 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 0. assume H3: Adj17 13 0.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_1 : Adj17 13 13 -> Adj17 13 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 1. assume H3: Adj17 13 1.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_2 : Adj17 13 13 -> Adj17 13 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 2. assume H3: Adj17 13 2.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_3 : Adj17 13 13 -> Adj17 13 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 3. assume H3: Adj17 13 3.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_4 : Adj17 13 13 -> Adj17 13 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 4. assume H3: Adj17 13 4.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_5 : Adj17 13 13 -> Adj17 13 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 5. assume H3: Adj17 13 5.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_6 : Adj17 13 13 -> Adj17 13 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 6. assume H3: Adj17 13 6.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_7 : Adj17 13 13 -> Adj17 13 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 7. assume H3: Adj17 13 7.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_8 : Adj17 13 13 -> Adj17 13 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 8. assume H3: Adj17 13 8.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_9 : Adj17 13 13 -> Adj17 13 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 9. assume H3: Adj17 13 9.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_10 : Adj17 13 13 -> Adj17 13 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 10. assume H3: Adj17 13 10.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_11 : Adj17 13 13 -> Adj17 13 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 11. assume H3: Adj17 13 11.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_12 : Adj17 13 13 -> Adj17 13 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 12. assume H3: Adj17 13 12.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_13 : Adj17 13 13 -> Adj17 13 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_14 : Adj17 13 13 -> Adj17 13 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 14. assume H3: Adj17 13 14.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_15 : Adj17 13 13 -> Adj17 13 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 15. assume H3: Adj17 13 15.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_13_16 : Adj17 13 13 -> Adj17 13 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 13. assume H2: Adj17 13 16. assume H3: Adj17 13 16.
exact Adj17_not_13_13 H1.
Qed.

Theorem tf_13_14_0 : Adj17 13 14 -> Adj17 14 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 0. assume H3: Adj17 13 0.
exact Adj17_not_13_0 H3.
Qed.

Theorem tf_13_14_1 : Adj17 13 14 -> Adj17 14 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 1. assume H3: Adj17 13 1.
exact Adj17_not_14_1 H2.
Qed.

Theorem tf_13_14_2 : Adj17 13 14 -> Adj17 14 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 2. assume H3: Adj17 13 2.
exact Adj17_not_14_2 H2.
Qed.

Theorem tf_13_14_3 : Adj17 13 14 -> Adj17 14 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 3. assume H3: Adj17 13 3.
exact Adj17_not_14_3 H2.
Qed.

Theorem tf_13_14_4 : Adj17 13 14 -> Adj17 14 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 4. assume H3: Adj17 13 4.
exact Adj17_not_13_4 H3.
Qed.

Theorem tf_13_14_5 : Adj17 13 14 -> Adj17 14 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 5. assume H3: Adj17 13 5.
exact Adj17_not_14_5 H2.
Qed.

Theorem tf_13_14_6 : Adj17 13 14 -> Adj17 14 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 6. assume H3: Adj17 13 6.
exact Adj17_not_13_6 H3.
Qed.

Theorem tf_13_14_7 : Adj17 13 14 -> Adj17 14 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 7. assume H3: Adj17 13 7.
exact Adj17_not_14_7 H2.
Qed.

Theorem tf_13_14_8 : Adj17 13 14 -> Adj17 14 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 8. assume H3: Adj17 13 8.
exact Adj17_not_13_8 H3.
Qed.

Theorem tf_13_14_9 : Adj17 13 14 -> Adj17 14 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 9. assume H3: Adj17 13 9.
exact Adj17_not_14_9 H2.
Qed.

Theorem tf_13_14_10 : Adj17 13 14 -> Adj17 14 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 10. assume H3: Adj17 13 10.
exact Adj17_not_14_10 H2.
Qed.

Theorem tf_13_14_11 : Adj17 13 14 -> Adj17 14 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 11. assume H3: Adj17 13 11.
exact Adj17_not_14_11 H2.
Qed.

Theorem tf_13_14_12 : Adj17 13 14 -> Adj17 14 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 12. assume H3: Adj17 13 12.
exact Adj17_not_14_12 H2.
Qed.

Theorem tf_13_14_13 : Adj17 13 14 -> Adj17 14 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_14_14 : Adj17 13 14 -> Adj17 14 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 14. assume H3: Adj17 13 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_13_14_15 : Adj17 13 14 -> Adj17 14 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 15. assume H3: Adj17 13 15.
exact Adj17_not_14_15 H2.
Qed.

Theorem tf_13_14_16 : Adj17 13 14 -> Adj17 14 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 14. assume H2: Adj17 14 16. assume H3: Adj17 13 16.
exact Adj17_not_14_16 H2.
Qed.

Theorem tf_13_15_0 : Adj17 13 15 -> Adj17 15 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 0. assume H3: Adj17 13 0.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_1 : Adj17 13 15 -> Adj17 15 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 1. assume H3: Adj17 13 1.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_2 : Adj17 13 15 -> Adj17 15 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 2. assume H3: Adj17 13 2.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_3 : Adj17 13 15 -> Adj17 15 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 3. assume H3: Adj17 13 3.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_4 : Adj17 13 15 -> Adj17 15 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 4. assume H3: Adj17 13 4.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_5 : Adj17 13 15 -> Adj17 15 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 5. assume H3: Adj17 13 5.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_6 : Adj17 13 15 -> Adj17 15 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 6. assume H3: Adj17 13 6.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_7 : Adj17 13 15 -> Adj17 15 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 7. assume H3: Adj17 13 7.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_8 : Adj17 13 15 -> Adj17 15 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 8. assume H3: Adj17 13 8.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_9 : Adj17 13 15 -> Adj17 15 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 9. assume H3: Adj17 13 9.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_10 : Adj17 13 15 -> Adj17 15 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 10. assume H3: Adj17 13 10.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_11 : Adj17 13 15 -> Adj17 15 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 11. assume H3: Adj17 13 11.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_12 : Adj17 13 15 -> Adj17 15 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 12. assume H3: Adj17 13 12.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_13 : Adj17 13 15 -> Adj17 15 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_15_14 : Adj17 13 15 -> Adj17 15 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 14. assume H3: Adj17 13 14.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_15_15 : Adj17 13 15 -> Adj17 15 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 15. assume H3: Adj17 13 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_13_15_16 : Adj17 13 15 -> Adj17 15 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 15. assume H2: Adj17 15 16. assume H3: Adj17 13 16.
exact Adj17_not_13_15 H1.
Qed.

Theorem tf_13_16_0 : Adj17 13 16 -> Adj17 16 0 -> Adj17 13 0 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 0. assume H3: Adj17 13 0.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_1 : Adj17 13 16 -> Adj17 16 1 -> Adj17 13 1 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 1. assume H3: Adj17 13 1.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_2 : Adj17 13 16 -> Adj17 16 2 -> Adj17 13 2 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 2. assume H3: Adj17 13 2.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_3 : Adj17 13 16 -> Adj17 16 3 -> Adj17 13 3 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 3. assume H3: Adj17 13 3.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_4 : Adj17 13 16 -> Adj17 16 4 -> Adj17 13 4 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 4. assume H3: Adj17 13 4.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_5 : Adj17 13 16 -> Adj17 16 5 -> Adj17 13 5 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 5. assume H3: Adj17 13 5.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_6 : Adj17 13 16 -> Adj17 16 6 -> Adj17 13 6 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 6. assume H3: Adj17 13 6.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_7 : Adj17 13 16 -> Adj17 16 7 -> Adj17 13 7 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 7. assume H3: Adj17 13 7.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_8 : Adj17 13 16 -> Adj17 16 8 -> Adj17 13 8 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 8. assume H3: Adj17 13 8.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_9 : Adj17 13 16 -> Adj17 16 9 -> Adj17 13 9 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 9. assume H3: Adj17 13 9.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_10 : Adj17 13 16 -> Adj17 16 10 -> Adj17 13 10 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 10. assume H3: Adj17 13 10.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_11 : Adj17 13 16 -> Adj17 16 11 -> Adj17 13 11 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 11. assume H3: Adj17 13 11.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_12 : Adj17 13 16 -> Adj17 16 12 -> Adj17 13 12 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 12. assume H3: Adj17 13 12.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_13 : Adj17 13 16 -> Adj17 16 13 -> Adj17 13 13 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 13. assume H3: Adj17 13 13.
exact Adj17_not_13_13 H3.
Qed.

Theorem tf_13_16_14 : Adj17 13 16 -> Adj17 16 14 -> Adj17 13 14 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 14. assume H3: Adj17 13 14.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_15 : Adj17 13 16 -> Adj17 16 15 -> Adj17 13 15 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 15. assume H3: Adj17 13 15.
exact Adj17_not_13_16 H1.
Qed.

Theorem tf_13_16_16 : Adj17 13 16 -> Adj17 16 16 -> Adj17 13 16 -> False.
assume H1: Adj17 13 16. assume H2: Adj17 16 16. assume H3: Adj17 13 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_14_0_0 : Adj17 14 0 -> Adj17 0 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 0. assume H3: Adj17 14 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_14_0_1 : Adj17 14 0 -> Adj17 0 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 1. assume H3: Adj17 14 1.
exact Adj17_not_0_1 H2.
Qed.

Theorem tf_14_0_2 : Adj17 14 0 -> Adj17 0 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 2. assume H3: Adj17 14 2.
exact Adj17_not_0_2 H2.
Qed.

Theorem tf_14_0_3 : Adj17 14 0 -> Adj17 0 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 3. assume H3: Adj17 14 3.
exact Adj17_not_0_3 H2.
Qed.

Theorem tf_14_0_4 : Adj17 14 0 -> Adj17 0 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 4. assume H3: Adj17 14 4.
exact Adj17_not_0_4 H2.
Qed.

Theorem tf_14_0_5 : Adj17 14 0 -> Adj17 0 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 5. assume H3: Adj17 14 5.
exact Adj17_not_0_5 H2.
Qed.

Theorem tf_14_0_6 : Adj17 14 0 -> Adj17 0 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 6. assume H3: Adj17 14 6.
exact Adj17_not_0_6 H2.
Qed.

Theorem tf_14_0_7 : Adj17 14 0 -> Adj17 0 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 7. assume H3: Adj17 14 7.
exact Adj17_not_0_7 H2.
Qed.

Theorem tf_14_0_8 : Adj17 14 0 -> Adj17 0 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 8. assume H3: Adj17 14 8.
exact Adj17_not_0_8 H2.
Qed.

Theorem tf_14_0_9 : Adj17 14 0 -> Adj17 0 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 9. assume H3: Adj17 14 9.
exact Adj17_not_14_9 H3.
Qed.

Theorem tf_14_0_10 : Adj17 14 0 -> Adj17 0 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 10. assume H3: Adj17 14 10.
exact Adj17_not_0_10 H2.
Qed.

Theorem tf_14_0_11 : Adj17 14 0 -> Adj17 0 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 11. assume H3: Adj17 14 11.
exact Adj17_not_0_11 H2.
Qed.

Theorem tf_14_0_12 : Adj17 14 0 -> Adj17 0 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 12. assume H3: Adj17 14 12.
exact Adj17_not_0_12 H2.
Qed.

Theorem tf_14_0_13 : Adj17 14 0 -> Adj17 0 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 13. assume H3: Adj17 14 13.
exact Adj17_not_0_13 H2.
Qed.

Theorem tf_14_0_14 : Adj17 14 0 -> Adj17 0 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_0_15 : Adj17 14 0 -> Adj17 0 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 15. assume H3: Adj17 14 15.
exact Adj17_not_14_15 H3.
Qed.

Theorem tf_14_0_16 : Adj17 14 0 -> Adj17 0 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 0. assume H2: Adj17 0 16. assume H3: Adj17 14 16.
exact Adj17_not_14_16 H3.
Qed.

Theorem tf_14_1_0 : Adj17 14 1 -> Adj17 1 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 0. assume H3: Adj17 14 0.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_1 : Adj17 14 1 -> Adj17 1 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 1. assume H3: Adj17 14 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_14_1_2 : Adj17 14 1 -> Adj17 1 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 2. assume H3: Adj17 14 2.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_3 : Adj17 14 1 -> Adj17 1 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 3. assume H3: Adj17 14 3.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_4 : Adj17 14 1 -> Adj17 1 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 4. assume H3: Adj17 14 4.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_5 : Adj17 14 1 -> Adj17 1 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 5. assume H3: Adj17 14 5.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_6 : Adj17 14 1 -> Adj17 1 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 6. assume H3: Adj17 14 6.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_7 : Adj17 14 1 -> Adj17 1 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 7. assume H3: Adj17 14 7.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_8 : Adj17 14 1 -> Adj17 1 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 8. assume H3: Adj17 14 8.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_9 : Adj17 14 1 -> Adj17 1 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 9. assume H3: Adj17 14 9.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_10 : Adj17 14 1 -> Adj17 1 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 10. assume H3: Adj17 14 10.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_11 : Adj17 14 1 -> Adj17 1 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 11. assume H3: Adj17 14 11.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_12 : Adj17 14 1 -> Adj17 1 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 12. assume H3: Adj17 14 12.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_13 : Adj17 14 1 -> Adj17 1 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 13. assume H3: Adj17 14 13.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_14 : Adj17 14 1 -> Adj17 1 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_1_15 : Adj17 14 1 -> Adj17 1 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 15. assume H3: Adj17 14 15.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_1_16 : Adj17 14 1 -> Adj17 1 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 1. assume H2: Adj17 1 16. assume H3: Adj17 14 16.
exact Adj17_not_14_1 H1.
Qed.

Theorem tf_14_2_0 : Adj17 14 2 -> Adj17 2 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 0. assume H3: Adj17 14 0.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_1 : Adj17 14 2 -> Adj17 2 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 1. assume H3: Adj17 14 1.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_2 : Adj17 14 2 -> Adj17 2 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 2. assume H3: Adj17 14 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_14_2_3 : Adj17 14 2 -> Adj17 2 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 3. assume H3: Adj17 14 3.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_4 : Adj17 14 2 -> Adj17 2 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 4. assume H3: Adj17 14 4.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_5 : Adj17 14 2 -> Adj17 2 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 5. assume H3: Adj17 14 5.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_6 : Adj17 14 2 -> Adj17 2 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 6. assume H3: Adj17 14 6.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_7 : Adj17 14 2 -> Adj17 2 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 7. assume H3: Adj17 14 7.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_8 : Adj17 14 2 -> Adj17 2 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 8. assume H3: Adj17 14 8.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_9 : Adj17 14 2 -> Adj17 2 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 9. assume H3: Adj17 14 9.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_10 : Adj17 14 2 -> Adj17 2 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 10. assume H3: Adj17 14 10.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_11 : Adj17 14 2 -> Adj17 2 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 11. assume H3: Adj17 14 11.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_12 : Adj17 14 2 -> Adj17 2 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 12. assume H3: Adj17 14 12.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_13 : Adj17 14 2 -> Adj17 2 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 13. assume H3: Adj17 14 13.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_14 : Adj17 14 2 -> Adj17 2 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_2_15 : Adj17 14 2 -> Adj17 2 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 15. assume H3: Adj17 14 15.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_2_16 : Adj17 14 2 -> Adj17 2 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 2. assume H2: Adj17 2 16. assume H3: Adj17 14 16.
exact Adj17_not_14_2 H1.
Qed.

Theorem tf_14_3_0 : Adj17 14 3 -> Adj17 3 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 0. assume H3: Adj17 14 0.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_1 : Adj17 14 3 -> Adj17 3 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 1. assume H3: Adj17 14 1.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_2 : Adj17 14 3 -> Adj17 3 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 2. assume H3: Adj17 14 2.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_3 : Adj17 14 3 -> Adj17 3 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 3. assume H3: Adj17 14 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_14_3_4 : Adj17 14 3 -> Adj17 3 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 4. assume H3: Adj17 14 4.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_5 : Adj17 14 3 -> Adj17 3 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 5. assume H3: Adj17 14 5.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_6 : Adj17 14 3 -> Adj17 3 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 6. assume H3: Adj17 14 6.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_7 : Adj17 14 3 -> Adj17 3 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 7. assume H3: Adj17 14 7.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_8 : Adj17 14 3 -> Adj17 3 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 8. assume H3: Adj17 14 8.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_9 : Adj17 14 3 -> Adj17 3 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 9. assume H3: Adj17 14 9.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_10 : Adj17 14 3 -> Adj17 3 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 10. assume H3: Adj17 14 10.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_11 : Adj17 14 3 -> Adj17 3 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 11. assume H3: Adj17 14 11.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_12 : Adj17 14 3 -> Adj17 3 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 12. assume H3: Adj17 14 12.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_13 : Adj17 14 3 -> Adj17 3 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 13. assume H3: Adj17 14 13.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_14 : Adj17 14 3 -> Adj17 3 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_3_15 : Adj17 14 3 -> Adj17 3 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 15. assume H3: Adj17 14 15.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_3_16 : Adj17 14 3 -> Adj17 3 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 3. assume H2: Adj17 3 16. assume H3: Adj17 14 16.
exact Adj17_not_14_3 H1.
Qed.

Theorem tf_14_4_0 : Adj17 14 4 -> Adj17 4 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 0. assume H3: Adj17 14 0.
exact Adj17_not_4_0 H2.
Qed.

Theorem tf_14_4_1 : Adj17 14 4 -> Adj17 4 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 1. assume H3: Adj17 14 1.
exact Adj17_not_4_1 H2.
Qed.

Theorem tf_14_4_2 : Adj17 14 4 -> Adj17 4 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 2. assume H3: Adj17 14 2.
exact Adj17_not_4_2 H2.
Qed.

Theorem tf_14_4_3 : Adj17 14 4 -> Adj17 4 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 3. assume H3: Adj17 14 3.
exact Adj17_not_4_3 H2.
Qed.

Theorem tf_14_4_4 : Adj17 14 4 -> Adj17 4 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 4. assume H3: Adj17 14 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_14_4_5 : Adj17 14 4 -> Adj17 4 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 5. assume H3: Adj17 14 5.
exact Adj17_not_14_5 H3.
Qed.

Theorem tf_14_4_6 : Adj17 14 4 -> Adj17 4 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 6. assume H3: Adj17 14 6.
exact Adj17_not_4_6 H2.
Qed.

Theorem tf_14_4_7 : Adj17 14 4 -> Adj17 4 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 7. assume H3: Adj17 14 7.
exact Adj17_not_14_7 H3.
Qed.

Theorem tf_14_4_8 : Adj17 14 4 -> Adj17 4 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 8. assume H3: Adj17 14 8.
exact Adj17_not_4_8 H2.
Qed.

Theorem tf_14_4_9 : Adj17 14 4 -> Adj17 4 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 9. assume H3: Adj17 14 9.
exact Adj17_not_4_9 H2.
Qed.

Theorem tf_14_4_10 : Adj17 14 4 -> Adj17 4 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 10. assume H3: Adj17 14 10.
exact Adj17_not_4_10 H2.
Qed.

Theorem tf_14_4_11 : Adj17 14 4 -> Adj17 4 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 11. assume H3: Adj17 14 11.
exact Adj17_not_4_11 H2.
Qed.

Theorem tf_14_4_12 : Adj17 14 4 -> Adj17 4 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 12. assume H3: Adj17 14 12.
exact Adj17_not_14_12 H3.
Qed.

Theorem tf_14_4_13 : Adj17 14 4 -> Adj17 4 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 13. assume H3: Adj17 14 13.
exact Adj17_not_4_13 H2.
Qed.

Theorem tf_14_4_14 : Adj17 14 4 -> Adj17 4 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_4_15 : Adj17 14 4 -> Adj17 4 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 15. assume H3: Adj17 14 15.
exact Adj17_not_4_15 H2.
Qed.

Theorem tf_14_4_16 : Adj17 14 4 -> Adj17 4 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 4. assume H2: Adj17 4 16. assume H3: Adj17 14 16.
exact Adj17_not_14_16 H3.
Qed.

Theorem tf_14_5_0 : Adj17 14 5 -> Adj17 5 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 0. assume H3: Adj17 14 0.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_1 : Adj17 14 5 -> Adj17 5 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 1. assume H3: Adj17 14 1.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_2 : Adj17 14 5 -> Adj17 5 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 2. assume H3: Adj17 14 2.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_3 : Adj17 14 5 -> Adj17 5 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 3. assume H3: Adj17 14 3.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_4 : Adj17 14 5 -> Adj17 5 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 4. assume H3: Adj17 14 4.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_5 : Adj17 14 5 -> Adj17 5 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 5. assume H3: Adj17 14 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_14_5_6 : Adj17 14 5 -> Adj17 5 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 6. assume H3: Adj17 14 6.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_7 : Adj17 14 5 -> Adj17 5 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 7. assume H3: Adj17 14 7.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_8 : Adj17 14 5 -> Adj17 5 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 8. assume H3: Adj17 14 8.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_9 : Adj17 14 5 -> Adj17 5 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 9. assume H3: Adj17 14 9.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_10 : Adj17 14 5 -> Adj17 5 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 10. assume H3: Adj17 14 10.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_11 : Adj17 14 5 -> Adj17 5 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 11. assume H3: Adj17 14 11.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_12 : Adj17 14 5 -> Adj17 5 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 12. assume H3: Adj17 14 12.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_13 : Adj17 14 5 -> Adj17 5 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 13. assume H3: Adj17 14 13.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_14 : Adj17 14 5 -> Adj17 5 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_5_15 : Adj17 14 5 -> Adj17 5 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 15. assume H3: Adj17 14 15.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_5_16 : Adj17 14 5 -> Adj17 5 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 5. assume H2: Adj17 5 16. assume H3: Adj17 14 16.
exact Adj17_not_14_5 H1.
Qed.

Theorem tf_14_6_0 : Adj17 14 6 -> Adj17 6 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 0. assume H3: Adj17 14 0.
exact Adj17_not_6_0 H2.
Qed.

Theorem tf_14_6_1 : Adj17 14 6 -> Adj17 6 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 1. assume H3: Adj17 14 1.
exact Adj17_not_6_1 H2.
Qed.

Theorem tf_14_6_2 : Adj17 14 6 -> Adj17 6 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 2. assume H3: Adj17 14 2.
exact Adj17_not_6_2 H2.
Qed.

Theorem tf_14_6_3 : Adj17 14 6 -> Adj17 6 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 3. assume H3: Adj17 14 3.
exact Adj17_not_14_3 H3.
Qed.

Theorem tf_14_6_4 : Adj17 14 6 -> Adj17 6 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 4. assume H3: Adj17 14 4.
exact Adj17_not_6_4 H2.
Qed.

Theorem tf_14_6_5 : Adj17 14 6 -> Adj17 6 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 5. assume H3: Adj17 14 5.
exact Adj17_not_6_5 H2.
Qed.

Theorem tf_14_6_6 : Adj17 14 6 -> Adj17 6 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 6. assume H3: Adj17 14 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_14_6_7 : Adj17 14 6 -> Adj17 6 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 7. assume H3: Adj17 14 7.
exact Adj17_not_6_7 H2.
Qed.

Theorem tf_14_6_8 : Adj17 14 6 -> Adj17 6 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 8. assume H3: Adj17 14 8.
exact Adj17_not_6_8 H2.
Qed.

Theorem tf_14_6_9 : Adj17 14 6 -> Adj17 6 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 9. assume H3: Adj17 14 9.
exact Adj17_not_6_9 H2.
Qed.

Theorem tf_14_6_10 : Adj17 14 6 -> Adj17 6 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 10. assume H3: Adj17 14 10.
exact Adj17_not_14_10 H3.
Qed.

Theorem tf_14_6_11 : Adj17 14 6 -> Adj17 6 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 11. assume H3: Adj17 14 11.
exact Adj17_not_14_11 H3.
Qed.

Theorem tf_14_6_12 : Adj17 14 6 -> Adj17 6 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 12. assume H3: Adj17 14 12.
exact Adj17_not_14_12 H3.
Qed.

Theorem tf_14_6_13 : Adj17 14 6 -> Adj17 6 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 13. assume H3: Adj17 14 13.
exact Adj17_not_6_13 H2.
Qed.

Theorem tf_14_6_14 : Adj17 14 6 -> Adj17 6 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_6_15 : Adj17 14 6 -> Adj17 6 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 15. assume H3: Adj17 14 15.
exact Adj17_not_6_15 H2.
Qed.

Theorem tf_14_6_16 : Adj17 14 6 -> Adj17 6 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 6. assume H2: Adj17 6 16. assume H3: Adj17 14 16.
exact Adj17_not_6_16 H2.
Qed.

Theorem tf_14_7_0 : Adj17 14 7 -> Adj17 7 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 0. assume H3: Adj17 14 0.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_1 : Adj17 14 7 -> Adj17 7 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 1. assume H3: Adj17 14 1.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_2 : Adj17 14 7 -> Adj17 7 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 2. assume H3: Adj17 14 2.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_3 : Adj17 14 7 -> Adj17 7 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 3. assume H3: Adj17 14 3.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_4 : Adj17 14 7 -> Adj17 7 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 4. assume H3: Adj17 14 4.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_5 : Adj17 14 7 -> Adj17 7 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 5. assume H3: Adj17 14 5.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_6 : Adj17 14 7 -> Adj17 7 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 6. assume H3: Adj17 14 6.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_7 : Adj17 14 7 -> Adj17 7 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 7. assume H3: Adj17 14 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_14_7_8 : Adj17 14 7 -> Adj17 7 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 8. assume H3: Adj17 14 8.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_9 : Adj17 14 7 -> Adj17 7 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 9. assume H3: Adj17 14 9.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_10 : Adj17 14 7 -> Adj17 7 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 10. assume H3: Adj17 14 10.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_11 : Adj17 14 7 -> Adj17 7 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 11. assume H3: Adj17 14 11.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_12 : Adj17 14 7 -> Adj17 7 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 12. assume H3: Adj17 14 12.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_13 : Adj17 14 7 -> Adj17 7 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 13. assume H3: Adj17 14 13.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_14 : Adj17 14 7 -> Adj17 7 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_7_15 : Adj17 14 7 -> Adj17 7 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 15. assume H3: Adj17 14 15.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_7_16 : Adj17 14 7 -> Adj17 7 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 7. assume H2: Adj17 7 16. assume H3: Adj17 14 16.
exact Adj17_not_14_7 H1.
Qed.

Theorem tf_14_8_0 : Adj17 14 8 -> Adj17 8 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 0. assume H3: Adj17 14 0.
exact Adj17_not_8_0 H2.
Qed.

Theorem tf_14_8_1 : Adj17 14 8 -> Adj17 8 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 1. assume H3: Adj17 14 1.
exact Adj17_not_8_1 H2.
Qed.

Theorem tf_14_8_2 : Adj17 14 8 -> Adj17 8 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 2. assume H3: Adj17 14 2.
exact Adj17_not_14_2 H3.
Qed.

Theorem tf_14_8_3 : Adj17 14 8 -> Adj17 8 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 3. assume H3: Adj17 14 3.
exact Adj17_not_14_3 H3.
Qed.

Theorem tf_14_8_4 : Adj17 14 8 -> Adj17 8 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 4. assume H3: Adj17 14 4.
exact Adj17_not_8_4 H2.
Qed.

Theorem tf_14_8_5 : Adj17 14 8 -> Adj17 8 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 5. assume H3: Adj17 14 5.
exact Adj17_not_8_5 H2.
Qed.

Theorem tf_14_8_6 : Adj17 14 8 -> Adj17 8 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 6. assume H3: Adj17 14 6.
exact Adj17_not_8_6 H2.
Qed.

Theorem tf_14_8_7 : Adj17 14 8 -> Adj17 8 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 7. assume H3: Adj17 14 7.
exact Adj17_not_8_7 H2.
Qed.

Theorem tf_14_8_8 : Adj17 14 8 -> Adj17 8 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 8. assume H3: Adj17 14 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_14_8_9 : Adj17 14 8 -> Adj17 8 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 9. assume H3: Adj17 14 9.
exact Adj17_not_14_9 H3.
Qed.

Theorem tf_14_8_10 : Adj17 14 8 -> Adj17 8 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 10. assume H3: Adj17 14 10.
exact Adj17_not_8_10 H2.
Qed.

Theorem tf_14_8_11 : Adj17 14 8 -> Adj17 8 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 11. assume H3: Adj17 14 11.
exact Adj17_not_14_11 H3.
Qed.

Theorem tf_14_8_12 : Adj17 14 8 -> Adj17 8 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 12. assume H3: Adj17 14 12.
exact Adj17_not_8_12 H2.
Qed.

Theorem tf_14_8_13 : Adj17 14 8 -> Adj17 8 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 13. assume H3: Adj17 14 13.
exact Adj17_not_8_13 H2.
Qed.

Theorem tf_14_8_14 : Adj17 14 8 -> Adj17 8 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_8_15 : Adj17 14 8 -> Adj17 8 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 15. assume H3: Adj17 14 15.
exact Adj17_not_8_15 H2.
Qed.

Theorem tf_14_8_16 : Adj17 14 8 -> Adj17 8 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 8. assume H2: Adj17 8 16. assume H3: Adj17 14 16.
exact Adj17_not_8_16 H2.
Qed.

Theorem tf_14_9_0 : Adj17 14 9 -> Adj17 9 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 0. assume H3: Adj17 14 0.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_1 : Adj17 14 9 -> Adj17 9 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 1. assume H3: Adj17 14 1.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_2 : Adj17 14 9 -> Adj17 9 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 2. assume H3: Adj17 14 2.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_3 : Adj17 14 9 -> Adj17 9 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 3. assume H3: Adj17 14 3.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_4 : Adj17 14 9 -> Adj17 9 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 4. assume H3: Adj17 14 4.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_5 : Adj17 14 9 -> Adj17 9 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 5. assume H3: Adj17 14 5.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_6 : Adj17 14 9 -> Adj17 9 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 6. assume H3: Adj17 14 6.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_7 : Adj17 14 9 -> Adj17 9 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 7. assume H3: Adj17 14 7.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_8 : Adj17 14 9 -> Adj17 9 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 8. assume H3: Adj17 14 8.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_9 : Adj17 14 9 -> Adj17 9 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 9. assume H3: Adj17 14 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_14_9_10 : Adj17 14 9 -> Adj17 9 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 10. assume H3: Adj17 14 10.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_11 : Adj17 14 9 -> Adj17 9 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 11. assume H3: Adj17 14 11.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_12 : Adj17 14 9 -> Adj17 9 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 12. assume H3: Adj17 14 12.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_13 : Adj17 14 9 -> Adj17 9 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 13. assume H3: Adj17 14 13.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_14 : Adj17 14 9 -> Adj17 9 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_9_15 : Adj17 14 9 -> Adj17 9 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 15. assume H3: Adj17 14 15.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_9_16 : Adj17 14 9 -> Adj17 9 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 9. assume H2: Adj17 9 16. assume H3: Adj17 14 16.
exact Adj17_not_14_9 H1.
Qed.

Theorem tf_14_10_0 : Adj17 14 10 -> Adj17 10 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 0. assume H3: Adj17 14 0.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_1 : Adj17 14 10 -> Adj17 10 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 1. assume H3: Adj17 14 1.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_2 : Adj17 14 10 -> Adj17 10 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 2. assume H3: Adj17 14 2.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_3 : Adj17 14 10 -> Adj17 10 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 3. assume H3: Adj17 14 3.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_4 : Adj17 14 10 -> Adj17 10 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 4. assume H3: Adj17 14 4.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_5 : Adj17 14 10 -> Adj17 10 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 5. assume H3: Adj17 14 5.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_6 : Adj17 14 10 -> Adj17 10 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 6. assume H3: Adj17 14 6.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_7 : Adj17 14 10 -> Adj17 10 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 7. assume H3: Adj17 14 7.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_8 : Adj17 14 10 -> Adj17 10 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 8. assume H3: Adj17 14 8.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_9 : Adj17 14 10 -> Adj17 10 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 9. assume H3: Adj17 14 9.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_10 : Adj17 14 10 -> Adj17 10 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 10. assume H3: Adj17 14 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_14_10_11 : Adj17 14 10 -> Adj17 10 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 11. assume H3: Adj17 14 11.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_12 : Adj17 14 10 -> Adj17 10 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 12. assume H3: Adj17 14 12.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_13 : Adj17 14 10 -> Adj17 10 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 13. assume H3: Adj17 14 13.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_14 : Adj17 14 10 -> Adj17 10 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_10_15 : Adj17 14 10 -> Adj17 10 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 15. assume H3: Adj17 14 15.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_10_16 : Adj17 14 10 -> Adj17 10 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 10. assume H2: Adj17 10 16. assume H3: Adj17 14 16.
exact Adj17_not_14_10 H1.
Qed.

Theorem tf_14_11_0 : Adj17 14 11 -> Adj17 11 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 0. assume H3: Adj17 14 0.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_1 : Adj17 14 11 -> Adj17 11 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 1. assume H3: Adj17 14 1.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_2 : Adj17 14 11 -> Adj17 11 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 2. assume H3: Adj17 14 2.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_3 : Adj17 14 11 -> Adj17 11 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 3. assume H3: Adj17 14 3.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_4 : Adj17 14 11 -> Adj17 11 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 4. assume H3: Adj17 14 4.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_5 : Adj17 14 11 -> Adj17 11 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 5. assume H3: Adj17 14 5.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_6 : Adj17 14 11 -> Adj17 11 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 6. assume H3: Adj17 14 6.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_7 : Adj17 14 11 -> Adj17 11 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 7. assume H3: Adj17 14 7.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_8 : Adj17 14 11 -> Adj17 11 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 8. assume H3: Adj17 14 8.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_9 : Adj17 14 11 -> Adj17 11 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 9. assume H3: Adj17 14 9.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_10 : Adj17 14 11 -> Adj17 11 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 10. assume H3: Adj17 14 10.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_11 : Adj17 14 11 -> Adj17 11 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 11. assume H3: Adj17 14 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_14_11_12 : Adj17 14 11 -> Adj17 11 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 12. assume H3: Adj17 14 12.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_13 : Adj17 14 11 -> Adj17 11 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 13. assume H3: Adj17 14 13.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_14 : Adj17 14 11 -> Adj17 11 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_11_15 : Adj17 14 11 -> Adj17 11 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 15. assume H3: Adj17 14 15.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_11_16 : Adj17 14 11 -> Adj17 11 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 11. assume H2: Adj17 11 16. assume H3: Adj17 14 16.
exact Adj17_not_14_11 H1.
Qed.

Theorem tf_14_12_0 : Adj17 14 12 -> Adj17 12 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 0. assume H3: Adj17 14 0.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_1 : Adj17 14 12 -> Adj17 12 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 1. assume H3: Adj17 14 1.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_2 : Adj17 14 12 -> Adj17 12 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 2. assume H3: Adj17 14 2.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_3 : Adj17 14 12 -> Adj17 12 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 3. assume H3: Adj17 14 3.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_4 : Adj17 14 12 -> Adj17 12 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 4. assume H3: Adj17 14 4.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_5 : Adj17 14 12 -> Adj17 12 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 5. assume H3: Adj17 14 5.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_6 : Adj17 14 12 -> Adj17 12 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 6. assume H3: Adj17 14 6.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_7 : Adj17 14 12 -> Adj17 12 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 7. assume H3: Adj17 14 7.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_8 : Adj17 14 12 -> Adj17 12 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 8. assume H3: Adj17 14 8.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_9 : Adj17 14 12 -> Adj17 12 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 9. assume H3: Adj17 14 9.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_10 : Adj17 14 12 -> Adj17 12 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 10. assume H3: Adj17 14 10.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_11 : Adj17 14 12 -> Adj17 12 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 11. assume H3: Adj17 14 11.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_12 : Adj17 14 12 -> Adj17 12 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 12. assume H3: Adj17 14 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_14_12_13 : Adj17 14 12 -> Adj17 12 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 13. assume H3: Adj17 14 13.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_14 : Adj17 14 12 -> Adj17 12 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_12_15 : Adj17 14 12 -> Adj17 12 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 15. assume H3: Adj17 14 15.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_12_16 : Adj17 14 12 -> Adj17 12 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 12. assume H2: Adj17 12 16. assume H3: Adj17 14 16.
exact Adj17_not_14_12 H1.
Qed.

Theorem tf_14_13_0 : Adj17 14 13 -> Adj17 13 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 0. assume H3: Adj17 14 0.
exact Adj17_not_13_0 H2.
Qed.

Theorem tf_14_13_1 : Adj17 14 13 -> Adj17 13 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 1. assume H3: Adj17 14 1.
exact Adj17_not_14_1 H3.
Qed.

Theorem tf_14_13_2 : Adj17 14 13 -> Adj17 13 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 2. assume H3: Adj17 14 2.
exact Adj17_not_13_2 H2.
Qed.

Theorem tf_14_13_3 : Adj17 14 13 -> Adj17 13 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 3. assume H3: Adj17 14 3.
exact Adj17_not_14_3 H3.
Qed.

Theorem tf_14_13_4 : Adj17 14 13 -> Adj17 13 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 4. assume H3: Adj17 14 4.
exact Adj17_not_13_4 H2.
Qed.

Theorem tf_14_13_5 : Adj17 14 13 -> Adj17 13 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 5. assume H3: Adj17 14 5.
exact Adj17_not_14_5 H3.
Qed.

Theorem tf_14_13_6 : Adj17 14 13 -> Adj17 13 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 6. assume H3: Adj17 14 6.
exact Adj17_not_13_6 H2.
Qed.

Theorem tf_14_13_7 : Adj17 14 13 -> Adj17 13 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 7. assume H3: Adj17 14 7.
exact Adj17_not_13_7 H2.
Qed.

Theorem tf_14_13_8 : Adj17 14 13 -> Adj17 13 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 8. assume H3: Adj17 14 8.
exact Adj17_not_13_8 H2.
Qed.

Theorem tf_14_13_9 : Adj17 14 13 -> Adj17 13 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 9. assume H3: Adj17 14 9.
exact Adj17_not_13_9 H2.
Qed.

Theorem tf_14_13_10 : Adj17 14 13 -> Adj17 13 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 10. assume H3: Adj17 14 10.
exact Adj17_not_13_10 H2.
Qed.

Theorem tf_14_13_11 : Adj17 14 13 -> Adj17 13 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 11. assume H3: Adj17 14 11.
exact Adj17_not_13_11 H2.
Qed.

Theorem tf_14_13_12 : Adj17 14 13 -> Adj17 13 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 12. assume H3: Adj17 14 12.
exact Adj17_not_14_12 H3.
Qed.

Theorem tf_14_13_13 : Adj17 14 13 -> Adj17 13 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 13. assume H3: Adj17 14 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_14_13_14 : Adj17 14 13 -> Adj17 13 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_13_15 : Adj17 14 13 -> Adj17 13 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 15. assume H3: Adj17 14 15.
exact Adj17_not_13_15 H2.
Qed.

Theorem tf_14_13_16 : Adj17 14 13 -> Adj17 13 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 13. assume H2: Adj17 13 16. assume H3: Adj17 14 16.
exact Adj17_not_13_16 H2.
Qed.

Theorem tf_14_14_0 : Adj17 14 14 -> Adj17 14 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 0. assume H3: Adj17 14 0.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_1 : Adj17 14 14 -> Adj17 14 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 1. assume H3: Adj17 14 1.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_2 : Adj17 14 14 -> Adj17 14 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 2. assume H3: Adj17 14 2.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_3 : Adj17 14 14 -> Adj17 14 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 3. assume H3: Adj17 14 3.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_4 : Adj17 14 14 -> Adj17 14 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 4. assume H3: Adj17 14 4.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_5 : Adj17 14 14 -> Adj17 14 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 5. assume H3: Adj17 14 5.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_6 : Adj17 14 14 -> Adj17 14 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 6. assume H3: Adj17 14 6.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_7 : Adj17 14 14 -> Adj17 14 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 7. assume H3: Adj17 14 7.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_8 : Adj17 14 14 -> Adj17 14 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 8. assume H3: Adj17 14 8.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_9 : Adj17 14 14 -> Adj17 14 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 9. assume H3: Adj17 14 9.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_10 : Adj17 14 14 -> Adj17 14 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 10. assume H3: Adj17 14 10.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_11 : Adj17 14 14 -> Adj17 14 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 11. assume H3: Adj17 14 11.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_12 : Adj17 14 14 -> Adj17 14 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 12. assume H3: Adj17 14 12.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_13 : Adj17 14 14 -> Adj17 14 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 13. assume H3: Adj17 14 13.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_14 : Adj17 14 14 -> Adj17 14 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_15 : Adj17 14 14 -> Adj17 14 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 15. assume H3: Adj17 14 15.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_14_16 : Adj17 14 14 -> Adj17 14 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 14. assume H2: Adj17 14 16. assume H3: Adj17 14 16.
exact Adj17_not_14_14 H1.
Qed.

Theorem tf_14_15_0 : Adj17 14 15 -> Adj17 15 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 0. assume H3: Adj17 14 0.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_1 : Adj17 14 15 -> Adj17 15 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 1. assume H3: Adj17 14 1.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_2 : Adj17 14 15 -> Adj17 15 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 2. assume H3: Adj17 14 2.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_3 : Adj17 14 15 -> Adj17 15 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 3. assume H3: Adj17 14 3.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_4 : Adj17 14 15 -> Adj17 15 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 4. assume H3: Adj17 14 4.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_5 : Adj17 14 15 -> Adj17 15 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 5. assume H3: Adj17 14 5.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_6 : Adj17 14 15 -> Adj17 15 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 6. assume H3: Adj17 14 6.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_7 : Adj17 14 15 -> Adj17 15 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 7. assume H3: Adj17 14 7.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_8 : Adj17 14 15 -> Adj17 15 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 8. assume H3: Adj17 14 8.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_9 : Adj17 14 15 -> Adj17 15 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 9. assume H3: Adj17 14 9.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_10 : Adj17 14 15 -> Adj17 15 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 10. assume H3: Adj17 14 10.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_11 : Adj17 14 15 -> Adj17 15 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 11. assume H3: Adj17 14 11.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_12 : Adj17 14 15 -> Adj17 15 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 12. assume H3: Adj17 14 12.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_13 : Adj17 14 15 -> Adj17 15 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 13. assume H3: Adj17 14 13.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_15_14 : Adj17 14 15 -> Adj17 15 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_15_15 : Adj17 14 15 -> Adj17 15 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 15. assume H3: Adj17 14 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_14_15_16 : Adj17 14 15 -> Adj17 15 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 15. assume H2: Adj17 15 16. assume H3: Adj17 14 16.
exact Adj17_not_14_15 H1.
Qed.

Theorem tf_14_16_0 : Adj17 14 16 -> Adj17 16 0 -> Adj17 14 0 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 0. assume H3: Adj17 14 0.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_1 : Adj17 14 16 -> Adj17 16 1 -> Adj17 14 1 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 1. assume H3: Adj17 14 1.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_2 : Adj17 14 16 -> Adj17 16 2 -> Adj17 14 2 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 2. assume H3: Adj17 14 2.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_3 : Adj17 14 16 -> Adj17 16 3 -> Adj17 14 3 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 3. assume H3: Adj17 14 3.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_4 : Adj17 14 16 -> Adj17 16 4 -> Adj17 14 4 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 4. assume H3: Adj17 14 4.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_5 : Adj17 14 16 -> Adj17 16 5 -> Adj17 14 5 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 5. assume H3: Adj17 14 5.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_6 : Adj17 14 16 -> Adj17 16 6 -> Adj17 14 6 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 6. assume H3: Adj17 14 6.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_7 : Adj17 14 16 -> Adj17 16 7 -> Adj17 14 7 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 7. assume H3: Adj17 14 7.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_8 : Adj17 14 16 -> Adj17 16 8 -> Adj17 14 8 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 8. assume H3: Adj17 14 8.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_9 : Adj17 14 16 -> Adj17 16 9 -> Adj17 14 9 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 9. assume H3: Adj17 14 9.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_10 : Adj17 14 16 -> Adj17 16 10 -> Adj17 14 10 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 10. assume H3: Adj17 14 10.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_11 : Adj17 14 16 -> Adj17 16 11 -> Adj17 14 11 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 11. assume H3: Adj17 14 11.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_12 : Adj17 14 16 -> Adj17 16 12 -> Adj17 14 12 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 12. assume H3: Adj17 14 12.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_13 : Adj17 14 16 -> Adj17 16 13 -> Adj17 14 13 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 13. assume H3: Adj17 14 13.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_14 : Adj17 14 16 -> Adj17 16 14 -> Adj17 14 14 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 14. assume H3: Adj17 14 14.
exact Adj17_not_14_14 H3.
Qed.

Theorem tf_14_16_15 : Adj17 14 16 -> Adj17 16 15 -> Adj17 14 15 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 15. assume H3: Adj17 14 15.
exact Adj17_not_14_16 H1.
Qed.

Theorem tf_14_16_16 : Adj17 14 16 -> Adj17 16 16 -> Adj17 14 16 -> False.
assume H1: Adj17 14 16. assume H2: Adj17 16 16. assume H3: Adj17 14 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_15_0_0 : Adj17 15 0 -> Adj17 0 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 0. assume H3: Adj17 15 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_15_0_1 : Adj17 15 0 -> Adj17 0 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 1. assume H3: Adj17 15 1.
exact Adj17_not_0_1 H2.
Qed.

Theorem tf_15_0_2 : Adj17 15 0 -> Adj17 0 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 2. assume H3: Adj17 15 2.
exact Adj17_not_0_2 H2.
Qed.

Theorem tf_15_0_3 : Adj17 15 0 -> Adj17 0 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 3. assume H3: Adj17 15 3.
exact Adj17_not_0_3 H2.
Qed.

Theorem tf_15_0_4 : Adj17 15 0 -> Adj17 0 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 4. assume H3: Adj17 15 4.
exact Adj17_not_0_4 H2.
Qed.

Theorem tf_15_0_5 : Adj17 15 0 -> Adj17 0 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 5. assume H3: Adj17 15 5.
exact Adj17_not_0_5 H2.
Qed.

Theorem tf_15_0_6 : Adj17 15 0 -> Adj17 0 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 6. assume H3: Adj17 15 6.
exact Adj17_not_0_6 H2.
Qed.

Theorem tf_15_0_7 : Adj17 15 0 -> Adj17 0 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 7. assume H3: Adj17 15 7.
exact Adj17_not_0_7 H2.
Qed.

Theorem tf_15_0_8 : Adj17 15 0 -> Adj17 0 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 8. assume H3: Adj17 15 8.
exact Adj17_not_0_8 H2.
Qed.

Theorem tf_15_0_9 : Adj17 15 0 -> Adj17 0 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 9. assume H3: Adj17 15 9.
exact Adj17_not_15_9 H3.
Qed.

Theorem tf_15_0_10 : Adj17 15 0 -> Adj17 0 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 10. assume H3: Adj17 15 10.
exact Adj17_not_0_10 H2.
Qed.

Theorem tf_15_0_11 : Adj17 15 0 -> Adj17 0 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 11. assume H3: Adj17 15 11.
exact Adj17_not_0_11 H2.
Qed.

Theorem tf_15_0_12 : Adj17 15 0 -> Adj17 0 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 12. assume H3: Adj17 15 12.
exact Adj17_not_0_12 H2.
Qed.

Theorem tf_15_0_13 : Adj17 15 0 -> Adj17 0 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 13. assume H3: Adj17 15 13.
exact Adj17_not_0_13 H2.
Qed.

Theorem tf_15_0_14 : Adj17 15 0 -> Adj17 0 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 14. assume H3: Adj17 15 14.
exact Adj17_not_15_14 H3.
Qed.

Theorem tf_15_0_15 : Adj17 15 0 -> Adj17 0 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_0_16 : Adj17 15 0 -> Adj17 0 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 0. assume H2: Adj17 0 16. assume H3: Adj17 15 16.
exact Adj17_not_15_16 H3.
Qed.

Theorem tf_15_1_0 : Adj17 15 1 -> Adj17 1 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 0. assume H3: Adj17 15 0.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_1 : Adj17 15 1 -> Adj17 1 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 1. assume H3: Adj17 15 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_15_1_2 : Adj17 15 1 -> Adj17 1 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 2. assume H3: Adj17 15 2.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_3 : Adj17 15 1 -> Adj17 1 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 3. assume H3: Adj17 15 3.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_4 : Adj17 15 1 -> Adj17 1 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 4. assume H3: Adj17 15 4.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_5 : Adj17 15 1 -> Adj17 1 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 5. assume H3: Adj17 15 5.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_6 : Adj17 15 1 -> Adj17 1 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 6. assume H3: Adj17 15 6.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_7 : Adj17 15 1 -> Adj17 1 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 7. assume H3: Adj17 15 7.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_8 : Adj17 15 1 -> Adj17 1 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 8. assume H3: Adj17 15 8.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_9 : Adj17 15 1 -> Adj17 1 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 9. assume H3: Adj17 15 9.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_10 : Adj17 15 1 -> Adj17 1 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 10. assume H3: Adj17 15 10.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_11 : Adj17 15 1 -> Adj17 1 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 11. assume H3: Adj17 15 11.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_12 : Adj17 15 1 -> Adj17 1 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 12. assume H3: Adj17 15 12.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_13 : Adj17 15 1 -> Adj17 1 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 13. assume H3: Adj17 15 13.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_14 : Adj17 15 1 -> Adj17 1 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 14. assume H3: Adj17 15 14.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_1_15 : Adj17 15 1 -> Adj17 1 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_1_16 : Adj17 15 1 -> Adj17 1 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 1. assume H2: Adj17 1 16. assume H3: Adj17 15 16.
exact Adj17_not_15_1 H1.
Qed.

Theorem tf_15_2_0 : Adj17 15 2 -> Adj17 2 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 0. assume H3: Adj17 15 0.
exact Adj17_not_2_0 H2.
Qed.

Theorem tf_15_2_1 : Adj17 15 2 -> Adj17 2 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 1. assume H3: Adj17 15 1.
exact Adj17_not_2_1 H2.
Qed.

Theorem tf_15_2_2 : Adj17 15 2 -> Adj17 2 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 2. assume H3: Adj17 15 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_15_2_3 : Adj17 15 2 -> Adj17 2 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 3. assume H3: Adj17 15 3.
exact Adj17_not_2_3 H2.
Qed.

Theorem tf_15_2_4 : Adj17 15 2 -> Adj17 2 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 4. assume H3: Adj17 15 4.
exact Adj17_not_2_4 H2.
Qed.

Theorem tf_15_2_5 : Adj17 15 2 -> Adj17 2 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 5. assume H3: Adj17 15 5.
exact Adj17_not_2_5 H2.
Qed.

Theorem tf_15_2_6 : Adj17 15 2 -> Adj17 2 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 6. assume H3: Adj17 15 6.
exact Adj17_not_2_6 H2.
Qed.

Theorem tf_15_2_7 : Adj17 15 2 -> Adj17 2 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 7. assume H3: Adj17 15 7.
exact Adj17_not_2_7 H2.
Qed.

Theorem tf_15_2_8 : Adj17 15 2 -> Adj17 2 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 8. assume H3: Adj17 15 8.
exact Adj17_not_15_8 H3.
Qed.

Theorem tf_15_2_9 : Adj17 15 2 -> Adj17 2 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 9. assume H3: Adj17 15 9.
exact Adj17_not_2_9 H2.
Qed.

Theorem tf_15_2_10 : Adj17 15 2 -> Adj17 2 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 10. assume H3: Adj17 15 10.
exact Adj17_not_15_10 H3.
Qed.

Theorem tf_15_2_11 : Adj17 15 2 -> Adj17 2 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 11. assume H3: Adj17 15 11.
exact Adj17_not_2_11 H2.
Qed.

Theorem tf_15_2_12 : Adj17 15 2 -> Adj17 2 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 12. assume H3: Adj17 15 12.
exact Adj17_not_15_12 H3.
Qed.

Theorem tf_15_2_13 : Adj17 15 2 -> Adj17 2 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 13. assume H3: Adj17 15 13.
exact Adj17_not_2_13 H2.
Qed.

Theorem tf_15_2_14 : Adj17 15 2 -> Adj17 2 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 14. assume H3: Adj17 15 14.
exact Adj17_not_2_14 H2.
Qed.

Theorem tf_15_2_15 : Adj17 15 2 -> Adj17 2 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_2_16 : Adj17 15 2 -> Adj17 2 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 2. assume H2: Adj17 2 16. assume H3: Adj17 15 16.
exact Adj17_not_2_16 H2.
Qed.

Theorem tf_15_3_0 : Adj17 15 3 -> Adj17 3 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 0. assume H3: Adj17 15 0.
exact Adj17_not_3_0 H2.
Qed.

Theorem tf_15_3_1 : Adj17 15 3 -> Adj17 3 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 1. assume H3: Adj17 15 1.
exact Adj17_not_3_1 H2.
Qed.

Theorem tf_15_3_2 : Adj17 15 3 -> Adj17 3 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 2. assume H3: Adj17 15 2.
exact Adj17_not_3_2 H2.
Qed.

Theorem tf_15_3_3 : Adj17 15 3 -> Adj17 3 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 3. assume H3: Adj17 15 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_15_3_4 : Adj17 15 3 -> Adj17 3 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 4. assume H3: Adj17 15 4.
exact Adj17_not_3_4 H2.
Qed.

Theorem tf_15_3_5 : Adj17 15 3 -> Adj17 3 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 5. assume H3: Adj17 15 5.
exact Adj17_not_3_5 H2.
Qed.

Theorem tf_15_3_6 : Adj17 15 3 -> Adj17 3 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 6. assume H3: Adj17 15 6.
exact Adj17_not_15_6 H3.
Qed.

Theorem tf_15_3_7 : Adj17 15 3 -> Adj17 3 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 7. assume H3: Adj17 15 7.
exact Adj17_not_3_7 H2.
Qed.

Theorem tf_15_3_8 : Adj17 15 3 -> Adj17 3 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 8. assume H3: Adj17 15 8.
exact Adj17_not_15_8 H3.
Qed.

Theorem tf_15_3_9 : Adj17 15 3 -> Adj17 3 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 9. assume H3: Adj17 15 9.
exact Adj17_not_3_9 H2.
Qed.

Theorem tf_15_3_10 : Adj17 15 3 -> Adj17 3 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 10. assume H3: Adj17 15 10.
exact Adj17_not_3_10 H2.
Qed.

Theorem tf_15_3_11 : Adj17 15 3 -> Adj17 3 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 11. assume H3: Adj17 15 11.
exact Adj17_not_3_11 H2.
Qed.

Theorem tf_15_3_12 : Adj17 15 3 -> Adj17 3 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 12. assume H3: Adj17 15 12.
exact Adj17_not_3_12 H2.
Qed.

Theorem tf_15_3_13 : Adj17 15 3 -> Adj17 3 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 13. assume H3: Adj17 15 13.
exact Adj17_not_15_13 H3.
Qed.

Theorem tf_15_3_14 : Adj17 15 3 -> Adj17 3 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 14. assume H3: Adj17 15 14.
exact Adj17_not_3_14 H2.
Qed.

Theorem tf_15_3_15 : Adj17 15 3 -> Adj17 3 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_3_16 : Adj17 15 3 -> Adj17 3 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 3. assume H2: Adj17 3 16. assume H3: Adj17 15 16.
exact Adj17_not_15_16 H3.
Qed.

Theorem tf_15_4_0 : Adj17 15 4 -> Adj17 4 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 0. assume H3: Adj17 15 0.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_1 : Adj17 15 4 -> Adj17 4 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 1. assume H3: Adj17 15 1.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_2 : Adj17 15 4 -> Adj17 4 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 2. assume H3: Adj17 15 2.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_3 : Adj17 15 4 -> Adj17 4 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 3. assume H3: Adj17 15 3.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_4 : Adj17 15 4 -> Adj17 4 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 4. assume H3: Adj17 15 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_15_4_5 : Adj17 15 4 -> Adj17 4 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 5. assume H3: Adj17 15 5.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_6 : Adj17 15 4 -> Adj17 4 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 6. assume H3: Adj17 15 6.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_7 : Adj17 15 4 -> Adj17 4 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 7. assume H3: Adj17 15 7.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_8 : Adj17 15 4 -> Adj17 4 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 8. assume H3: Adj17 15 8.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_9 : Adj17 15 4 -> Adj17 4 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 9. assume H3: Adj17 15 9.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_10 : Adj17 15 4 -> Adj17 4 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 10. assume H3: Adj17 15 10.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_11 : Adj17 15 4 -> Adj17 4 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 11. assume H3: Adj17 15 11.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_12 : Adj17 15 4 -> Adj17 4 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 12. assume H3: Adj17 15 12.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_13 : Adj17 15 4 -> Adj17 4 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 13. assume H3: Adj17 15 13.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_14 : Adj17 15 4 -> Adj17 4 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 14. assume H3: Adj17 15 14.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_4_15 : Adj17 15 4 -> Adj17 4 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_4_16 : Adj17 15 4 -> Adj17 4 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 4. assume H2: Adj17 4 16. assume H3: Adj17 15 16.
exact Adj17_not_15_4 H1.
Qed.

Theorem tf_15_5_0 : Adj17 15 5 -> Adj17 5 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 0. assume H3: Adj17 15 0.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_1 : Adj17 15 5 -> Adj17 5 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 1. assume H3: Adj17 15 1.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_2 : Adj17 15 5 -> Adj17 5 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 2. assume H3: Adj17 15 2.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_3 : Adj17 15 5 -> Adj17 5 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 3. assume H3: Adj17 15 3.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_4 : Adj17 15 5 -> Adj17 5 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 4. assume H3: Adj17 15 4.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_5 : Adj17 15 5 -> Adj17 5 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 5. assume H3: Adj17 15 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_15_5_6 : Adj17 15 5 -> Adj17 5 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 6. assume H3: Adj17 15 6.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_7 : Adj17 15 5 -> Adj17 5 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 7. assume H3: Adj17 15 7.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_8 : Adj17 15 5 -> Adj17 5 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 8. assume H3: Adj17 15 8.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_9 : Adj17 15 5 -> Adj17 5 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 9. assume H3: Adj17 15 9.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_10 : Adj17 15 5 -> Adj17 5 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 10. assume H3: Adj17 15 10.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_11 : Adj17 15 5 -> Adj17 5 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 11. assume H3: Adj17 15 11.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_12 : Adj17 15 5 -> Adj17 5 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 12. assume H3: Adj17 15 12.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_13 : Adj17 15 5 -> Adj17 5 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 13. assume H3: Adj17 15 13.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_14 : Adj17 15 5 -> Adj17 5 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 14. assume H3: Adj17 15 14.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_5_15 : Adj17 15 5 -> Adj17 5 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_5_16 : Adj17 15 5 -> Adj17 5 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 5. assume H2: Adj17 5 16. assume H3: Adj17 15 16.
exact Adj17_not_15_5 H1.
Qed.

Theorem tf_15_6_0 : Adj17 15 6 -> Adj17 6 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 0. assume H3: Adj17 15 0.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_1 : Adj17 15 6 -> Adj17 6 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 1. assume H3: Adj17 15 1.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_2 : Adj17 15 6 -> Adj17 6 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 2. assume H3: Adj17 15 2.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_3 : Adj17 15 6 -> Adj17 6 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 3. assume H3: Adj17 15 3.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_4 : Adj17 15 6 -> Adj17 6 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 4. assume H3: Adj17 15 4.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_5 : Adj17 15 6 -> Adj17 6 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 5. assume H3: Adj17 15 5.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_6 : Adj17 15 6 -> Adj17 6 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 6. assume H3: Adj17 15 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_15_6_7 : Adj17 15 6 -> Adj17 6 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 7. assume H3: Adj17 15 7.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_8 : Adj17 15 6 -> Adj17 6 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 8. assume H3: Adj17 15 8.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_9 : Adj17 15 6 -> Adj17 6 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 9. assume H3: Adj17 15 9.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_10 : Adj17 15 6 -> Adj17 6 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 10. assume H3: Adj17 15 10.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_11 : Adj17 15 6 -> Adj17 6 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 11. assume H3: Adj17 15 11.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_12 : Adj17 15 6 -> Adj17 6 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 12. assume H3: Adj17 15 12.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_13 : Adj17 15 6 -> Adj17 6 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 13. assume H3: Adj17 15 13.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_14 : Adj17 15 6 -> Adj17 6 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 14. assume H3: Adj17 15 14.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_6_15 : Adj17 15 6 -> Adj17 6 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_6_16 : Adj17 15 6 -> Adj17 6 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 6. assume H2: Adj17 6 16. assume H3: Adj17 15 16.
exact Adj17_not_15_6 H1.
Qed.

Theorem tf_15_7_0 : Adj17 15 7 -> Adj17 7 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 0. assume H3: Adj17 15 0.
exact Adj17_not_7_0 H2.
Qed.

Theorem tf_15_7_1 : Adj17 15 7 -> Adj17 7 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 1. assume H3: Adj17 15 1.
exact Adj17_not_15_1 H3.
Qed.

Theorem tf_15_7_2 : Adj17 15 7 -> Adj17 7 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 2. assume H3: Adj17 15 2.
exact Adj17_not_7_2 H2.
Qed.

Theorem tf_15_7_3 : Adj17 15 7 -> Adj17 7 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 3. assume H3: Adj17 15 3.
exact Adj17_not_7_3 H2.
Qed.

Theorem tf_15_7_4 : Adj17 15 7 -> Adj17 7 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 4. assume H3: Adj17 15 4.
exact Adj17_not_15_4 H3.
Qed.

Theorem tf_15_7_5 : Adj17 15 7 -> Adj17 7 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 5. assume H3: Adj17 15 5.
exact Adj17_not_7_5 H2.
Qed.

Theorem tf_15_7_6 : Adj17 15 7 -> Adj17 7 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 6. assume H3: Adj17 15 6.
exact Adj17_not_7_6 H2.
Qed.

Theorem tf_15_7_7 : Adj17 15 7 -> Adj17 7 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 7. assume H3: Adj17 15 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_15_7_8 : Adj17 15 7 -> Adj17 7 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 8. assume H3: Adj17 15 8.
exact Adj17_not_7_8 H2.
Qed.

Theorem tf_15_7_9 : Adj17 15 7 -> Adj17 7 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 9. assume H3: Adj17 15 9.
exact Adj17_not_15_9 H3.
Qed.

Theorem tf_15_7_10 : Adj17 15 7 -> Adj17 7 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 10. assume H3: Adj17 15 10.
exact Adj17_not_15_10 H3.
Qed.

Theorem tf_15_7_11 : Adj17 15 7 -> Adj17 7 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 11. assume H3: Adj17 15 11.
exact Adj17_not_7_11 H2.
Qed.

Theorem tf_15_7_12 : Adj17 15 7 -> Adj17 7 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 12. assume H3: Adj17 15 12.
exact Adj17_not_7_12 H2.
Qed.

Theorem tf_15_7_13 : Adj17 15 7 -> Adj17 7 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 13. assume H3: Adj17 15 13.
exact Adj17_not_7_13 H2.
Qed.

Theorem tf_15_7_14 : Adj17 15 7 -> Adj17 7 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 14. assume H3: Adj17 15 14.
exact Adj17_not_7_14 H2.
Qed.

Theorem tf_15_7_15 : Adj17 15 7 -> Adj17 7 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_7_16 : Adj17 15 7 -> Adj17 7 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 7. assume H2: Adj17 7 16. assume H3: Adj17 15 16.
exact Adj17_not_7_16 H2.
Qed.

Theorem tf_15_8_0 : Adj17 15 8 -> Adj17 8 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 0. assume H3: Adj17 15 0.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_1 : Adj17 15 8 -> Adj17 8 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 1. assume H3: Adj17 15 1.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_2 : Adj17 15 8 -> Adj17 8 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 2. assume H3: Adj17 15 2.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_3 : Adj17 15 8 -> Adj17 8 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 3. assume H3: Adj17 15 3.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_4 : Adj17 15 8 -> Adj17 8 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 4. assume H3: Adj17 15 4.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_5 : Adj17 15 8 -> Adj17 8 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 5. assume H3: Adj17 15 5.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_6 : Adj17 15 8 -> Adj17 8 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 6. assume H3: Adj17 15 6.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_7 : Adj17 15 8 -> Adj17 8 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 7. assume H3: Adj17 15 7.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_8 : Adj17 15 8 -> Adj17 8 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 8. assume H3: Adj17 15 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_15_8_9 : Adj17 15 8 -> Adj17 8 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 9. assume H3: Adj17 15 9.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_10 : Adj17 15 8 -> Adj17 8 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 10. assume H3: Adj17 15 10.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_11 : Adj17 15 8 -> Adj17 8 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 11. assume H3: Adj17 15 11.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_12 : Adj17 15 8 -> Adj17 8 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 12. assume H3: Adj17 15 12.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_13 : Adj17 15 8 -> Adj17 8 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 13. assume H3: Adj17 15 13.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_14 : Adj17 15 8 -> Adj17 8 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 14. assume H3: Adj17 15 14.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_8_15 : Adj17 15 8 -> Adj17 8 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_8_16 : Adj17 15 8 -> Adj17 8 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 8. assume H2: Adj17 8 16. assume H3: Adj17 15 16.
exact Adj17_not_15_8 H1.
Qed.

Theorem tf_15_9_0 : Adj17 15 9 -> Adj17 9 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 0. assume H3: Adj17 15 0.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_1 : Adj17 15 9 -> Adj17 9 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 1. assume H3: Adj17 15 1.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_2 : Adj17 15 9 -> Adj17 9 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 2. assume H3: Adj17 15 2.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_3 : Adj17 15 9 -> Adj17 9 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 3. assume H3: Adj17 15 3.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_4 : Adj17 15 9 -> Adj17 9 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 4. assume H3: Adj17 15 4.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_5 : Adj17 15 9 -> Adj17 9 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 5. assume H3: Adj17 15 5.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_6 : Adj17 15 9 -> Adj17 9 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 6. assume H3: Adj17 15 6.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_7 : Adj17 15 9 -> Adj17 9 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 7. assume H3: Adj17 15 7.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_8 : Adj17 15 9 -> Adj17 9 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 8. assume H3: Adj17 15 8.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_9 : Adj17 15 9 -> Adj17 9 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 9. assume H3: Adj17 15 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_15_9_10 : Adj17 15 9 -> Adj17 9 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 10. assume H3: Adj17 15 10.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_11 : Adj17 15 9 -> Adj17 9 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 11. assume H3: Adj17 15 11.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_12 : Adj17 15 9 -> Adj17 9 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 12. assume H3: Adj17 15 12.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_13 : Adj17 15 9 -> Adj17 9 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 13. assume H3: Adj17 15 13.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_14 : Adj17 15 9 -> Adj17 9 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 14. assume H3: Adj17 15 14.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_9_15 : Adj17 15 9 -> Adj17 9 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_9_16 : Adj17 15 9 -> Adj17 9 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 9. assume H2: Adj17 9 16. assume H3: Adj17 15 16.
exact Adj17_not_15_9 H1.
Qed.

Theorem tf_15_10_0 : Adj17 15 10 -> Adj17 10 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 0. assume H3: Adj17 15 0.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_1 : Adj17 15 10 -> Adj17 10 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 1. assume H3: Adj17 15 1.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_2 : Adj17 15 10 -> Adj17 10 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 2. assume H3: Adj17 15 2.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_3 : Adj17 15 10 -> Adj17 10 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 3. assume H3: Adj17 15 3.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_4 : Adj17 15 10 -> Adj17 10 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 4. assume H3: Adj17 15 4.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_5 : Adj17 15 10 -> Adj17 10 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 5. assume H3: Adj17 15 5.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_6 : Adj17 15 10 -> Adj17 10 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 6. assume H3: Adj17 15 6.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_7 : Adj17 15 10 -> Adj17 10 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 7. assume H3: Adj17 15 7.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_8 : Adj17 15 10 -> Adj17 10 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 8. assume H3: Adj17 15 8.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_9 : Adj17 15 10 -> Adj17 10 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 9. assume H3: Adj17 15 9.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_10 : Adj17 15 10 -> Adj17 10 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 10. assume H3: Adj17 15 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_15_10_11 : Adj17 15 10 -> Adj17 10 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 11. assume H3: Adj17 15 11.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_12 : Adj17 15 10 -> Adj17 10 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 12. assume H3: Adj17 15 12.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_13 : Adj17 15 10 -> Adj17 10 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 13. assume H3: Adj17 15 13.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_14 : Adj17 15 10 -> Adj17 10 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 14. assume H3: Adj17 15 14.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_10_15 : Adj17 15 10 -> Adj17 10 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_10_16 : Adj17 15 10 -> Adj17 10 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 10. assume H2: Adj17 10 16. assume H3: Adj17 15 16.
exact Adj17_not_15_10 H1.
Qed.

Theorem tf_15_11_0 : Adj17 15 11 -> Adj17 11 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 0. assume H3: Adj17 15 0.
exact Adj17_not_11_0 H2.
Qed.

Theorem tf_15_11_1 : Adj17 15 11 -> Adj17 11 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 1. assume H3: Adj17 15 1.
exact Adj17_not_15_1 H3.
Qed.

Theorem tf_15_11_2 : Adj17 15 11 -> Adj17 11 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 2. assume H3: Adj17 15 2.
exact Adj17_not_11_2 H2.
Qed.

Theorem tf_15_11_3 : Adj17 15 11 -> Adj17 11 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 3. assume H3: Adj17 15 3.
exact Adj17_not_11_3 H2.
Qed.

Theorem tf_15_11_4 : Adj17 15 11 -> Adj17 11 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 4. assume H3: Adj17 15 4.
exact Adj17_not_11_4 H2.
Qed.

Theorem tf_15_11_5 : Adj17 15 11 -> Adj17 11 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 5. assume H3: Adj17 15 5.
exact Adj17_not_15_5 H3.
Qed.

Theorem tf_15_11_6 : Adj17 15 11 -> Adj17 11 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 6. assume H3: Adj17 15 6.
exact Adj17_not_15_6 H3.
Qed.

Theorem tf_15_11_7 : Adj17 15 11 -> Adj17 11 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 7. assume H3: Adj17 15 7.
exact Adj17_not_11_7 H2.
Qed.

Theorem tf_15_11_8 : Adj17 15 11 -> Adj17 11 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 8. assume H3: Adj17 15 8.
exact Adj17_not_15_8 H3.
Qed.

Theorem tf_15_11_9 : Adj17 15 11 -> Adj17 11 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 9. assume H3: Adj17 15 9.
exact Adj17_not_11_9 H2.
Qed.

Theorem tf_15_11_10 : Adj17 15 11 -> Adj17 11 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 10. assume H3: Adj17 15 10.
exact Adj17_not_11_10 H2.
Qed.

Theorem tf_15_11_11 : Adj17 15 11 -> Adj17 11 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 11. assume H3: Adj17 15 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_15_11_12 : Adj17 15 11 -> Adj17 11 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 12. assume H3: Adj17 15 12.
exact Adj17_not_11_12 H2.
Qed.

Theorem tf_15_11_13 : Adj17 15 11 -> Adj17 11 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 13. assume H3: Adj17 15 13.
exact Adj17_not_11_13 H2.
Qed.

Theorem tf_15_11_14 : Adj17 15 11 -> Adj17 11 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 14. assume H3: Adj17 15 14.
exact Adj17_not_11_14 H2.
Qed.

Theorem tf_15_11_15 : Adj17 15 11 -> Adj17 11 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_11_16 : Adj17 15 11 -> Adj17 11 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 11. assume H2: Adj17 11 16. assume H3: Adj17 15 16.
exact Adj17_not_11_16 H2.
Qed.

Theorem tf_15_12_0 : Adj17 15 12 -> Adj17 12 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 0. assume H3: Adj17 15 0.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_1 : Adj17 15 12 -> Adj17 12 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 1. assume H3: Adj17 15 1.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_2 : Adj17 15 12 -> Adj17 12 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 2. assume H3: Adj17 15 2.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_3 : Adj17 15 12 -> Adj17 12 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 3. assume H3: Adj17 15 3.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_4 : Adj17 15 12 -> Adj17 12 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 4. assume H3: Adj17 15 4.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_5 : Adj17 15 12 -> Adj17 12 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 5. assume H3: Adj17 15 5.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_6 : Adj17 15 12 -> Adj17 12 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 6. assume H3: Adj17 15 6.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_7 : Adj17 15 12 -> Adj17 12 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 7. assume H3: Adj17 15 7.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_8 : Adj17 15 12 -> Adj17 12 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 8. assume H3: Adj17 15 8.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_9 : Adj17 15 12 -> Adj17 12 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 9. assume H3: Adj17 15 9.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_10 : Adj17 15 12 -> Adj17 12 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 10. assume H3: Adj17 15 10.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_11 : Adj17 15 12 -> Adj17 12 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 11. assume H3: Adj17 15 11.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_12 : Adj17 15 12 -> Adj17 12 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 12. assume H3: Adj17 15 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_15_12_13 : Adj17 15 12 -> Adj17 12 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 13. assume H3: Adj17 15 13.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_14 : Adj17 15 12 -> Adj17 12 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 14. assume H3: Adj17 15 14.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_12_15 : Adj17 15 12 -> Adj17 12 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_12_16 : Adj17 15 12 -> Adj17 12 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 12. assume H2: Adj17 12 16. assume H3: Adj17 15 16.
exact Adj17_not_15_12 H1.
Qed.

Theorem tf_15_13_0 : Adj17 15 13 -> Adj17 13 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 0. assume H3: Adj17 15 0.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_1 : Adj17 15 13 -> Adj17 13 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 1. assume H3: Adj17 15 1.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_2 : Adj17 15 13 -> Adj17 13 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 2. assume H3: Adj17 15 2.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_3 : Adj17 15 13 -> Adj17 13 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 3. assume H3: Adj17 15 3.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_4 : Adj17 15 13 -> Adj17 13 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 4. assume H3: Adj17 15 4.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_5 : Adj17 15 13 -> Adj17 13 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 5. assume H3: Adj17 15 5.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_6 : Adj17 15 13 -> Adj17 13 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 6. assume H3: Adj17 15 6.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_7 : Adj17 15 13 -> Adj17 13 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 7. assume H3: Adj17 15 7.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_8 : Adj17 15 13 -> Adj17 13 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 8. assume H3: Adj17 15 8.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_9 : Adj17 15 13 -> Adj17 13 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 9. assume H3: Adj17 15 9.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_10 : Adj17 15 13 -> Adj17 13 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 10. assume H3: Adj17 15 10.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_11 : Adj17 15 13 -> Adj17 13 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 11. assume H3: Adj17 15 11.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_12 : Adj17 15 13 -> Adj17 13 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 12. assume H3: Adj17 15 12.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_13 : Adj17 15 13 -> Adj17 13 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 13. assume H3: Adj17 15 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_15_13_14 : Adj17 15 13 -> Adj17 13 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 14. assume H3: Adj17 15 14.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_13_15 : Adj17 15 13 -> Adj17 13 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_13_16 : Adj17 15 13 -> Adj17 13 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 13. assume H2: Adj17 13 16. assume H3: Adj17 15 16.
exact Adj17_not_15_13 H1.
Qed.

Theorem tf_15_14_0 : Adj17 15 14 -> Adj17 14 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 0. assume H3: Adj17 15 0.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_1 : Adj17 15 14 -> Adj17 14 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 1. assume H3: Adj17 15 1.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_2 : Adj17 15 14 -> Adj17 14 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 2. assume H3: Adj17 15 2.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_3 : Adj17 15 14 -> Adj17 14 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 3. assume H3: Adj17 15 3.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_4 : Adj17 15 14 -> Adj17 14 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 4. assume H3: Adj17 15 4.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_5 : Adj17 15 14 -> Adj17 14 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 5. assume H3: Adj17 15 5.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_6 : Adj17 15 14 -> Adj17 14 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 6. assume H3: Adj17 15 6.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_7 : Adj17 15 14 -> Adj17 14 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 7. assume H3: Adj17 15 7.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_8 : Adj17 15 14 -> Adj17 14 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 8. assume H3: Adj17 15 8.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_9 : Adj17 15 14 -> Adj17 14 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 9. assume H3: Adj17 15 9.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_10 : Adj17 15 14 -> Adj17 14 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 10. assume H3: Adj17 15 10.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_11 : Adj17 15 14 -> Adj17 14 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 11. assume H3: Adj17 15 11.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_12 : Adj17 15 14 -> Adj17 14 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 12. assume H3: Adj17 15 12.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_13 : Adj17 15 14 -> Adj17 14 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 13. assume H3: Adj17 15 13.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_14_14 : Adj17 15 14 -> Adj17 14 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 14. assume H3: Adj17 15 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_15_14_15 : Adj17 15 14 -> Adj17 14 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_14_16 : Adj17 15 14 -> Adj17 14 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 14. assume H2: Adj17 14 16. assume H3: Adj17 15 16.
exact Adj17_not_15_14 H1.
Qed.

Theorem tf_15_15_0 : Adj17 15 15 -> Adj17 15 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 0. assume H3: Adj17 15 0.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_1 : Adj17 15 15 -> Adj17 15 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 1. assume H3: Adj17 15 1.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_2 : Adj17 15 15 -> Adj17 15 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 2. assume H3: Adj17 15 2.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_3 : Adj17 15 15 -> Adj17 15 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 3. assume H3: Adj17 15 3.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_4 : Adj17 15 15 -> Adj17 15 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 4. assume H3: Adj17 15 4.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_5 : Adj17 15 15 -> Adj17 15 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 5. assume H3: Adj17 15 5.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_6 : Adj17 15 15 -> Adj17 15 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 6. assume H3: Adj17 15 6.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_7 : Adj17 15 15 -> Adj17 15 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 7. assume H3: Adj17 15 7.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_8 : Adj17 15 15 -> Adj17 15 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 8. assume H3: Adj17 15 8.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_9 : Adj17 15 15 -> Adj17 15 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 9. assume H3: Adj17 15 9.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_10 : Adj17 15 15 -> Adj17 15 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 10. assume H3: Adj17 15 10.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_11 : Adj17 15 15 -> Adj17 15 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 11. assume H3: Adj17 15 11.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_12 : Adj17 15 15 -> Adj17 15 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 12. assume H3: Adj17 15 12.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_13 : Adj17 15 15 -> Adj17 15 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 13. assume H3: Adj17 15 13.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_14 : Adj17 15 15 -> Adj17 15 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 14. assume H3: Adj17 15 14.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_15 : Adj17 15 15 -> Adj17 15 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_15_16 : Adj17 15 15 -> Adj17 15 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 15. assume H2: Adj17 15 16. assume H3: Adj17 15 16.
exact Adj17_not_15_15 H1.
Qed.

Theorem tf_15_16_0 : Adj17 15 16 -> Adj17 16 0 -> Adj17 15 0 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 0. assume H3: Adj17 15 0.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_1 : Adj17 15 16 -> Adj17 16 1 -> Adj17 15 1 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 1. assume H3: Adj17 15 1.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_2 : Adj17 15 16 -> Adj17 16 2 -> Adj17 15 2 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 2. assume H3: Adj17 15 2.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_3 : Adj17 15 16 -> Adj17 16 3 -> Adj17 15 3 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 3. assume H3: Adj17 15 3.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_4 : Adj17 15 16 -> Adj17 16 4 -> Adj17 15 4 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 4. assume H3: Adj17 15 4.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_5 : Adj17 15 16 -> Adj17 16 5 -> Adj17 15 5 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 5. assume H3: Adj17 15 5.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_6 : Adj17 15 16 -> Adj17 16 6 -> Adj17 15 6 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 6. assume H3: Adj17 15 6.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_7 : Adj17 15 16 -> Adj17 16 7 -> Adj17 15 7 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 7. assume H3: Adj17 15 7.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_8 : Adj17 15 16 -> Adj17 16 8 -> Adj17 15 8 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 8. assume H3: Adj17 15 8.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_9 : Adj17 15 16 -> Adj17 16 9 -> Adj17 15 9 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 9. assume H3: Adj17 15 9.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_10 : Adj17 15 16 -> Adj17 16 10 -> Adj17 15 10 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 10. assume H3: Adj17 15 10.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_11 : Adj17 15 16 -> Adj17 16 11 -> Adj17 15 11 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 11. assume H3: Adj17 15 11.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_12 : Adj17 15 16 -> Adj17 16 12 -> Adj17 15 12 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 12. assume H3: Adj17 15 12.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_13 : Adj17 15 16 -> Adj17 16 13 -> Adj17 15 13 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 13. assume H3: Adj17 15 13.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_14 : Adj17 15 16 -> Adj17 16 14 -> Adj17 15 14 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 14. assume H3: Adj17 15 14.
exact Adj17_not_15_16 H1.
Qed.

Theorem tf_15_16_15 : Adj17 15 16 -> Adj17 16 15 -> Adj17 15 15 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 15. assume H3: Adj17 15 15.
exact Adj17_not_15_15 H3.
Qed.

Theorem tf_15_16_16 : Adj17 15 16 -> Adj17 16 16 -> Adj17 15 16 -> False.
assume H1: Adj17 15 16. assume H2: Adj17 16 16. assume H3: Adj17 15 16.
exact Adj17_not_16_16 H2.
Qed.

Theorem tf_16_0_0 : Adj17 16 0 -> Adj17 0 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 0. assume H3: Adj17 16 0.
exact Adj17_not_0_0 H2.
Qed.

Theorem tf_16_0_1 : Adj17 16 0 -> Adj17 0 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 1. assume H3: Adj17 16 1.
exact Adj17_not_0_1 H2.
Qed.

Theorem tf_16_0_2 : Adj17 16 0 -> Adj17 0 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 2. assume H3: Adj17 16 2.
exact Adj17_not_0_2 H2.
Qed.

Theorem tf_16_0_3 : Adj17 16 0 -> Adj17 0 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 3. assume H3: Adj17 16 3.
exact Adj17_not_0_3 H2.
Qed.

Theorem tf_16_0_4 : Adj17 16 0 -> Adj17 0 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 4. assume H3: Adj17 16 4.
exact Adj17_not_0_4 H2.
Qed.

Theorem tf_16_0_5 : Adj17 16 0 -> Adj17 0 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 5. assume H3: Adj17 16 5.
exact Adj17_not_0_5 H2.
Qed.

Theorem tf_16_0_6 : Adj17 16 0 -> Adj17 0 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 6. assume H3: Adj17 16 6.
exact Adj17_not_0_6 H2.
Qed.

Theorem tf_16_0_7 : Adj17 16 0 -> Adj17 0 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 7. assume H3: Adj17 16 7.
exact Adj17_not_0_7 H2.
Qed.

Theorem tf_16_0_8 : Adj17 16 0 -> Adj17 0 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 8. assume H3: Adj17 16 8.
exact Adj17_not_0_8 H2.
Qed.

Theorem tf_16_0_9 : Adj17 16 0 -> Adj17 0 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 9. assume H3: Adj17 16 9.
exact Adj17_not_16_9 H3.
Qed.

Theorem tf_16_0_10 : Adj17 16 0 -> Adj17 0 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 10. assume H3: Adj17 16 10.
exact Adj17_not_0_10 H2.
Qed.

Theorem tf_16_0_11 : Adj17 16 0 -> Adj17 0 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 11. assume H3: Adj17 16 11.
exact Adj17_not_0_11 H2.
Qed.

Theorem tf_16_0_12 : Adj17 16 0 -> Adj17 0 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 12. assume H3: Adj17 16 12.
exact Adj17_not_0_12 H2.
Qed.

Theorem tf_16_0_13 : Adj17 16 0 -> Adj17 0 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 13. assume H3: Adj17 16 13.
exact Adj17_not_0_13 H2.
Qed.

Theorem tf_16_0_14 : Adj17 16 0 -> Adj17 0 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 14. assume H3: Adj17 16 14.
exact Adj17_not_16_14 H3.
Qed.

Theorem tf_16_0_15 : Adj17 16 0 -> Adj17 0 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 15. assume H3: Adj17 16 15.
exact Adj17_not_16_15 H3.
Qed.

Theorem tf_16_0_16 : Adj17 16 0 -> Adj17 0 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 0. assume H2: Adj17 0 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_1_0 : Adj17 16 1 -> Adj17 1 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 0. assume H3: Adj17 16 0.
exact Adj17_not_1_0 H2.
Qed.

Theorem tf_16_1_1 : Adj17 16 1 -> Adj17 1 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 1. assume H3: Adj17 16 1.
exact Adj17_not_1_1 H2.
Qed.

Theorem tf_16_1_2 : Adj17 16 1 -> Adj17 1 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 2. assume H3: Adj17 16 2.
exact Adj17_not_1_2 H2.
Qed.

Theorem tf_16_1_3 : Adj17 16 1 -> Adj17 1 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 3. assume H3: Adj17 16 3.
exact Adj17_not_1_3 H2.
Qed.

Theorem tf_16_1_4 : Adj17 16 1 -> Adj17 1 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 4. assume H3: Adj17 16 4.
exact Adj17_not_1_4 H2.
Qed.

Theorem tf_16_1_5 : Adj17 16 1 -> Adj17 1 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 5. assume H3: Adj17 16 5.
exact Adj17_not_1_5 H2.
Qed.

Theorem tf_16_1_6 : Adj17 16 1 -> Adj17 1 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 6. assume H3: Adj17 16 6.
exact Adj17_not_1_6 H2.
Qed.

Theorem tf_16_1_7 : Adj17 16 1 -> Adj17 1 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 7. assume H3: Adj17 16 7.
exact Adj17_not_16_7 H3.
Qed.

Theorem tf_16_1_8 : Adj17 16 1 -> Adj17 1 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 8. assume H3: Adj17 16 8.
exact Adj17_not_1_8 H2.
Qed.

Theorem tf_16_1_9 : Adj17 16 1 -> Adj17 1 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 9. assume H3: Adj17 16 9.
exact Adj17_not_1_9 H2.
Qed.

Theorem tf_16_1_10 : Adj17 16 1 -> Adj17 1 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 10. assume H3: Adj17 16 10.
exact Adj17_not_1_10 H2.
Qed.

Theorem tf_16_1_11 : Adj17 16 1 -> Adj17 1 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 11. assume H3: Adj17 16 11.
exact Adj17_not_16_11 H3.
Qed.

Theorem tf_16_1_12 : Adj17 16 1 -> Adj17 1 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 12. assume H3: Adj17 16 12.
exact Adj17_not_1_12 H2.
Qed.

Theorem tf_16_1_13 : Adj17 16 1 -> Adj17 1 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 13. assume H3: Adj17 16 13.
exact Adj17_not_16_13 H3.
Qed.

Theorem tf_16_1_14 : Adj17 16 1 -> Adj17 1 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 14. assume H3: Adj17 16 14.
exact Adj17_not_1_14 H2.
Qed.

Theorem tf_16_1_15 : Adj17 16 1 -> Adj17 1 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 15. assume H3: Adj17 16 15.
exact Adj17_not_1_15 H2.
Qed.

Theorem tf_16_1_16 : Adj17 16 1 -> Adj17 1 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 1. assume H2: Adj17 1 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_2_0 : Adj17 16 2 -> Adj17 2 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 0. assume H3: Adj17 16 0.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_1 : Adj17 16 2 -> Adj17 2 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 1. assume H3: Adj17 16 1.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_2 : Adj17 16 2 -> Adj17 2 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 2. assume H3: Adj17 16 2.
exact Adj17_not_2_2 H2.
Qed.

Theorem tf_16_2_3 : Adj17 16 2 -> Adj17 2 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 3. assume H3: Adj17 16 3.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_4 : Adj17 16 2 -> Adj17 2 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 4. assume H3: Adj17 16 4.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_5 : Adj17 16 2 -> Adj17 2 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 5. assume H3: Adj17 16 5.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_6 : Adj17 16 2 -> Adj17 2 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 6. assume H3: Adj17 16 6.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_7 : Adj17 16 2 -> Adj17 2 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 7. assume H3: Adj17 16 7.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_8 : Adj17 16 2 -> Adj17 2 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 8. assume H3: Adj17 16 8.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_9 : Adj17 16 2 -> Adj17 2 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 9. assume H3: Adj17 16 9.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_10 : Adj17 16 2 -> Adj17 2 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 10. assume H3: Adj17 16 10.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_11 : Adj17 16 2 -> Adj17 2 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 11. assume H3: Adj17 16 11.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_12 : Adj17 16 2 -> Adj17 2 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 12. assume H3: Adj17 16 12.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_13 : Adj17 16 2 -> Adj17 2 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 13. assume H3: Adj17 16 13.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_14 : Adj17 16 2 -> Adj17 2 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 14. assume H3: Adj17 16 14.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_15 : Adj17 16 2 -> Adj17 2 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 15. assume H3: Adj17 16 15.
exact Adj17_not_16_2 H1.
Qed.

Theorem tf_16_2_16 : Adj17 16 2 -> Adj17 2 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 2. assume H2: Adj17 2 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_3_0 : Adj17 16 3 -> Adj17 3 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 0. assume H3: Adj17 16 0.
exact Adj17_not_3_0 H2.
Qed.

Theorem tf_16_3_1 : Adj17 16 3 -> Adj17 3 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 1. assume H3: Adj17 16 1.
exact Adj17_not_3_1 H2.
Qed.

Theorem tf_16_3_2 : Adj17 16 3 -> Adj17 3 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 2. assume H3: Adj17 16 2.
exact Adj17_not_3_2 H2.
Qed.

Theorem tf_16_3_3 : Adj17 16 3 -> Adj17 3 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 3. assume H3: Adj17 16 3.
exact Adj17_not_3_3 H2.
Qed.

Theorem tf_16_3_4 : Adj17 16 3 -> Adj17 3 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 4. assume H3: Adj17 16 4.
exact Adj17_not_3_4 H2.
Qed.

Theorem tf_16_3_5 : Adj17 16 3 -> Adj17 3 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 5. assume H3: Adj17 16 5.
exact Adj17_not_3_5 H2.
Qed.

Theorem tf_16_3_6 : Adj17 16 3 -> Adj17 3 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 6. assume H3: Adj17 16 6.
exact Adj17_not_16_6 H3.
Qed.

Theorem tf_16_3_7 : Adj17 16 3 -> Adj17 3 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 7. assume H3: Adj17 16 7.
exact Adj17_not_3_7 H2.
Qed.

Theorem tf_16_3_8 : Adj17 16 3 -> Adj17 3 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 8. assume H3: Adj17 16 8.
exact Adj17_not_16_8 H3.
Qed.

Theorem tf_16_3_9 : Adj17 16 3 -> Adj17 3 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 9. assume H3: Adj17 16 9.
exact Adj17_not_3_9 H2.
Qed.

Theorem tf_16_3_10 : Adj17 16 3 -> Adj17 3 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 10. assume H3: Adj17 16 10.
exact Adj17_not_3_10 H2.
Qed.

Theorem tf_16_3_11 : Adj17 16 3 -> Adj17 3 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 11. assume H3: Adj17 16 11.
exact Adj17_not_3_11 H2.
Qed.

Theorem tf_16_3_12 : Adj17 16 3 -> Adj17 3 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 12. assume H3: Adj17 16 12.
exact Adj17_not_3_12 H2.
Qed.

Theorem tf_16_3_13 : Adj17 16 3 -> Adj17 3 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 13. assume H3: Adj17 16 13.
exact Adj17_not_16_13 H3.
Qed.

Theorem tf_16_3_14 : Adj17 16 3 -> Adj17 3 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 14. assume H3: Adj17 16 14.
exact Adj17_not_3_14 H2.
Qed.

Theorem tf_16_3_15 : Adj17 16 3 -> Adj17 3 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 15. assume H3: Adj17 16 15.
exact Adj17_not_16_15 H3.
Qed.

Theorem tf_16_3_16 : Adj17 16 3 -> Adj17 3 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 3. assume H2: Adj17 3 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_4_0 : Adj17 16 4 -> Adj17 4 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 0. assume H3: Adj17 16 0.
exact Adj17_not_4_0 H2.
Qed.

Theorem tf_16_4_1 : Adj17 16 4 -> Adj17 4 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 1. assume H3: Adj17 16 1.
exact Adj17_not_4_1 H2.
Qed.

Theorem tf_16_4_2 : Adj17 16 4 -> Adj17 4 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 2. assume H3: Adj17 16 2.
exact Adj17_not_4_2 H2.
Qed.

Theorem tf_16_4_3 : Adj17 16 4 -> Adj17 4 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 3. assume H3: Adj17 16 3.
exact Adj17_not_4_3 H2.
Qed.

Theorem tf_16_4_4 : Adj17 16 4 -> Adj17 4 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 4. assume H3: Adj17 16 4.
exact Adj17_not_4_4 H2.
Qed.

Theorem tf_16_4_5 : Adj17 16 4 -> Adj17 4 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 5. assume H3: Adj17 16 5.
exact Adj17_not_16_5 H3.
Qed.

Theorem tf_16_4_6 : Adj17 16 4 -> Adj17 4 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 6. assume H3: Adj17 16 6.
exact Adj17_not_4_6 H2.
Qed.

Theorem tf_16_4_7 : Adj17 16 4 -> Adj17 4 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 7. assume H3: Adj17 16 7.
exact Adj17_not_16_7 H3.
Qed.

Theorem tf_16_4_8 : Adj17 16 4 -> Adj17 4 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 8. assume H3: Adj17 16 8.
exact Adj17_not_4_8 H2.
Qed.

Theorem tf_16_4_9 : Adj17 16 4 -> Adj17 4 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 9. assume H3: Adj17 16 9.
exact Adj17_not_4_9 H2.
Qed.

Theorem tf_16_4_10 : Adj17 16 4 -> Adj17 4 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 10. assume H3: Adj17 16 10.
exact Adj17_not_4_10 H2.
Qed.

Theorem tf_16_4_11 : Adj17 16 4 -> Adj17 4 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 11. assume H3: Adj17 16 11.
exact Adj17_not_4_11 H2.
Qed.

Theorem tf_16_4_12 : Adj17 16 4 -> Adj17 4 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 12. assume H3: Adj17 16 12.
exact Adj17_not_16_12 H3.
Qed.

Theorem tf_16_4_13 : Adj17 16 4 -> Adj17 4 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 13. assume H3: Adj17 16 13.
exact Adj17_not_4_13 H2.
Qed.

Theorem tf_16_4_14 : Adj17 16 4 -> Adj17 4 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 14. assume H3: Adj17 16 14.
exact Adj17_not_16_14 H3.
Qed.

Theorem tf_16_4_15 : Adj17 16 4 -> Adj17 4 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 15. assume H3: Adj17 16 15.
exact Adj17_not_4_15 H2.
Qed.

Theorem tf_16_4_16 : Adj17 16 4 -> Adj17 4 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 4. assume H2: Adj17 4 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_5_0 : Adj17 16 5 -> Adj17 5 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 0. assume H3: Adj17 16 0.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_1 : Adj17 16 5 -> Adj17 5 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 1. assume H3: Adj17 16 1.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_2 : Adj17 16 5 -> Adj17 5 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 2. assume H3: Adj17 16 2.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_3 : Adj17 16 5 -> Adj17 5 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 3. assume H3: Adj17 16 3.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_4 : Adj17 16 5 -> Adj17 5 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 4. assume H3: Adj17 16 4.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_5 : Adj17 16 5 -> Adj17 5 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 5. assume H3: Adj17 16 5.
exact Adj17_not_5_5 H2.
Qed.

Theorem tf_16_5_6 : Adj17 16 5 -> Adj17 5 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 6. assume H3: Adj17 16 6.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_7 : Adj17 16 5 -> Adj17 5 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 7. assume H3: Adj17 16 7.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_8 : Adj17 16 5 -> Adj17 5 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 8. assume H3: Adj17 16 8.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_9 : Adj17 16 5 -> Adj17 5 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 9. assume H3: Adj17 16 9.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_10 : Adj17 16 5 -> Adj17 5 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 10. assume H3: Adj17 16 10.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_11 : Adj17 16 5 -> Adj17 5 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 11. assume H3: Adj17 16 11.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_12 : Adj17 16 5 -> Adj17 5 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 12. assume H3: Adj17 16 12.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_13 : Adj17 16 5 -> Adj17 5 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 13. assume H3: Adj17 16 13.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_14 : Adj17 16 5 -> Adj17 5 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 14. assume H3: Adj17 16 14.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_15 : Adj17 16 5 -> Adj17 5 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 15. assume H3: Adj17 16 15.
exact Adj17_not_16_5 H1.
Qed.

Theorem tf_16_5_16 : Adj17 16 5 -> Adj17 5 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 5. assume H2: Adj17 5 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_6_0 : Adj17 16 6 -> Adj17 6 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 0. assume H3: Adj17 16 0.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_1 : Adj17 16 6 -> Adj17 6 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 1. assume H3: Adj17 16 1.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_2 : Adj17 16 6 -> Adj17 6 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 2. assume H3: Adj17 16 2.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_3 : Adj17 16 6 -> Adj17 6 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 3. assume H3: Adj17 16 3.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_4 : Adj17 16 6 -> Adj17 6 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 4. assume H3: Adj17 16 4.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_5 : Adj17 16 6 -> Adj17 6 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 5. assume H3: Adj17 16 5.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_6 : Adj17 16 6 -> Adj17 6 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 6. assume H3: Adj17 16 6.
exact Adj17_not_6_6 H2.
Qed.

Theorem tf_16_6_7 : Adj17 16 6 -> Adj17 6 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 7. assume H3: Adj17 16 7.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_8 : Adj17 16 6 -> Adj17 6 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 8. assume H3: Adj17 16 8.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_9 : Adj17 16 6 -> Adj17 6 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 9. assume H3: Adj17 16 9.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_10 : Adj17 16 6 -> Adj17 6 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 10. assume H3: Adj17 16 10.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_11 : Adj17 16 6 -> Adj17 6 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 11. assume H3: Adj17 16 11.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_12 : Adj17 16 6 -> Adj17 6 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 12. assume H3: Adj17 16 12.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_13 : Adj17 16 6 -> Adj17 6 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 13. assume H3: Adj17 16 13.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_14 : Adj17 16 6 -> Adj17 6 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 14. assume H3: Adj17 16 14.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_15 : Adj17 16 6 -> Adj17 6 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 15. assume H3: Adj17 16 15.
exact Adj17_not_16_6 H1.
Qed.

Theorem tf_16_6_16 : Adj17 16 6 -> Adj17 6 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 6. assume H2: Adj17 6 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_7_0 : Adj17 16 7 -> Adj17 7 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 0. assume H3: Adj17 16 0.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_1 : Adj17 16 7 -> Adj17 7 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 1. assume H3: Adj17 16 1.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_2 : Adj17 16 7 -> Adj17 7 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 2. assume H3: Adj17 16 2.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_3 : Adj17 16 7 -> Adj17 7 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 3. assume H3: Adj17 16 3.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_4 : Adj17 16 7 -> Adj17 7 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 4. assume H3: Adj17 16 4.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_5 : Adj17 16 7 -> Adj17 7 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 5. assume H3: Adj17 16 5.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_6 : Adj17 16 7 -> Adj17 7 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 6. assume H3: Adj17 16 6.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_7 : Adj17 16 7 -> Adj17 7 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 7. assume H3: Adj17 16 7.
exact Adj17_not_7_7 H2.
Qed.

Theorem tf_16_7_8 : Adj17 16 7 -> Adj17 7 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 8. assume H3: Adj17 16 8.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_9 : Adj17 16 7 -> Adj17 7 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 9. assume H3: Adj17 16 9.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_10 : Adj17 16 7 -> Adj17 7 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 10. assume H3: Adj17 16 10.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_11 : Adj17 16 7 -> Adj17 7 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 11. assume H3: Adj17 16 11.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_12 : Adj17 16 7 -> Adj17 7 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 12. assume H3: Adj17 16 12.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_13 : Adj17 16 7 -> Adj17 7 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 13. assume H3: Adj17 16 13.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_14 : Adj17 16 7 -> Adj17 7 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 14. assume H3: Adj17 16 14.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_15 : Adj17 16 7 -> Adj17 7 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 15. assume H3: Adj17 16 15.
exact Adj17_not_16_7 H1.
Qed.

Theorem tf_16_7_16 : Adj17 16 7 -> Adj17 7 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 7. assume H2: Adj17 7 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_8_0 : Adj17 16 8 -> Adj17 8 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 0. assume H3: Adj17 16 0.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_1 : Adj17 16 8 -> Adj17 8 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 1. assume H3: Adj17 16 1.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_2 : Adj17 16 8 -> Adj17 8 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 2. assume H3: Adj17 16 2.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_3 : Adj17 16 8 -> Adj17 8 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 3. assume H3: Adj17 16 3.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_4 : Adj17 16 8 -> Adj17 8 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 4. assume H3: Adj17 16 4.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_5 : Adj17 16 8 -> Adj17 8 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 5. assume H3: Adj17 16 5.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_6 : Adj17 16 8 -> Adj17 8 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 6. assume H3: Adj17 16 6.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_7 : Adj17 16 8 -> Adj17 8 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 7. assume H3: Adj17 16 7.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_8 : Adj17 16 8 -> Adj17 8 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 8. assume H3: Adj17 16 8.
exact Adj17_not_8_8 H2.
Qed.

Theorem tf_16_8_9 : Adj17 16 8 -> Adj17 8 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 9. assume H3: Adj17 16 9.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_10 : Adj17 16 8 -> Adj17 8 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 10. assume H3: Adj17 16 10.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_11 : Adj17 16 8 -> Adj17 8 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 11. assume H3: Adj17 16 11.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_12 : Adj17 16 8 -> Adj17 8 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 12. assume H3: Adj17 16 12.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_13 : Adj17 16 8 -> Adj17 8 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 13. assume H3: Adj17 16 13.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_14 : Adj17 16 8 -> Adj17 8 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 14. assume H3: Adj17 16 14.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_15 : Adj17 16 8 -> Adj17 8 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 15. assume H3: Adj17 16 15.
exact Adj17_not_16_8 H1.
Qed.

Theorem tf_16_8_16 : Adj17 16 8 -> Adj17 8 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 8. assume H2: Adj17 8 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_9_0 : Adj17 16 9 -> Adj17 9 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 0. assume H3: Adj17 16 0.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_1 : Adj17 16 9 -> Adj17 9 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 1. assume H3: Adj17 16 1.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_2 : Adj17 16 9 -> Adj17 9 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 2. assume H3: Adj17 16 2.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_3 : Adj17 16 9 -> Adj17 9 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 3. assume H3: Adj17 16 3.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_4 : Adj17 16 9 -> Adj17 9 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 4. assume H3: Adj17 16 4.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_5 : Adj17 16 9 -> Adj17 9 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 5. assume H3: Adj17 16 5.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_6 : Adj17 16 9 -> Adj17 9 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 6. assume H3: Adj17 16 6.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_7 : Adj17 16 9 -> Adj17 9 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 7. assume H3: Adj17 16 7.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_8 : Adj17 16 9 -> Adj17 9 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 8. assume H3: Adj17 16 8.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_9 : Adj17 16 9 -> Adj17 9 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 9. assume H3: Adj17 16 9.
exact Adj17_not_9_9 H2.
Qed.

Theorem tf_16_9_10 : Adj17 16 9 -> Adj17 9 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 10. assume H3: Adj17 16 10.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_11 : Adj17 16 9 -> Adj17 9 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 11. assume H3: Adj17 16 11.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_12 : Adj17 16 9 -> Adj17 9 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 12. assume H3: Adj17 16 12.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_13 : Adj17 16 9 -> Adj17 9 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 13. assume H3: Adj17 16 13.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_14 : Adj17 16 9 -> Adj17 9 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 14. assume H3: Adj17 16 14.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_15 : Adj17 16 9 -> Adj17 9 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 15. assume H3: Adj17 16 15.
exact Adj17_not_16_9 H1.
Qed.

Theorem tf_16_9_16 : Adj17 16 9 -> Adj17 9 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 9. assume H2: Adj17 9 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_10_0 : Adj17 16 10 -> Adj17 10 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 0. assume H3: Adj17 16 0.
exact Adj17_not_10_0 H2.
Qed.

Theorem tf_16_10_1 : Adj17 16 10 -> Adj17 10 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 1. assume H3: Adj17 16 1.
exact Adj17_not_10_1 H2.
Qed.

Theorem tf_16_10_2 : Adj17 16 10 -> Adj17 10 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 2. assume H3: Adj17 16 2.
exact Adj17_not_16_2 H3.
Qed.

Theorem tf_16_10_3 : Adj17 16 10 -> Adj17 10 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 3. assume H3: Adj17 16 3.
exact Adj17_not_10_3 H2.
Qed.

Theorem tf_16_10_4 : Adj17 16 10 -> Adj17 10 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 4. assume H3: Adj17 16 4.
exact Adj17_not_10_4 H2.
Qed.

Theorem tf_16_10_5 : Adj17 16 10 -> Adj17 10 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 5. assume H3: Adj17 16 5.
exact Adj17_not_16_5 H3.
Qed.

Theorem tf_16_10_6 : Adj17 16 10 -> Adj17 10 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 6. assume H3: Adj17 16 6.
exact Adj17_not_16_6 H3.
Qed.

Theorem tf_16_10_7 : Adj17 16 10 -> Adj17 10 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 7. assume H3: Adj17 16 7.
exact Adj17_not_16_7 H3.
Qed.

Theorem tf_16_10_8 : Adj17 16 10 -> Adj17 10 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 8. assume H3: Adj17 16 8.
exact Adj17_not_10_8 H2.
Qed.

Theorem tf_16_10_9 : Adj17 16 10 -> Adj17 10 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 9. assume H3: Adj17 16 9.
exact Adj17_not_10_9 H2.
Qed.

Theorem tf_16_10_10 : Adj17 16 10 -> Adj17 10 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 10. assume H3: Adj17 16 10.
exact Adj17_not_10_10 H2.
Qed.

Theorem tf_16_10_11 : Adj17 16 10 -> Adj17 10 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 11. assume H3: Adj17 16 11.
exact Adj17_not_10_11 H2.
Qed.

Theorem tf_16_10_12 : Adj17 16 10 -> Adj17 10 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 12. assume H3: Adj17 16 12.
exact Adj17_not_10_12 H2.
Qed.

Theorem tf_16_10_13 : Adj17 16 10 -> Adj17 10 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 13. assume H3: Adj17 16 13.
exact Adj17_not_10_13 H2.
Qed.

Theorem tf_16_10_14 : Adj17 16 10 -> Adj17 10 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 14. assume H3: Adj17 16 14.
exact Adj17_not_10_14 H2.
Qed.

Theorem tf_16_10_15 : Adj17 16 10 -> Adj17 10 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 15. assume H3: Adj17 16 15.
exact Adj17_not_10_15 H2.
Qed.

Theorem tf_16_10_16 : Adj17 16 10 -> Adj17 10 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 10. assume H2: Adj17 10 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_11_0 : Adj17 16 11 -> Adj17 11 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 0. assume H3: Adj17 16 0.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_1 : Adj17 16 11 -> Adj17 11 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 1. assume H3: Adj17 16 1.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_2 : Adj17 16 11 -> Adj17 11 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 2. assume H3: Adj17 16 2.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_3 : Adj17 16 11 -> Adj17 11 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 3. assume H3: Adj17 16 3.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_4 : Adj17 16 11 -> Adj17 11 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 4. assume H3: Adj17 16 4.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_5 : Adj17 16 11 -> Adj17 11 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 5. assume H3: Adj17 16 5.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_6 : Adj17 16 11 -> Adj17 11 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 6. assume H3: Adj17 16 6.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_7 : Adj17 16 11 -> Adj17 11 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 7. assume H3: Adj17 16 7.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_8 : Adj17 16 11 -> Adj17 11 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 8. assume H3: Adj17 16 8.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_9 : Adj17 16 11 -> Adj17 11 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 9. assume H3: Adj17 16 9.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_10 : Adj17 16 11 -> Adj17 11 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 10. assume H3: Adj17 16 10.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_11 : Adj17 16 11 -> Adj17 11 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 11. assume H3: Adj17 16 11.
exact Adj17_not_11_11 H2.
Qed.

Theorem tf_16_11_12 : Adj17 16 11 -> Adj17 11 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 12. assume H3: Adj17 16 12.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_13 : Adj17 16 11 -> Adj17 11 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 13. assume H3: Adj17 16 13.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_14 : Adj17 16 11 -> Adj17 11 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 14. assume H3: Adj17 16 14.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_15 : Adj17 16 11 -> Adj17 11 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 15. assume H3: Adj17 16 15.
exact Adj17_not_16_11 H1.
Qed.

Theorem tf_16_11_16 : Adj17 16 11 -> Adj17 11 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 11. assume H2: Adj17 11 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_12_0 : Adj17 16 12 -> Adj17 12 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 0. assume H3: Adj17 16 0.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_1 : Adj17 16 12 -> Adj17 12 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 1. assume H3: Adj17 16 1.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_2 : Adj17 16 12 -> Adj17 12 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 2. assume H3: Adj17 16 2.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_3 : Adj17 16 12 -> Adj17 12 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 3. assume H3: Adj17 16 3.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_4 : Adj17 16 12 -> Adj17 12 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 4. assume H3: Adj17 16 4.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_5 : Adj17 16 12 -> Adj17 12 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 5. assume H3: Adj17 16 5.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_6 : Adj17 16 12 -> Adj17 12 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 6. assume H3: Adj17 16 6.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_7 : Adj17 16 12 -> Adj17 12 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 7. assume H3: Adj17 16 7.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_8 : Adj17 16 12 -> Adj17 12 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 8. assume H3: Adj17 16 8.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_9 : Adj17 16 12 -> Adj17 12 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 9. assume H3: Adj17 16 9.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_10 : Adj17 16 12 -> Adj17 12 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 10. assume H3: Adj17 16 10.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_11 : Adj17 16 12 -> Adj17 12 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 11. assume H3: Adj17 16 11.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_12 : Adj17 16 12 -> Adj17 12 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 12. assume H3: Adj17 16 12.
exact Adj17_not_12_12 H2.
Qed.

Theorem tf_16_12_13 : Adj17 16 12 -> Adj17 12 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 13. assume H3: Adj17 16 13.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_14 : Adj17 16 12 -> Adj17 12 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 14. assume H3: Adj17 16 14.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_15 : Adj17 16 12 -> Adj17 12 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 15. assume H3: Adj17 16 15.
exact Adj17_not_16_12 H1.
Qed.

Theorem tf_16_12_16 : Adj17 16 12 -> Adj17 12 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 12. assume H2: Adj17 12 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_13_0 : Adj17 16 13 -> Adj17 13 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 0. assume H3: Adj17 16 0.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_1 : Adj17 16 13 -> Adj17 13 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 1. assume H3: Adj17 16 1.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_2 : Adj17 16 13 -> Adj17 13 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 2. assume H3: Adj17 16 2.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_3 : Adj17 16 13 -> Adj17 13 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 3. assume H3: Adj17 16 3.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_4 : Adj17 16 13 -> Adj17 13 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 4. assume H3: Adj17 16 4.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_5 : Adj17 16 13 -> Adj17 13 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 5. assume H3: Adj17 16 5.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_6 : Adj17 16 13 -> Adj17 13 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 6. assume H3: Adj17 16 6.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_7 : Adj17 16 13 -> Adj17 13 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 7. assume H3: Adj17 16 7.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_8 : Adj17 16 13 -> Adj17 13 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 8. assume H3: Adj17 16 8.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_9 : Adj17 16 13 -> Adj17 13 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 9. assume H3: Adj17 16 9.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_10 : Adj17 16 13 -> Adj17 13 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 10. assume H3: Adj17 16 10.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_11 : Adj17 16 13 -> Adj17 13 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 11. assume H3: Adj17 16 11.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_12 : Adj17 16 13 -> Adj17 13 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 12. assume H3: Adj17 16 12.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_13 : Adj17 16 13 -> Adj17 13 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 13. assume H3: Adj17 16 13.
exact Adj17_not_13_13 H2.
Qed.

Theorem tf_16_13_14 : Adj17 16 13 -> Adj17 13 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 14. assume H3: Adj17 16 14.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_15 : Adj17 16 13 -> Adj17 13 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 15. assume H3: Adj17 16 15.
exact Adj17_not_16_13 H1.
Qed.

Theorem tf_16_13_16 : Adj17 16 13 -> Adj17 13 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 13. assume H2: Adj17 13 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_14_0 : Adj17 16 14 -> Adj17 14 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 0. assume H3: Adj17 16 0.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_1 : Adj17 16 14 -> Adj17 14 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 1. assume H3: Adj17 16 1.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_2 : Adj17 16 14 -> Adj17 14 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 2. assume H3: Adj17 16 2.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_3 : Adj17 16 14 -> Adj17 14 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 3. assume H3: Adj17 16 3.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_4 : Adj17 16 14 -> Adj17 14 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 4. assume H3: Adj17 16 4.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_5 : Adj17 16 14 -> Adj17 14 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 5. assume H3: Adj17 16 5.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_6 : Adj17 16 14 -> Adj17 14 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 6. assume H3: Adj17 16 6.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_7 : Adj17 16 14 -> Adj17 14 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 7. assume H3: Adj17 16 7.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_8 : Adj17 16 14 -> Adj17 14 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 8. assume H3: Adj17 16 8.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_9 : Adj17 16 14 -> Adj17 14 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 9. assume H3: Adj17 16 9.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_10 : Adj17 16 14 -> Adj17 14 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 10. assume H3: Adj17 16 10.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_11 : Adj17 16 14 -> Adj17 14 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 11. assume H3: Adj17 16 11.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_12 : Adj17 16 14 -> Adj17 14 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 12. assume H3: Adj17 16 12.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_13 : Adj17 16 14 -> Adj17 14 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 13. assume H3: Adj17 16 13.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_14 : Adj17 16 14 -> Adj17 14 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 14. assume H3: Adj17 16 14.
exact Adj17_not_14_14 H2.
Qed.

Theorem tf_16_14_15 : Adj17 16 14 -> Adj17 14 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 15. assume H3: Adj17 16 15.
exact Adj17_not_16_14 H1.
Qed.

Theorem tf_16_14_16 : Adj17 16 14 -> Adj17 14 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 14. assume H2: Adj17 14 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_15_0 : Adj17 16 15 -> Adj17 15 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 0. assume H3: Adj17 16 0.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_1 : Adj17 16 15 -> Adj17 15 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 1. assume H3: Adj17 16 1.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_2 : Adj17 16 15 -> Adj17 15 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 2. assume H3: Adj17 16 2.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_3 : Adj17 16 15 -> Adj17 15 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 3. assume H3: Adj17 16 3.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_4 : Adj17 16 15 -> Adj17 15 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 4. assume H3: Adj17 16 4.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_5 : Adj17 16 15 -> Adj17 15 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 5. assume H3: Adj17 16 5.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_6 : Adj17 16 15 -> Adj17 15 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 6. assume H3: Adj17 16 6.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_7 : Adj17 16 15 -> Adj17 15 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 7. assume H3: Adj17 16 7.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_8 : Adj17 16 15 -> Adj17 15 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 8. assume H3: Adj17 16 8.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_9 : Adj17 16 15 -> Adj17 15 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 9. assume H3: Adj17 16 9.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_10 : Adj17 16 15 -> Adj17 15 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 10. assume H3: Adj17 16 10.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_11 : Adj17 16 15 -> Adj17 15 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 11. assume H3: Adj17 16 11.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_12 : Adj17 16 15 -> Adj17 15 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 12. assume H3: Adj17 16 12.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_13 : Adj17 16 15 -> Adj17 15 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 13. assume H3: Adj17 16 13.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_14 : Adj17 16 15 -> Adj17 15 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 14. assume H3: Adj17 16 14.
exact Adj17_not_16_15 H1.
Qed.

Theorem tf_16_15_15 : Adj17 16 15 -> Adj17 15 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 15. assume H3: Adj17 16 15.
exact Adj17_not_15_15 H2.
Qed.

Theorem tf_16_15_16 : Adj17 16 15 -> Adj17 15 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 15. assume H2: Adj17 15 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H3.
Qed.

Theorem tf_16_16_0 : Adj17 16 16 -> Adj17 16 0 -> Adj17 16 0 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 0. assume H3: Adj17 16 0.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_1 : Adj17 16 16 -> Adj17 16 1 -> Adj17 16 1 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 1. assume H3: Adj17 16 1.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_2 : Adj17 16 16 -> Adj17 16 2 -> Adj17 16 2 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 2. assume H3: Adj17 16 2.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_3 : Adj17 16 16 -> Adj17 16 3 -> Adj17 16 3 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 3. assume H3: Adj17 16 3.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_4 : Adj17 16 16 -> Adj17 16 4 -> Adj17 16 4 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 4. assume H3: Adj17 16 4.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_5 : Adj17 16 16 -> Adj17 16 5 -> Adj17 16 5 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 5. assume H3: Adj17 16 5.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_6 : Adj17 16 16 -> Adj17 16 6 -> Adj17 16 6 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 6. assume H3: Adj17 16 6.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_7 : Adj17 16 16 -> Adj17 16 7 -> Adj17 16 7 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 7. assume H3: Adj17 16 7.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_8 : Adj17 16 16 -> Adj17 16 8 -> Adj17 16 8 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 8. assume H3: Adj17 16 8.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_9 : Adj17 16 16 -> Adj17 16 9 -> Adj17 16 9 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 9. assume H3: Adj17 16 9.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_10 : Adj17 16 16 -> Adj17 16 10 -> Adj17 16 10 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 10. assume H3: Adj17 16 10.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_11 : Adj17 16 16 -> Adj17 16 11 -> Adj17 16 11 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 11. assume H3: Adj17 16 11.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_12 : Adj17 16 16 -> Adj17 16 12 -> Adj17 16 12 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 12. assume H3: Adj17 16 12.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_13 : Adj17 16 16 -> Adj17 16 13 -> Adj17 16 13 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 13. assume H3: Adj17 16 13.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_14 : Adj17 16 16 -> Adj17 16 14 -> Adj17 16 14 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 14. assume H3: Adj17 16 14.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_15 : Adj17 16 16 -> Adj17 16 15 -> Adj17 16 15 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 15. assume H3: Adj17 16 15.
exact Adj17_not_16_16 H1.
Qed.

Theorem tf_16_16_16 : Adj17 16 16 -> Adj17 16 16 -> Adj17 16 16 -> False.
assume H1: Adj17 16 16. assume H2: Adj17 16 16. assume H3: Adj17 16 16.
exact Adj17_not_16_16 H1.
Qed.

Theorem Adj17_triangle_free : triangle_free 17 Adj17.
Admitted.
