Definition xor_col : set -> set -> set -> prop :=
  fun c1 c2 r =>
    (c1 = 0 /\ c2 = 0 /\ r = 0) \/
    (c1 = 0 /\ c2 = 1 /\ r = 1) \/
    (c1 = 0 /\ c2 = 2 /\ r = 2) \/
    (c1 = 0 /\ c2 = 3 /\ r = 3) \/
    (c1 = 1 /\ c2 = 0 /\ r = 1) \/
    (c1 = 1 /\ c2 = 1 /\ r = 0) \/
    (c1 = 1 /\ c2 = 2 /\ r = 3) \/
    (c1 = 1 /\ c2 = 3 /\ r = 2) \/
    (c1 = 2 /\ c2 = 0 /\ r = 2) \/
    (c1 = 2 /\ c2 = 1 /\ r = 3) \/
    (c1 = 2 /\ c2 = 2 /\ r = 0) \/
    (c1 = 2 /\ c2 = 3 /\ r = 1) \/
    (c1 = 3 /\ c2 = 0 /\ r = 3) \/
    (c1 = 3 /\ c2 = 1 /\ r = 2) \/
    (c1 = 3 /\ c2 = 2 /\ r = 1) \/
    (c1 = 3 /\ c2 = 3 /\ r = 0).

Theorem xor_0_0 : xor_col 0 0 0.
prove (0 = 0 /\ 0 = 0 /\ 0 = 0) \/
    (0 = 0 /\ 0 = 1 /\ 0 = 1) \/
    (0 = 0 /\ 0 = 2 /\ 0 = 2) \/
    (0 = 0 /\ 0 = 3 /\ 0 = 3) \/
    (0 = 1 /\ 0 = 0 /\ 0 = 1) \/
    (0 = 1 /\ 0 = 1 /\ 0 = 0) \/
    (0 = 1 /\ 0 = 2 /\ 0 = 3) \/
    (0 = 1 /\ 0 = 3 /\ 0 = 2) \/
    (0 = 2 /\ 0 = 0 /\ 0 = 2) \/
    (0 = 2 /\ 0 = 1 /\ 0 = 3) \/
    (0 = 2 /\ 0 = 2 /\ 0 = 0) \/
    (0 = 2 /\ 0 = 3 /\ 0 = 1) \/
    (0 = 3 /\ 0 = 0 /\ 0 = 3) \/
    (0 = 3 /\ 0 = 1 /\ 0 = 2) \/
    (0 = 3 /\ 0 = 2 /\ 0 = 1) \/
    (0 = 3 /\ 0 = 3 /\ 0 = 0).
apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL.
apply andI.
- reflexivity.
- apply andI.
  + reflexivity.
  + reflexivity.
Qed.

Theorem xor_1_1 : xor_col 1 1 0.
prove (1 = 0 /\ 1 = 0 /\ 0 = 0) \/
    (1 = 0 /\ 1 = 1 /\ 0 = 1) \/
    (1 = 0 /\ 1 = 2 /\ 0 = 2) \/
    (1 = 0 /\ 1 = 3 /\ 0 = 3) \/
    (1 = 1 /\ 1 = 0 /\ 0 = 1) \/
    (1 = 1 /\ 1 = 1 /\ 0 = 0) \/
    (1 = 1 /\ 1 = 2 /\ 0 = 3) \/
    (1 = 1 /\ 1 = 3 /\ 0 = 2) \/
    (1 = 2 /\ 1 = 0 /\ 0 = 2) \/
    (1 = 2 /\ 1 = 1 /\ 0 = 3) \/
    (1 = 2 /\ 1 = 2 /\ 0 = 0) \/
    (1 = 2 /\ 1 = 3 /\ 0 = 1) \/
    (1 = 3 /\ 1 = 0 /\ 0 = 3) \/
    (1 = 3 /\ 1 = 1 /\ 0 = 2) \/
    (1 = 3 /\ 1 = 2 /\ 0 = 1) \/
    (1 = 3 /\ 1 = 3 /\ 0 = 0).
apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIR.
apply andI.
- reflexivity.
- apply andI.
  + reflexivity.
  + reflexivity.
Qed.

Theorem xor_2_2 : xor_col 2 2 0.
prove (2 = 0 /\ 2 = 0 /\ 0 = 0) \/
    (2 = 0 /\ 2 = 1 /\ 0 = 1) \/
    (2 = 0 /\ 2 = 2 /\ 0 = 2) \/
    (2 = 0 /\ 2 = 3 /\ 0 = 3) \/
    (2 = 1 /\ 2 = 0 /\ 0 = 1) \/
    (2 = 1 /\ 2 = 1 /\ 0 = 0) \/
    (2 = 1 /\ 2 = 2 /\ 0 = 3) \/
    (2 = 1 /\ 2 = 3 /\ 0 = 2) \/
    (2 = 2 /\ 2 = 0 /\ 0 = 2) \/
    (2 = 2 /\ 2 = 1 /\ 0 = 3) \/
    (2 = 2 /\ 2 = 2 /\ 0 = 0) \/
    (2 = 2 /\ 2 = 3 /\ 0 = 1) \/
    (2 = 3 /\ 2 = 0 /\ 0 = 3) \/
    (2 = 3 /\ 2 = 1 /\ 0 = 2) \/
    (2 = 3 /\ 2 = 2 /\ 0 = 1) \/
    (2 = 3 /\ 2 = 3 /\ 0 = 0).
apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIR.
apply andI.
- reflexivity.
- apply andI.
  + reflexivity.
  + reflexivity.
Qed.

Theorem xor_3_3 : xor_col 3 3 0.
prove (3 = 0 /\ 3 = 0 /\ 0 = 0) \/
    (3 = 0 /\ 3 = 1 /\ 0 = 1) \/
    (3 = 0 /\ 3 = 2 /\ 0 = 2) \/
    (3 = 0 /\ 3 = 3 /\ 0 = 3) \/
    (3 = 1 /\ 3 = 0 /\ 0 = 1) \/
    (3 = 1 /\ 3 = 1 /\ 0 = 0) \/
    (3 = 1 /\ 3 = 2 /\ 0 = 3) \/
    (3 = 1 /\ 3 = 3 /\ 0 = 2) \/
    (3 = 2 /\ 3 = 0 /\ 0 = 2) \/
    (3 = 2 /\ 3 = 1 /\ 0 = 3) \/
    (3 = 2 /\ 3 = 2 /\ 0 = 0) \/
    (3 = 2 /\ 3 = 3 /\ 0 = 1) \/
    (3 = 3 /\ 3 = 0 /\ 0 = 3) \/
    (3 = 3 /\ 3 = 1 /\ 0 = 2) \/
    (3 = 3 /\ 3 = 2 /\ 0 = 1) \/
    (3 = 3 /\ 3 = 3 /\ 0 = 0).
apply orIR.
apply andI.
- reflexivity.
- apply andI.
  + reflexivity.
  + reflexivity.
Qed.

Theorem xor_1_2 : xor_col 1 2 3.
prove (1 = 0 /\ 2 = 0 /\ 3 = 0) \/
    (1 = 0 /\ 2 = 1 /\ 3 = 1) \/
    (1 = 0 /\ 2 = 2 /\ 3 = 2) \/
    (1 = 0 /\ 2 = 3 /\ 3 = 3) \/
    (1 = 1 /\ 2 = 0 /\ 3 = 1) \/
    (1 = 1 /\ 2 = 1 /\ 3 = 0) \/
    (1 = 1 /\ 2 = 2 /\ 3 = 3) \/
    (1 = 1 /\ 2 = 3 /\ 3 = 2) \/
    (1 = 2 /\ 2 = 0 /\ 3 = 2) \/
    (1 = 2 /\ 2 = 1 /\ 3 = 3) \/
    (1 = 2 /\ 2 = 2 /\ 3 = 0) \/
    (1 = 2 /\ 2 = 3 /\ 3 = 1) \/
    (1 = 3 /\ 2 = 0 /\ 3 = 3) \/
    (1 = 3 /\ 2 = 1 /\ 3 = 2) \/
    (1 = 3 /\ 2 = 2 /\ 3 = 1) \/
    (1 = 3 /\ 2 = 3 /\ 3 = 0).
apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIR.
apply andI.
- reflexivity.
- apply andI.
  + reflexivity.
  + reflexivity.
Qed.

Theorem xor_2_1 : xor_col 2 1 3.
prove (2 = 0 /\ 1 = 0 /\ 3 = 0) \/
    (2 = 0 /\ 1 = 1 /\ 3 = 1) \/
    (2 = 0 /\ 1 = 2 /\ 3 = 2) \/
    (2 = 0 /\ 1 = 3 /\ 3 = 3) \/
    (2 = 1 /\ 1 = 0 /\ 3 = 1) \/
    (2 = 1 /\ 1 = 1 /\ 3 = 0) \/
    (2 = 1 /\ 1 = 2 /\ 3 = 3) \/
    (2 = 1 /\ 1 = 3 /\ 3 = 2) \/
    (2 = 2 /\ 1 = 0 /\ 3 = 2) \/
    (2 = 2 /\ 1 = 1 /\ 3 = 3) \/
    (2 = 2 /\ 1 = 2 /\ 3 = 0) \/
    (2 = 2 /\ 1 = 3 /\ 3 = 1) \/
    (2 = 3 /\ 1 = 0 /\ 3 = 3) \/
    (2 = 3 /\ 1 = 1 /\ 3 = 2) \/
    (2 = 3 /\ 1 = 2 /\ 3 = 1) \/
    (2 = 3 /\ 1 = 3 /\ 3 = 0).
apply orIL. apply orIL. apply orIL. apply orIL. apply orIL. apply orIR.
apply andI.
- reflexivity.
- apply andI.
  + reflexivity.
  + reflexivity.
Qed.
