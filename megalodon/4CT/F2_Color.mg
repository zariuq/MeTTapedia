Definition Colors : set := 4.

Definition is_color : set -> prop := fun c => c :e 4.

Theorem Zero_is_color : is_color 0.
exact In_0_4.
Qed.

Theorem Red_is_color : is_color 1.
exact In_1_4.
Qed.

Theorem Blue_is_color : is_color 2.
exact In_2_4.
Qed.

Theorem Purple_is_color : is_color 3.
exact In_3_4.
Qed.

Definition color_xor : set -> set -> set :=
  fun c1 c2 =>
    if c1 = 0 then c2
    else if c2 = 0 then c1
    else if c1 = c2 then 0
    else if c1 = 1 /\ c2 = 2 then 3
    else if c1 = 2 /\ c2 = 1 then 3
    else if c1 = 1 /\ c2 = 3 then 2
    else if c1 = 3 /\ c2 = 1 then 2
    else if c1 = 2 /\ c2 = 3 then 1
    else if c1 = 3 /\ c2 = 2 then 1
    else 0.

Theorem xor_zero_l : forall c:set, color_xor 0 c = c.
let c.
claim L1: 0 = 0. reflexivity.
exact If_i_1 (0 = 0) c (if c = 0 then 0
       else if 0 = c then 0
       else if 0 = 1 /\ c = 2 then 3
       else if 0 = 2 /\ c = 1 then 3
       else if 0 = 1 /\ c = 3 then 2
       else if 0 = 3 /\ c = 1 then 2
       else if 0 = 2 /\ c = 3 then 1
       else if 0 = 3 /\ c = 2 then 1
       else 0) L1.
Qed.

Theorem xor_0_0 : color_xor 0 0 = 0.
exact xor_zero_l 0.
Qed.

Theorem xor_1_0 : color_xor 1 0 = 1.
claim L1: ~(1 = 0). exact neq_1_0.
claim L2: 0 = 0. reflexivity.
apply eq_i_tra (color_xor 1 0) (if 0 = 0 then 1
       else if 1 = 0 then 0
       else if 1 = 1 /\ 0 = 2 then 3
       else if 1 = 2 /\ 0 = 1 then 3
       else if 1 = 1 /\ 0 = 3 then 2
       else if 1 = 3 /\ 0 = 1 then 2
       else if 1 = 2 /\ 0 = 3 then 1
       else if 1 = 3 /\ 0 = 2 then 1
       else 0) 1.
- exact If_i_0 (1 = 0) 0 (if 0 = 0 then 1
       else if 1 = 0 then 0
       else if 1 = 1 /\ 0 = 2 then 3
       else if 1 = 2 /\ 0 = 1 then 3
       else if 1 = 1 /\ 0 = 3 then 2
       else if 1 = 3 /\ 0 = 1 then 2
       else if 1 = 2 /\ 0 = 3 then 1
       else if 1 = 3 /\ 0 = 2 then 1
       else 0) L1.
- exact If_i_1 (0 = 0) 1 (if 1 = 0 then 0
       else if 1 = 1 /\ 0 = 2 then 3
       else if 1 = 2 /\ 0 = 1 then 3
       else if 1 = 1 /\ 0 = 3 then 2
       else if 1 = 3 /\ 0 = 1 then 2
       else if 1 = 2 /\ 0 = 3 then 1
       else if 1 = 3 /\ 0 = 2 then 1
       else 0) L2.
Qed.

Theorem xor_2_0 : color_xor 2 0 = 2.
claim L1: ~(2 = 0). exact neq_2_0.
claim L2: 0 = 0. reflexivity.
apply eq_i_tra (color_xor 2 0) (if 0 = 0 then 2
       else if 2 = 0 then 0
       else if 2 = 1 /\ 0 = 2 then 3
       else if 2 = 2 /\ 0 = 1 then 3
       else if 2 = 1 /\ 0 = 3 then 2
       else if 2 = 3 /\ 0 = 1 then 2
       else if 2 = 2 /\ 0 = 3 then 1
       else if 2 = 3 /\ 0 = 2 then 1
       else 0) 2.
- exact If_i_0 (2 = 0) 0 (if 0 = 0 then 2
       else if 2 = 0 then 0
       else if 2 = 1 /\ 0 = 2 then 3
       else if 2 = 2 /\ 0 = 1 then 3
       else if 2 = 1 /\ 0 = 3 then 2
       else if 2 = 3 /\ 0 = 1 then 2
       else if 2 = 2 /\ 0 = 3 then 1
       else if 2 = 3 /\ 0 = 2 then 1
       else 0) L1.
- exact If_i_1 (0 = 0) 2 (if 2 = 0 then 0
       else if 2 = 1 /\ 0 = 2 then 3
       else if 2 = 2 /\ 0 = 1 then 3
       else if 2 = 1 /\ 0 = 3 then 2
       else if 2 = 3 /\ 0 = 1 then 2
       else if 2 = 2 /\ 0 = 3 then 1
       else if 2 = 3 /\ 0 = 2 then 1
       else 0) L2.
Qed.

Theorem xor_3_0 : color_xor 3 0 = 3.
claim L1: ~(3 = 0). exact neq_3_0.
claim L2: 0 = 0. reflexivity.
apply eq_i_tra (color_xor 3 0) (if 0 = 0 then 3
       else if 3 = 0 then 0
       else if 3 = 1 /\ 0 = 2 then 3
       else if 3 = 2 /\ 0 = 1 then 3
       else if 3 = 1 /\ 0 = 3 then 2
       else if 3 = 3 /\ 0 = 1 then 2
       else if 3 = 2 /\ 0 = 3 then 1
       else if 3 = 3 /\ 0 = 2 then 1
       else 0) 3.
- exact If_i_0 (3 = 0) 0 (if 0 = 0 then 3
       else if 3 = 0 then 0
       else if 3 = 1 /\ 0 = 2 then 3
       else if 3 = 2 /\ 0 = 1 then 3
       else if 3 = 1 /\ 0 = 3 then 2
       else if 3 = 3 /\ 0 = 1 then 2
       else if 3 = 2 /\ 0 = 3 then 1
       else if 3 = 3 /\ 0 = 2 then 1
       else 0) L1.
- exact If_i_1 (0 = 0) 3 (if 3 = 0 then 0
       else if 3 = 1 /\ 0 = 2 then 3
       else if 3 = 2 /\ 0 = 1 then 3
       else if 3 = 1 /\ 0 = 3 then 2
       else if 3 = 3 /\ 0 = 1 then 2
       else if 3 = 2 /\ 0 = 3 then 1
       else if 3 = 3 /\ 0 = 2 then 1
       else 0) L2.
Qed.

Theorem xor_1_1 : color_xor 1 1 = 0.
claim L1: ~(1 = 0). exact neq_1_0.
claim L2: 1 = 1. reflexivity.
apply eq_i_tra (color_xor 1 1) (if 1 = 0 then 1
       else if 1 = 1 then 0
       else if 1 = 1 /\ 1 = 2 then 3
       else if 1 = 2 /\ 1 = 1 then 3
       else if 1 = 1 /\ 1 = 3 then 2
       else if 1 = 3 /\ 1 = 1 then 2
       else if 1 = 2 /\ 1 = 3 then 1
       else if 1 = 3 /\ 1 = 2 then 1
       else 0) 0.
- exact If_i_0 (1 = 0) 1 (if 1 = 0 then 1
       else if 1 = 1 then 0
       else if 1 = 1 /\ 1 = 2 then 3
       else if 1 = 2 /\ 1 = 1 then 3
       else if 1 = 1 /\ 1 = 3 then 2
       else if 1 = 3 /\ 1 = 1 then 2
       else if 1 = 2 /\ 1 = 3 then 1
       else if 1 = 3 /\ 1 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 1 = 0 then 1
       else if 1 = 1 then 0
       else if 1 = 1 /\ 1 = 2 then 3
       else if 1 = 2 /\ 1 = 1 then 3
       else if 1 = 1 /\ 1 = 3 then 2
       else if 1 = 3 /\ 1 = 1 then 2
       else if 1 = 2 /\ 1 = 3 then 1
       else if 1 = 3 /\ 1 = 2 then 1
       else 0) (if 1 = 1 then 0
       else if 1 = 1 /\ 1 = 2 then 3
       else if 1 = 2 /\ 1 = 1 then 3
       else if 1 = 1 /\ 1 = 3 then 2
       else if 1 = 3 /\ 1 = 1 then 2
       else if 1 = 2 /\ 1 = 3 then 1
       else if 1 = 3 /\ 1 = 2 then 1
       else 0) 0.
  + exact If_i_0 (1 = 0) 1 (if 1 = 1 then 0
       else if 1 = 1 /\ 1 = 2 then 3
       else if 1 = 2 /\ 1 = 1 then 3
       else if 1 = 1 /\ 1 = 3 then 2
       else if 1 = 3 /\ 1 = 1 then 2
       else if 1 = 2 /\ 1 = 3 then 1
       else if 1 = 3 /\ 1 = 2 then 1
       else 0) L1.
  + exact If_i_1 (1 = 1) 0 (if 1 = 1 /\ 1 = 2 then 3
       else if 1 = 2 /\ 1 = 1 then 3
       else if 1 = 1 /\ 1 = 3 then 2
       else if 1 = 3 /\ 1 = 1 then 2
       else if 1 = 2 /\ 1 = 3 then 1
       else if 1 = 3 /\ 1 = 2 then 1
       else 0) L2.
Qed.

Theorem xor_2_2 : color_xor 2 2 = 0.
claim L1: ~(2 = 0). exact neq_2_0.
claim L2: 2 = 2. reflexivity.
apply eq_i_tra (color_xor 2 2) (if 2 = 0 then 2
       else if 2 = 2 then 0
       else if 2 = 1 /\ 2 = 2 then 3
       else if 2 = 2 /\ 2 = 1 then 3
       else if 2 = 1 /\ 2 = 3 then 2
       else if 2 = 3 /\ 2 = 1 then 2
       else if 2 = 2 /\ 2 = 3 then 1
       else if 2 = 3 /\ 2 = 2 then 1
       else 0) 0.
- exact If_i_0 (2 = 0) 2 (if 2 = 0 then 2
       else if 2 = 2 then 0
       else if 2 = 1 /\ 2 = 2 then 3
       else if 2 = 2 /\ 2 = 1 then 3
       else if 2 = 1 /\ 2 = 3 then 2
       else if 2 = 3 /\ 2 = 1 then 2
       else if 2 = 2 /\ 2 = 3 then 1
       else if 2 = 3 /\ 2 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 2 = 0 then 2
       else if 2 = 2 then 0
       else if 2 = 1 /\ 2 = 2 then 3
       else if 2 = 2 /\ 2 = 1 then 3
       else if 2 = 1 /\ 2 = 3 then 2
       else if 2 = 3 /\ 2 = 1 then 2
       else if 2 = 2 /\ 2 = 3 then 1
       else if 2 = 3 /\ 2 = 2 then 1
       else 0) (if 2 = 2 then 0
       else if 2 = 1 /\ 2 = 2 then 3
       else if 2 = 2 /\ 2 = 1 then 3
       else if 2 = 1 /\ 2 = 3 then 2
       else if 2 = 3 /\ 2 = 1 then 2
       else if 2 = 2 /\ 2 = 3 then 1
       else if 2 = 3 /\ 2 = 2 then 1
       else 0) 0.
  + exact If_i_0 (2 = 0) 2 (if 2 = 2 then 0
       else if 2 = 1 /\ 2 = 2 then 3
       else if 2 = 2 /\ 2 = 1 then 3
       else if 2 = 1 /\ 2 = 3 then 2
       else if 2 = 3 /\ 2 = 1 then 2
       else if 2 = 2 /\ 2 = 3 then 1
       else if 2 = 3 /\ 2 = 2 then 1
       else 0) L1.
  + exact If_i_1 (2 = 2) 0 (if 2 = 1 /\ 2 = 2 then 3
       else if 2 = 2 /\ 2 = 1 then 3
       else if 2 = 1 /\ 2 = 3 then 2
       else if 2 = 3 /\ 2 = 1 then 2
       else if 2 = 2 /\ 2 = 3 then 1
       else if 2 = 3 /\ 2 = 2 then 1
       else 0) L2.
Qed.

Theorem xor_3_3 : color_xor 3 3 = 0.
claim L1: ~(3 = 0). exact neq_3_0.
claim L2: 3 = 3. reflexivity.
apply eq_i_tra (color_xor 3 3) (if 3 = 0 then 3
       else if 3 = 3 then 0
       else if 3 = 1 /\ 3 = 2 then 3
       else if 3 = 2 /\ 3 = 1 then 3
       else if 3 = 1 /\ 3 = 3 then 2
       else if 3 = 3 /\ 3 = 1 then 2
       else if 3 = 2 /\ 3 = 3 then 1
       else if 3 = 3 /\ 3 = 2 then 1
       else 0) 0.
- exact If_i_0 (3 = 0) 3 (if 3 = 0 then 3
       else if 3 = 3 then 0
       else if 3 = 1 /\ 3 = 2 then 3
       else if 3 = 2 /\ 3 = 1 then 3
       else if 3 = 1 /\ 3 = 3 then 2
       else if 3 = 3 /\ 3 = 1 then 2
       else if 3 = 2 /\ 3 = 3 then 1
       else if 3 = 3 /\ 3 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 3 = 0 then 3
       else if 3 = 3 then 0
       else if 3 = 1 /\ 3 = 2 then 3
       else if 3 = 2 /\ 3 = 1 then 3
       else if 3 = 1 /\ 3 = 3 then 2
       else if 3 = 3 /\ 3 = 1 then 2
       else if 3 = 2 /\ 3 = 3 then 1
       else if 3 = 3 /\ 3 = 2 then 1
       else 0) (if 3 = 3 then 0
       else if 3 = 1 /\ 3 = 2 then 3
       else if 3 = 2 /\ 3 = 1 then 3
       else if 3 = 1 /\ 3 = 3 then 2
       else if 3 = 3 /\ 3 = 1 then 2
       else if 3 = 2 /\ 3 = 3 then 1
       else if 3 = 3 /\ 3 = 2 then 1
       else 0) 0.
  + exact If_i_0 (3 = 0) 3 (if 3 = 3 then 0
       else if 3 = 1 /\ 3 = 2 then 3
       else if 3 = 2 /\ 3 = 1 then 3
       else if 3 = 1 /\ 3 = 3 then 2
       else if 3 = 3 /\ 3 = 1 then 2
       else if 3 = 2 /\ 3 = 3 then 1
       else if 3 = 3 /\ 3 = 2 then 1
       else 0) L1.
  + exact If_i_1 (3 = 3) 0 (if 3 = 1 /\ 3 = 2 then 3
       else if 3 = 2 /\ 3 = 1 then 3
       else if 3 = 1 /\ 3 = 3 then 2
       else if 3 = 3 /\ 3 = 1 then 2
       else if 3 = 2 /\ 3 = 3 then 1
       else if 3 = 3 /\ 3 = 2 then 1
       else 0) L2.
Qed.

Theorem xor_1_2 : color_xor 1 2 = 3.
claim L1: ~(1 = 0). exact neq_1_0.
claim L2: ~(2 = 0). exact neq_2_0.
claim L3: ~(1 = 2). exact neq_1_2.
claim L4: 1 = 1 /\ 2 = 2. apply andI. reflexivity. reflexivity.
apply eq_i_tra (color_xor 1 2) (if 2 = 0 then 1
       else if 1 = 2 then 0
       else if 1 = 1 /\ 2 = 2 then 3
       else if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) 3.
- exact If_i_0 (1 = 0) 2 (if 2 = 0 then 1
       else if 1 = 2 then 0
       else if 1 = 1 /\ 2 = 2 then 3
       else if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 2 = 0 then 1
       else if 1 = 2 then 0
       else if 1 = 1 /\ 2 = 2 then 3
       else if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) (if 1 = 2 then 0
       else if 1 = 1 /\ 2 = 2 then 3
       else if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) 3.
  + exact If_i_0 (2 = 0) 1 (if 1 = 2 then 0
       else if 1 = 1 /\ 2 = 2 then 3
       else if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) L2.
  + apply eq_i_tra (if 1 = 2 then 0
       else if 1 = 1 /\ 2 = 2 then 3
       else if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) (if 1 = 1 /\ 2 = 2 then 3
       else if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) 3.
    * exact If_i_0 (1 = 2) 0 (if 1 = 1 /\ 2 = 2 then 3
       else if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) L3.
    * exact If_i_1 (1 = 1 /\ 2 = 2) 3 (if 1 = 2 /\ 2 = 1 then 3
       else if 1 = 1 /\ 2 = 3 then 2
       else if 1 = 3 /\ 2 = 1 then 2
       else if 1 = 2 /\ 2 = 3 then 1
       else if 1 = 3 /\ 2 = 2 then 1
       else 0) L4.
Qed.

Theorem xor_2_1 : color_xor 2 1 = 3.
claim L1: ~(2 = 0). exact neq_2_0.
claim L2: ~(1 = 0). exact neq_1_0.
claim L3: ~(2 = 1). exact neq_2_1.
claim L4: 2 = 2 /\ 1 = 1. apply andI. reflexivity. reflexivity.
apply eq_i_tra (color_xor 2 1) (if 1 = 0 then 2
       else if 2 = 1 then 0
       else if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) 3.
- exact If_i_0 (2 = 0) 1 (if 1 = 0 then 2
       else if 2 = 1 then 0
       else if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 1 = 0 then 2
       else if 2 = 1 then 0
       else if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) (if 2 = 1 then 0
       else if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) 3.
  + exact If_i_0 (1 = 0) 2 (if 2 = 1 then 0
       else if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) L2.
  + apply eq_i_tra (if 2 = 1 then 0
       else if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) (if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) 3.
    * exact If_i_0 (2 = 1) 0 (if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) L3.
    * claim L5: ~(2 = 1 /\ 1 = 2).
        assume H. apply H. assume H1: 2 = 1. assume H2: 1 = 2. exact L3 H1.
      apply eq_i_tra (if 2 = 1 /\ 1 = 2 then 3
       else if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) (if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) 3.
      { exact If_i_0 (2 = 1 /\ 1 = 2) 3 (if 2 = 2 /\ 1 = 1 then 3
       else if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) L5. }
      { exact If_i_1 (2 = 2 /\ 1 = 1) 3 (if 2 = 1 /\ 1 = 3 then 2
       else if 2 = 3 /\ 1 = 1 then 2
       else if 2 = 2 /\ 1 = 3 then 1
       else if 2 = 3 /\ 1 = 2 then 1
       else 0) L4. }
Qed.

Theorem xor_1_3 : color_xor 1 3 = 2.
claim L1: ~(1 = 0). exact neq_1_0.
claim L2: ~(3 = 0). exact neq_3_0.
claim L3: ~(1 = 3).
  assume H: 1 = 3.
  claim H': 3 = 1.
    let Q:set->set->prop.
    assume HQ: Q 3 1.
    exact H (fun a b:set => Q b a) HQ.
  exact neq_3_1 H'.
claim L4: ~(1 = 1 /\ 3 = 2).
  assume H. apply H. assume H1: 1 = 1. assume H2: 3 = 2. exact neq_3_2 H2.
claim L5: ~(1 = 2 /\ 3 = 1).
  assume H. apply H. assume H1: 1 = 2. assume H2: 3 = 1. exact neq_1_2 H1.
claim L6: 1 = 1 /\ 3 = 3. apply andI. reflexivity. reflexivity.
apply eq_i_tra (color_xor 1 3) (if 3 = 0 then 1
       else if 1 = 3 then 0
       else if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) 2.
- exact If_i_0 (1 = 0) 3 (if 3 = 0 then 1
       else if 1 = 3 then 0
       else if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 3 = 0 then 1
       else if 1 = 3 then 0
       else if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) (if 1 = 3 then 0
       else if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) 2.
  + exact If_i_0 (3 = 0) 1 (if 1 = 3 then 0
       else if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) L2.
  + apply eq_i_tra (if 1 = 3 then 0
       else if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) (if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) 2.
    * exact If_i_0 (1 = 3) 0 (if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) L3.
    * apply eq_i_tra (if 1 = 1 /\ 3 = 2 then 3
       else if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) (if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) 2.
      { exact If_i_0 (1 = 1 /\ 3 = 2) 3 (if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) L4. }
      { apply eq_i_tra (if 1 = 2 /\ 3 = 1 then 3
       else if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) (if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) 2.
        { exact If_i_0 (1 = 2 /\ 3 = 1) 3 (if 1 = 1 /\ 3 = 3 then 2
       else if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) L5. }
        { exact If_i_1 (1 = 1 /\ 3 = 3) 2 (if 1 = 3 /\ 3 = 1 then 2
       else if 1 = 2 /\ 3 = 3 then 1
       else if 1 = 3 /\ 3 = 2 then 1
       else 0) L6. } }
Qed.

Theorem xor_3_1 : color_xor 3 1 = 2.
claim L1: ~(3 = 0). exact neq_3_0.
claim L2: ~(1 = 0). exact neq_1_0.
claim L3: ~(3 = 1). exact neq_3_1.
claim L4: ~(3 = 1 /\ 1 = 2).
  assume H. apply H. assume H1: 3 = 1. assume H2: 1 = 2. exact L3 H1.
claim L5: ~(3 = 2 /\ 1 = 1).
  assume H. apply H. assume H1: 3 = 2. assume H2: 1 = 1. exact neq_3_2 H1.
claim L6: ~(3 = 1 /\ 1 = 3).
  assume H. apply H. assume H1: 3 = 1. assume H2: 1 = 3. exact L3 H1.
claim L7: 3 = 3 /\ 1 = 1. apply andI. reflexivity. reflexivity.
apply eq_i_tra (color_xor 3 1) (if 1 = 0 then 3
       else if 3 = 1 then 0
       else if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) 2.
- exact If_i_0 (3 = 0) 1 (if 1 = 0 then 3
       else if 3 = 1 then 0
       else if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 1 = 0 then 3
       else if 3 = 1 then 0
       else if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) (if 3 = 1 then 0
       else if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) 2.
  + exact If_i_0 (1 = 0) 3 (if 3 = 1 then 0
       else if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) L2.
  + apply eq_i_tra (if 3 = 1 then 0
       else if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) (if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) 2.
    * exact If_i_0 (3 = 1) 0 (if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) L3.
    * apply eq_i_tra (if 3 = 1 /\ 1 = 2 then 3
       else if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) (if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) 2.
      { exact If_i_0 (3 = 1 /\ 1 = 2) 3 (if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) L4. }
      { apply eq_i_tra (if 3 = 2 /\ 1 = 1 then 3
       else if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) (if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) 2.
        { exact If_i_0 (3 = 2 /\ 1 = 1) 3 (if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) L5. }
        { apply eq_i_tra (if 3 = 1 /\ 1 = 3 then 2
       else if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) (if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) 2.
          { exact If_i_0 (3 = 1 /\ 1 = 3) 2 (if 3 = 3 /\ 1 = 1 then 2
       else if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) L6. }
          { exact If_i_1 (3 = 3 /\ 1 = 1) 2 (if 3 = 2 /\ 1 = 3 then 1
       else if 3 = 3 /\ 1 = 2 then 1
       else 0) L7. } } }
Qed.

Theorem xor_2_3 : color_xor 2 3 = 1.
claim L1: ~(2 = 0). exact neq_2_0.
claim L2: ~(3 = 0). exact neq_3_0.
claim L3: ~(2 = 3).
  assume H: 2 = 3.
  claim H': 3 = 2.
    let Q:set->set->prop.
    assume HQ: Q 3 2.
    exact H (fun a b:set => Q b a) HQ.
  exact neq_3_2 H'.
claim L4: ~(2 = 1 /\ 3 = 2).
  assume H. apply H. assume H1: 2 = 1. assume H2: 3 = 2. exact neq_2_1 H1.
claim L5: ~(2 = 2 /\ 3 = 1).
  assume H. apply H. assume H1: 2 = 2. assume H2: 3 = 1. exact neq_3_1 H2.
claim L6: ~(2 = 1 /\ 3 = 3).
  assume H. apply H. assume H1: 2 = 1. assume H2: 3 = 3. exact neq_2_1 H1.
claim L7: ~(2 = 3 /\ 3 = 1).
  assume H. apply H. assume H1: 2 = 3. assume H2: 3 = 1. exact L3 H1.
claim L8: 2 = 2 /\ 3 = 3. apply andI. reflexivity. reflexivity.
apply eq_i_tra (color_xor 2 3) (if 3 = 0 then 2
       else if 2 = 3 then 0
       else if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) 1.
- exact If_i_0 (2 = 0) 3 (if 3 = 0 then 2
       else if 2 = 3 then 0
       else if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 3 = 0 then 2
       else if 2 = 3 then 0
       else if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) (if 2 = 3 then 0
       else if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) 1.
  + exact If_i_0 (3 = 0) 2 (if 2 = 3 then 0
       else if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) L2.
  + apply eq_i_tra (if 2 = 3 then 0
       else if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) (if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) 1.
    * exact If_i_0 (2 = 3) 0 (if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) L3.
    * apply eq_i_tra (if 2 = 1 /\ 3 = 2 then 3
       else if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) (if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) 1.
      { exact If_i_0 (2 = 1 /\ 3 = 2) 3 (if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) L4. }
      { apply eq_i_tra (if 2 = 2 /\ 3 = 1 then 3
       else if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) (if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) 1.
        { exact If_i_0 (2 = 2 /\ 3 = 1) 3 (if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) L5. }
        { apply eq_i_tra (if 2 = 1 /\ 3 = 3 then 2
       else if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) (if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) 1.
          { exact If_i_0 (2 = 1 /\ 3 = 3) 2 (if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) L6. }
          { apply eq_i_tra (if 2 = 3 /\ 3 = 1 then 2
       else if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) (if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) 1.
            { exact If_i_0 (2 = 3 /\ 3 = 1) 2 (if 2 = 2 /\ 3 = 3 then 1
       else if 2 = 3 /\ 3 = 2 then 1
       else 0) L7. }
            { exact If_i_1 (2 = 2 /\ 3 = 3) 1 (if 2 = 3 /\ 3 = 2 then 1
       else 0) L8. } } } }
Qed.

Theorem xor_3_2 : color_xor 3 2 = 1.
claim L1: ~(3 = 0). exact neq_3_0.
claim L2: ~(2 = 0). exact neq_2_0.
claim L3: ~(3 = 2). exact neq_3_2.
claim L4: ~(3 = 1 /\ 2 = 2).
  assume H. apply H. assume H1: 3 = 1. assume H2: 2 = 2. exact neq_3_1 H1.
claim L5: ~(3 = 2 /\ 2 = 1).
  assume H. apply H. assume H1: 3 = 2. assume H2: 2 = 1. exact L3 H1.
claim L6: ~(3 = 1 /\ 2 = 3).
  assume H. apply H. assume H1: 3 = 1. assume H2: 2 = 3. exact neq_3_1 H1.
claim L7: ~(3 = 3 /\ 2 = 1).
  assume H. apply H. assume H1: 3 = 3. assume H2: 2 = 1. exact neq_2_1 H2.
claim L8: ~(3 = 2 /\ 2 = 3).
  assume H. apply H. assume H1: 3 = 2. assume H2: 2 = 3. exact L3 H1.
claim L9: 3 = 3 /\ 2 = 2. apply andI. reflexivity. reflexivity.
apply eq_i_tra (color_xor 3 2) (if 2 = 0 then 3
       else if 3 = 2 then 0
       else if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) 1.
- exact If_i_0 (3 = 0) 2 (if 2 = 0 then 3
       else if 3 = 2 then 0
       else if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) L1.
- apply eq_i_tra (if 2 = 0 then 3
       else if 3 = 2 then 0
       else if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) (if 3 = 2 then 0
       else if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) 1.
  + exact If_i_0 (2 = 0) 3 (if 3 = 2 then 0
       else if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) L2.
  + apply eq_i_tra (if 3 = 2 then 0
       else if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) (if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) 1.
    * exact If_i_0 (3 = 2) 0 (if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) L3.
    * apply eq_i_tra (if 3 = 1 /\ 2 = 2 then 3
       else if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) (if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) 1.
      { exact If_i_0 (3 = 1 /\ 2 = 2) 3 (if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) L4. }
      { apply eq_i_tra (if 3 = 2 /\ 2 = 1 then 3
       else if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) (if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) 1.
        { exact If_i_0 (3 = 2 /\ 2 = 1) 3 (if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) L5. }
        { apply eq_i_tra (if 3 = 1 /\ 2 = 3 then 2
       else if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) (if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) 1.
          { exact If_i_0 (3 = 1 /\ 2 = 3) 2 (if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) L6. }
          { apply eq_i_tra (if 3 = 3 /\ 2 = 1 then 2
       else if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) (if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) 1.
            { exact If_i_0 (3 = 3 /\ 2 = 1) 2 (if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) L7. }
            { apply eq_i_tra (if 3 = 2 /\ 2 = 3 then 1
       else if 3 = 3 /\ 2 = 2 then 1
       else 0) (if 3 = 3 /\ 2 = 2 then 1
       else 0) 1.
              { exact If_i_0 (3 = 2 /\ 2 = 3) 1 (if 3 = 3 /\ 2 = 2 then 1
       else 0) L8. }
              { exact If_i_1 (3 = 3 /\ 2 = 2) 1 0 L9. } } } } }
Qed.

Definition Chain : (set -> set) -> prop := fun c => forall e:set, is_color (c e).

Definition zeroChain : set -> set := fun e:set => 0.

Definition chain_xor : (set -> set) -> (set -> set) -> (set -> set) :=
  fun x y e => color_xor (x e) (y e).

Definition indicator : (set -> prop) -> set -> (set -> set) :=
  fun S c e => if S e then c else 0.

Definition support : (set -> set) -> (set -> prop) :=
  fun x e => x e <> 0.

Theorem zeroChain_is_chain : Chain zeroChain.
let e.
prove is_color 0.
exact Zero_is_color.
Qed.

Theorem xor_0_0_in_4 : color_xor 0 0 :e 4.
claim L: color_xor 0 0 = 0. exact xor_0_0.
exact L (fun a b => b :e 4) In_0_4.
Qed.

Theorem xor_0_1_in_4 : color_xor 0 1 :e 4.
claim L: color_xor 0 1 = 1. exact xor_zero_l 1.
exact L (fun a b => b :e 4) In_1_4.
Qed.

Theorem xor_0_2_in_4 : color_xor 0 2 :e 4.
claim L: color_xor 0 2 = 2. exact xor_zero_l 2.
exact L (fun a b => b :e 4) In_2_4.
Qed.

Theorem xor_0_3_in_4 : color_xor 0 3 :e 4.
claim L: color_xor 0 3 = 3. exact xor_zero_l 3.
exact L (fun a b => b :e 4) In_3_4.
Qed.

Theorem xor_0_c : forall c:set, c :e 4 -> color_xor 0 c :e 4.
let c.
assume H: c :e 4.
exact cases_4 c H (fun x => color_xor 0 x :e 4) xor_0_0_in_4 xor_0_1_in_4 xor_0_2_in_4 xor_0_3_in_4.
Qed.

Theorem xor_1_0_in_4 : color_xor 1 0 :e 4.
claim L: color_xor 1 0 = 1. exact xor_1_0.
exact L (fun a b => b :e 4) In_1_4.
Qed.

Theorem xor_1_1_in_4 : color_xor 1 1 :e 4.
claim L: color_xor 1 1 = 0. exact xor_1_1.
exact L (fun a b => b :e 4) In_0_4.
Qed.

Theorem xor_1_2_in_4 : color_xor 1 2 :e 4.
claim L: color_xor 1 2 = 3. exact xor_1_2.
exact L (fun a b => b :e 4) In_3_4.
Qed.

Theorem xor_1_3_in_4 : color_xor 1 3 :e 4.
claim L: color_xor 1 3 = 2. exact xor_1_3.
exact L (fun a b => b :e 4) In_2_4.
Qed.

Theorem xor_1_c : forall c:set, c :e 4 -> color_xor 1 c :e 4.
let c.
assume H: c :e 4.
exact cases_4 c H (fun x => color_xor 1 x :e 4) xor_1_0_in_4 xor_1_1_in_4 xor_1_2_in_4 xor_1_3_in_4.
Qed.

Theorem xor_2_0_in_4 : color_xor 2 0 :e 4.
claim L: color_xor 2 0 = 2. exact xor_2_0.
exact L (fun a b => b :e 4) In_2_4.
Qed.

Theorem xor_2_1_in_4 : color_xor 2 1 :e 4.
claim L: color_xor 2 1 = 3. exact xor_2_1.
exact L (fun a b => b :e 4) In_3_4.
Qed.

Theorem xor_2_2_in_4 : color_xor 2 2 :e 4.
claim L: color_xor 2 2 = 0. exact xor_2_2.
exact L (fun a b => b :e 4) In_0_4.
Qed.

Theorem xor_2_3_in_4 : color_xor 2 3 :e 4.
claim L: color_xor 2 3 = 1. exact xor_2_3.
exact L (fun a b => b :e 4) In_1_4.
Qed.

Theorem xor_2_c : forall c:set, c :e 4 -> color_xor 2 c :e 4.
let c.
assume H: c :e 4.
exact cases_4 c H (fun x => color_xor 2 x :e 4) xor_2_0_in_4 xor_2_1_in_4 xor_2_2_in_4 xor_2_3_in_4.
Qed.

Theorem xor_3_0_in_4 : color_xor 3 0 :e 4.
claim L: color_xor 3 0 = 3. exact xor_3_0.
exact L (fun a b => b :e 4) In_3_4.
Qed.

Theorem xor_3_1_in_4 : color_xor 3 1 :e 4.
claim L: color_xor 3 1 = 2. exact xor_3_1.
exact L (fun a b => b :e 4) In_2_4.
Qed.

Theorem xor_3_2_in_4 : color_xor 3 2 :e 4.
claim L: color_xor 3 2 = 1. exact xor_3_2.
exact L (fun a b => b :e 4) In_1_4.
Qed.

Theorem xor_3_3_in_4 : color_xor 3 3 :e 4.
claim L: color_xor 3 3 = 0. exact xor_3_3.
exact L (fun a b => b :e 4) In_0_4.
Qed.

Theorem xor_3_c : forall c:set, c :e 4 -> color_xor 3 c :e 4.
let c.
assume H: c :e 4.
exact cases_4 c H (fun x => color_xor 3 x :e 4) xor_3_0_in_4 xor_3_1_in_4 xor_3_2_in_4 xor_3_3_in_4.
Qed.

Theorem xor_closed : forall c1 c2:set, is_color c1 -> is_color c2 -> is_color (color_xor c1 c2).
let c1. let c2.
assume H1: is_color c1.
assume H2: is_color c2.
exact cases_4 c1 H1 (fun x => color_xor x c2 :e 4) (xor_0_c c2 H2) (xor_1_c c2 H2) (xor_2_c c2 H2) (xor_3_c c2 H2).
Qed.

Theorem chain_xor_preserves : forall x y:set -> set,
  Chain x -> Chain y -> Chain (chain_xor x y).
let x. let y.
assume Hx: Chain x.
assume Hy: Chain y.
let e.
prove is_color (chain_xor x y e).
prove is_color (color_xor (x e) (y e)).
apply xor_closed.
- exact Hx e.
- exact Hy e.
Qed.

Theorem xor_zero_r : forall c:set, c :e 4 -> color_xor c 0 = c.
let c.
assume H: c :e 4.
exact cases_4 c H (fun x => color_xor x 0 = x) xor_0_0 xor_1_0 xor_2_0 xor_3_0.
Qed.

Theorem xor_zero_r_general : forall c:set, color_xor c 0 = c.
let c.
claim Heq: 0 = 0. reflexivity.
prove (if c = 0 then 0
       else if 0 = 0 then c
       else if c = 0 then 0
       else if c = 1 /\ 0 = 2 then 3
       else if c = 2 /\ 0 = 1 then 3
       else if c = 1 /\ 0 = 3 then 2
       else if c = 3 /\ 0 = 1 then 2
       else if c = 2 /\ 0 = 3 then 1
       else if c = 3 /\ 0 = 2 then 1
       else 0) = c.
claim Lem: forall p:prop, p \/ ~p. exact xm.
apply Lem (c = 0).
- assume Hc0: c = 0.
  apply eq_i_tra (if c = 0 then 0
       else if 0 = 0 then c
       else if c = 0 then 0
       else if c = 1 /\ 0 = 2 then 3
       else if c = 2 /\ 0 = 1 then 3
       else if c = 1 /\ 0 = 3 then 2
       else if c = 3 /\ 0 = 1 then 2
       else if c = 2 /\ 0 = 3 then 1
       else if c = 3 /\ 0 = 2 then 1
       else 0) 0 c.
  + exact If_i_1 (c = 0) 0 (if 0 = 0 then c
       else if c = 0 then 0
       else if c = 1 /\ 0 = 2 then 3
       else if c = 2 /\ 0 = 1 then 3
       else if c = 1 /\ 0 = 3 then 2
       else if c = 3 /\ 0 = 1 then 2
       else if c = 2 /\ 0 = 3 then 1
       else if c = 3 /\ 0 = 2 then 1
       else 0) Hc0.
  + exact Hc0 (fun a b => a = b) Hc0.
- assume Hcn0: ~(c = 0).
  apply eq_i_tra (if c = 0 then 0
       else if 0 = 0 then c
       else if c = 0 then 0
       else if c = 1 /\ 0 = 2 then 3
       else if c = 2 /\ 0 = 1 then 3
       else if c = 1 /\ 0 = 3 then 2
       else if c = 3 /\ 0 = 1 then 2
       else if c = 2 /\ 0 = 3 then 1
       else if c = 3 /\ 0 = 2 then 1
       else 0) (if 0 = 0 then c
       else if c = 0 then 0
       else if c = 1 /\ 0 = 2 then 3
       else if c = 2 /\ 0 = 1 then 3
       else if c = 1 /\ 0 = 3 then 2
       else if c = 3 /\ 0 = 1 then 2
       else if c = 2 /\ 0 = 3 then 1
       else if c = 3 /\ 0 = 2 then 1
       else 0) c.
  + exact If_i_0 (c = 0) 0 (if 0 = 0 then c
       else if c = 0 then 0
       else if c = 1 /\ 0 = 2 then 3
       else if c = 2 /\ 0 = 1 then 3
       else if c = 1 /\ 0 = 3 then 2
       else if c = 3 /\ 0 = 1 then 2
       else if c = 2 /\ 0 = 3 then 1
       else if c = 3 /\ 0 = 2 then 1
       else 0) Hcn0.
  + exact If_i_1 (0 = 0) c (if c = 0 then 0
       else if c = 1 /\ 0 = 2 then 3
       else if c = 2 /\ 0 = 1 then 3
       else if c = 1 /\ 0 = 3 then 2
       else if c = 3 /\ 0 = 1 then 2
       else if c = 2 /\ 0 = 3 then 1
       else if c = 3 /\ 0 = 2 then 1
       else 0) Heq.
Qed.

Theorem chain_xor_zero_r : forall x:set -> set, chain_xor x zeroChain = x.
let x.
apply func_ext set set.
let e.
prove chain_xor x zeroChain e = x e.
prove color_xor (x e) 0 = x e.
exact xor_zero_r_general (x e).
Qed.

Theorem xor_self_general : forall c:set, color_xor c c = 0.
let c.
claim Heq: c = c. reflexivity.
prove (if c = 0 then c
       else if c = 0 then c
       else if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) = 0.
claim Lem: forall p:prop, p \/ ~p. exact xm.
apply Lem (c = 0).
- assume Hc0: c = 0.
  apply eq_i_tra (if c = 0 then c
       else if c = 0 then c
       else if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) c 0.
  + exact If_i_1 (c = 0) c (if c = 0 then c
       else if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) Hc0.
  + exact Hc0.
- assume Hcn0: ~(c = 0).
  apply eq_i_tra (if c = 0 then c
       else if c = 0 then c
       else if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) (if c = 0 then c
       else if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) 0.
  + exact If_i_0 (c = 0) c (if c = 0 then c
       else if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) Hcn0.
  + apply eq_i_tra (if c = 0 then c
       else if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) (if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) 0.
    * exact If_i_0 (c = 0) c (if c = c then 0
       else if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) Hcn0.
    * exact If_i_1 (c = c) 0 (if c = 1 /\ c = 2 then 3
       else if c = 2 /\ c = 1 then 3
       else if c = 1 /\ c = 3 then 2
       else if c = 3 /\ c = 1 then 2
       else if c = 2 /\ c = 3 then 1
       else if c = 3 /\ c = 2 then 1
       else 0) Heq.
Qed.

Theorem chain_xor_self : forall x:set -> set, chain_xor x x = zeroChain.
let x.
apply func_ext set set.
let e.
prove chain_xor x x e = zeroChain e.
prove color_xor (x e) (x e) = 0.
exact xor_self_general (x e).
Qed.

Definition symm_diff : (set -> prop) -> (set -> prop) -> (set -> prop) :=
  fun S T e => (S e /\ ~T e) \/ (T e /\ ~S e).

Theorem indicator_at_in : forall S:set -> prop, forall c e:set,
  S e -> indicator S c e = c.
let S. let c. let e.
assume H: S e.
prove (if S e then c else 0) = c.
claim L1: S e. exact H.
exact If_i_1 (S e) c 0 L1.
Qed.

Theorem indicator_at_out : forall S:set -> prop, forall c e:set,
  ~S e -> indicator S c e = 0.
let S. let c. let e.
assume H: ~S e.
prove (if S e then c else 0) = 0.
exact If_i_0 (S e) c 0 H.
Qed.

Theorem indicator_xor_symm_diff :
  forall S T:set -> prop, forall c:set,
    chain_xor (indicator S c) (indicator T c) = indicator (symm_diff S T) c.
let S. let T. let c.
apply func_ext set set.
let e.
prove chain_xor (indicator S c) (indicator T c) e = indicator (symm_diff S T) c e.
prove color_xor (indicator S c e) (indicator T c e) = (if symm_diff S T e then c else 0).
claim Lem: forall p:prop, p \/ ~p. exact xm.
apply Lem (S e).
- assume HS: S e.
  apply Lem (T e).
  + assume HT: T e.
    claim Lindic_S: indicator S c e = c. exact indicator_at_in S c e HS.
    claim Lindic_T: indicator T c e = c. exact indicator_at_in T c e HT.
    claim Lxor: color_xor c c = 0. exact xor_self_general c.
    claim Lsymm: ~symm_diff S T e.
    { prove ~((S e /\ ~T e) \/ (T e /\ ~S e)).
      assume H: (S e /\ ~T e) \/ (T e /\ ~S e).
      apply H.
      * assume H1: S e /\ ~T e.
        apply H1. assume HSe: S e. assume HnT: ~T e. exact HnT HT.
      * assume H2: T e /\ ~S e.
        apply H2. assume HTe: T e. assume HnS: ~S e. exact HnS HS. }
    claim Lrhs: (if symm_diff S T e then c else 0) = 0. exact If_i_0 (symm_diff S T e) c 0 Lsymm.
    apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) 0 (if symm_diff S T e then c else 0).
    * claim L1: color_xor (indicator S c e) (indicator T c e) = color_xor c (indicator T c e).
        let R. assume HR: R (color_xor (indicator S c e) (indicator T c e)) (color_xor c (indicator T c e)).
        exact Lindic_S (fun a b => R (color_xor a (indicator T c e)) (color_xor b (indicator T c e))) HR.
      claim L2: color_xor c (indicator T c e) = color_xor c c.
        let R. assume HR: R (color_xor c (indicator T c e)) (color_xor c c).
        exact Lindic_T (fun a b => R (color_xor c a) (color_xor c b)) HR.
      apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) (color_xor c (indicator T c e)) 0.
      { exact L1. }
      { apply eq_i_tra (color_xor c (indicator T c e)) (color_xor c c) 0.
        { exact L2. }
        { exact Lxor. } }
    * exact Lrhs (fun a b => a = b) Lrhs.
  + assume HnT: ~T e.
    claim Lindic_S: indicator S c e = c. exact indicator_at_in S c e HS.
    claim Lindic_T: indicator T c e = 0. exact indicator_at_out T c e HnT.
    claim Lxor: color_xor c 0 = c. exact xor_zero_r_general c.
    claim Lsymm: symm_diff S T e.
      prove (S e /\ ~T e) \/ (T e /\ ~S e).
      apply orIL.
      apply andI. exact HS. exact HnT.
    claim Lrhs: (if symm_diff S T e then c else 0) = c. exact If_i_1 (symm_diff S T e) c 0 Lsymm.
    apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) c (if symm_diff S T e then c else 0).
    * claim L1: color_xor (indicator S c e) (indicator T c e) = color_xor c (indicator T c e).
        let R. assume HR: R (color_xor (indicator S c e) (indicator T c e)) (color_xor c (indicator T c e)).
        exact Lindic_S (fun a b => R (color_xor a (indicator T c e)) (color_xor b (indicator T c e))) HR.
      claim L2: color_xor c (indicator T c e) = color_xor c 0.
        let R. assume HR: R (color_xor c (indicator T c e)) (color_xor c 0).
        exact Lindic_T (fun a b => R (color_xor c a) (color_xor c b)) HR.
      apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) (color_xor c 0) c.
      { apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) (color_xor c (indicator T c e)) (color_xor c 0).
        { exact L1. }
        { exact L2. } }
      { exact Lxor. }
    * exact Lrhs (fun a b => a = b) Lrhs.
- assume HnS: ~S e.
  apply Lem (T e).
  + assume HT: T e.
    claim Lindic_S: indicator S c e = 0. exact indicator_at_out S c e HnS.
    claim Lindic_T: indicator T c e = c. exact indicator_at_in T c e HT.
    claim Lxor: color_xor 0 c = c. exact xor_zero_l c.
    claim Lsymm: symm_diff S T e.
      prove (S e /\ ~T e) \/ (T e /\ ~S e).
      apply orIR.
      apply andI. exact HT. exact HnS.
    claim Lrhs: (if symm_diff S T e then c else 0) = c. exact If_i_1 (symm_diff S T e) c 0 Lsymm.
    apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) c (if symm_diff S T e then c else 0).
    * claim L1: color_xor (indicator S c e) (indicator T c e) = color_xor 0 (indicator T c e).
        let R. assume HR: R (color_xor (indicator S c e) (indicator T c e)) (color_xor 0 (indicator T c e)).
        exact Lindic_S (fun a b => R (color_xor a (indicator T c e)) (color_xor b (indicator T c e))) HR.
      claim L2: color_xor 0 (indicator T c e) = color_xor 0 c.
        let R. assume HR: R (color_xor 0 (indicator T c e)) (color_xor 0 c).
        exact Lindic_T (fun a b => R (color_xor 0 a) (color_xor 0 b)) HR.
      apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) (color_xor 0 c) c.
      { apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) (color_xor 0 (indicator T c e)) (color_xor 0 c).
        { exact L1. }
        { exact L2. } }
      { exact Lxor. }
    * exact Lrhs (fun a b => a = b) Lrhs.
  + assume HnT: ~T e.
    claim Lindic_S: indicator S c e = 0. exact indicator_at_out S c e HnS.
    claim Lindic_T: indicator T c e = 0. exact indicator_at_out T c e HnT.
    claim Lxor: color_xor 0 0 = 0. exact xor_0_0.
    claim Lsymm: ~symm_diff S T e.
    { prove ~((S e /\ ~T e) \/ (T e /\ ~S e)).
      assume H: (S e /\ ~T e) \/ (T e /\ ~S e).
      apply H.
      * assume H1: S e /\ ~T e.
        apply H1. assume HSe: S e. assume HnTe: ~T e. exact HnS HSe.
      * assume H2: T e /\ ~S e.
        apply H2. assume HTe: T e. assume HnSe: ~S e. exact HnT HTe. }
    claim Lrhs: (if symm_diff S T e then c else 0) = 0. exact If_i_0 (symm_diff S T e) c 0 Lsymm.
    apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) 0 (if symm_diff S T e then c else 0).
    * claim L1: color_xor (indicator S c e) (indicator T c e) = color_xor 0 (indicator T c e).
        let R. assume HR: R (color_xor (indicator S c e) (indicator T c e)) (color_xor 0 (indicator T c e)).
        exact Lindic_S (fun a b => R (color_xor a (indicator T c e)) (color_xor b (indicator T c e))) HR.
      claim L2: color_xor 0 (indicator T c e) = color_xor 0 0.
        let R. assume HR: R (color_xor 0 (indicator T c e)) (color_xor 0 0).
        exact Lindic_T (fun a b => R (color_xor 0 a) (color_xor 0 b)) HR.
      apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) (color_xor 0 0) 0.
      { apply eq_i_tra (color_xor (indicator S c e) (indicator T c e)) (color_xor 0 (indicator T c e)) (color_xor 0 0).
        { exact L1. }
        { exact L2. } }
      { exact Lxor. }
    * exact Lrhs (fun a b => a = b) Lrhs.
Qed.

Definition union_set : (set -> prop) -> (set -> prop) -> (set -> prop) :=
  fun S T e => S e \/ T e.

Definition disjoint : (set -> prop) -> (set -> prop) -> prop :=
  fun S T => forall e:set, ~(S e /\ T e).

Theorem symm_diff_with_common_prefix :
  forall R A A':set -> prop,
    disjoint R A -> disjoint R A' -> disjoint A A' ->
    symm_diff (union_set R A) (union_set R A') = union_set A A'.
let R. let A. let A'.
assume H_RA: disjoint R A.
assume H_RA': disjoint R A'.
assume H_AA': disjoint A A'.
prove (fun e:set => (union_set R A e /\ ~union_set R A' e) \/ (union_set R A' e /\ ~union_set R A e))
    = (fun e:set => A e \/ A' e).
apply pred_ext.
let e.
prove ((union_set R A e /\ ~union_set R A' e) \/ (union_set R A' e /\ ~union_set R A e))
  <-> (A e \/ A' e).
apply iffI.
- assume H: (union_set R A e /\ ~union_set R A' e) \/ (union_set R A' e /\ ~union_set R A e).
  prove A e \/ A' e.
  apply H.
  * assume H1: union_set R A e /\ ~union_set R A' e.
    apply H1.
    assume Hin: union_set R A e.
    assume Hout: ~union_set R A' e.
    apply Hin.
    + assume HR: R e.
      claim Hcontra: ~union_set R A' e. exact Hout.
      prove False.
      apply Hcontra.
      prove R e \/ A' e.
      apply orIL. exact HR.
    + assume HA: A e.
      apply orIL. exact HA.
  * assume H2: union_set R A' e /\ ~union_set R A e.
    apply H2.
    assume Hin: union_set R A' e.
    assume Hout: ~union_set R A e.
    apply Hin.
    + assume HR: R e.
      claim Hcontra: ~union_set R A e. exact Hout.
      prove False.
      apply Hcontra.
      prove R e \/ A e.
      apply orIL. exact HR.
    + assume HA': A' e.
      apply orIR. exact HA'.
- assume H: A e \/ A' e.
  prove (union_set R A e /\ ~union_set R A' e) \/ (union_set R A' e /\ ~union_set R A e).
  apply H.
  * assume HA: A e.
    apply orIL.
    apply andI.
    + prove union_set R A e. prove R e \/ A e. apply orIR. exact HA.
    + prove ~union_set R A' e.
      assume Hcontra: union_set R A' e.
      apply Hcontra.
      - assume HR: R e.
        claim Hdisj: ~(R e /\ A e). exact H_RA e.
        apply Hdisj. apply andI. exact HR. exact HA.
      - assume HA': A' e.
        claim Hdisj: ~(A e /\ A' e). exact H_AA' e.
        apply Hdisj. apply andI. exact HA. exact HA'.
  * assume HA': A' e.
    apply orIR.
    apply andI.
    + prove union_set R A' e. prove R e \/ A' e. apply orIR. exact HA'.
    + prove ~union_set R A e.
      assume Hcontra: union_set R A e.
      apply Hcontra.
      - assume HR: R e.
        claim Hdisj: ~(R e /\ A' e). exact H_RA' e.
        apply Hdisj. apply andI. exact HR. exact HA'.
      - assume HA: A e.
        claim Hdisj: ~(A e /\ A' e). exact H_AA' e.
        apply Hdisj. apply andI. exact HA. exact HA'.
Qed.

Definition X_in_C : set -> (set -> prop) -> (set -> prop) -> (set -> set) :=
  fun gamma R A => indicator (union_set R A) gamma.

Definition X_in_CR : set -> (set -> prop) -> (set -> prop) -> (set -> set) :=
  fun gamma R A' => indicator (union_set R A') gamma.

Definition kc_interior : (set -> prop) -> (set -> prop) -> (set -> prop) :=
  fun A A' => union_set A A'.

Theorem per_run_xor_is_interior :
  forall gamma:set, forall R A A':set -> prop,
    disjoint R A -> disjoint R A' -> disjoint A A' ->
    chain_xor (X_in_C gamma R A) (X_in_CR gamma R A')
    = indicator (kc_interior A A') gamma.
let gamma. let R. let A. let A'.
assume H_RA: disjoint R A.
assume H_RA': disjoint R A'.
assume H_AA': disjoint A A'.
prove chain_xor (indicator (union_set R A) gamma) (indicator (union_set R A') gamma)
    = indicator (union_set A A') gamma.
claim L1: chain_xor (indicator (union_set R A) gamma) (indicator (union_set R A') gamma)
        = indicator (symm_diff (union_set R A) (union_set R A')) gamma.
  exact indicator_xor_symm_diff (union_set R A) (union_set R A') gamma.
claim L2: symm_diff (union_set R A) (union_set R A') = union_set A A'.
  exact symm_diff_with_common_prefix R A A' H_RA H_RA' H_AA'.
apply func_ext set set.
let e.
prove chain_xor (indicator (union_set R A) gamma) (indicator (union_set R A') gamma) e = indicator (union_set A A') gamma e.
claim L1e: chain_xor (indicator (union_set R A) gamma) (indicator (union_set R A') gamma) e
         = indicator (symm_diff (union_set R A) (union_set R A')) gamma e.
{ let R'. assume HR': R' (chain_xor (indicator (union_set R A) gamma) (indicator (union_set R A') gamma) e)
                        (indicator (symm_diff (union_set R A) (union_set R A')) gamma e).
  exact L1 (fun a b => R' (a e) (b e)) HR'. }
claim L2e: symm_diff (union_set R A) (union_set R A') e = union_set A A' e.
{ let R'. assume HR': R' (symm_diff (union_set R A) (union_set R A') e) (union_set A A' e).
  exact L2 (fun a b => R' (a e) (b e)) HR'. }
claim L3e: indicator (symm_diff (union_set R A) (union_set R A')) gamma e = indicator (union_set A A') gamma e.
{ prove (if symm_diff (union_set R A) (union_set R A') e then gamma else 0) = (if union_set A A' e then gamma else 0).
  claim Lem: forall p:prop, p \/ ~p. exact xm.
  apply Lem (symm_diff (union_set R A) (union_set R A') e).
  - assume Hsymm: symm_diff (union_set R A) (union_set R A') e.
    claim Hunion: union_set A A' e. exact L2e (fun a b => a) Hsymm.
    apply eq_i_tra (if symm_diff (union_set R A) (union_set R A') e then gamma else 0) gamma (if union_set A A' e then gamma else 0).
    { exact If_i_1 (symm_diff (union_set R A) (union_set R A') e) gamma 0 Hsymm. }
    { claim L: (if union_set A A' e then gamma else 0) = gamma. exact If_i_1 (union_set A A' e) gamma 0 Hunion.
      exact L (fun a b => a = b) L. }
  - assume HnSymm: ~symm_diff (union_set R A) (union_set R A') e.
    claim HnUnion: ~union_set A A' e.
    { assume Hu: union_set A A' e.
      claim Hsymm: symm_diff (union_set R A) (union_set R A') e. exact L2e (fun a b => b) Hu.
      exact HnSymm Hsymm. }
    apply eq_i_tra (if symm_diff (union_set R A) (union_set R A') e then gamma else 0) 0 (if union_set A A' e then gamma else 0).
    { exact If_i_0 (symm_diff (union_set R A) (union_set R A') e) gamma 0 HnSymm. }
    { claim L: (if union_set A A' e then gamma else 0) = 0. exact If_i_0 (union_set A A' e) gamma 0 HnUnion.
      exact L (fun a b => a = b) L. } }
apply eq_i_tra (chain_xor (indicator (union_set R A) gamma) (indicator (union_set R A') gamma) e)
              (indicator (symm_diff (union_set R A) (union_set R A')) gamma e)
              (indicator (union_set A A') gamma e).
{ exact L1e. }
{ exact L3e. }
Qed.

Theorem per_run_diff_zero_on_run :
  forall gamma:set, forall R A A':set -> prop, forall e:set,
    gamma <> 0 ->
    disjoint R A -> disjoint R A' -> disjoint A A' ->
    R e ->
    (chain_xor (X_in_C gamma R A) (X_in_CR gamma R A')) e = 0.
let gamma. let R. let A. let A'. let e.
assume Hgamma: gamma <> 0.
assume H_RA: disjoint R A.
assume H_RA': disjoint R A'.
assume H_AA': disjoint A A'.
assume HR: R e.
claim L1: (chain_xor (X_in_C gamma R A) (X_in_CR gamma R A'))
        = indicator (kc_interior A A') gamma.
  exact per_run_xor_is_interior gamma R A A' H_RA H_RA' H_AA'.
claim L2: ~(kc_interior A A' e).
{ prove ~(union_set A A' e).
  prove ~(A e \/ A' e).
  assume H: A e \/ A' e.
  apply H.
  - assume HA: A e.
    claim Hcontra: ~(R e /\ A e). exact H_RA e.
    apply Hcontra.
    apply andI.
    + exact HR.
    + exact HA.
  - assume HA': A' e.
    claim Hcontra: ~(R e /\ A' e). exact H_RA' e.
    apply Hcontra.
    apply andI.
    + exact HR.
    + exact HA'. }
claim L3: indicator (kc_interior A A') gamma e = 0.
  exact indicator_at_out (kc_interior A A') gamma e L2.
claim L1e: (chain_xor (X_in_C gamma R A) (X_in_CR gamma R A')) e = indicator (kc_interior A A') gamma e.
{ let R'. assume HR': R' ((chain_xor (X_in_C gamma R A) (X_in_CR gamma R A')) e) (indicator (kc_interior A A') gamma e).
  exact L1 (fun a b => R' (a e) (b e)) HR'. }
apply eq_i_tra ((chain_xor (X_in_C gamma R A) (X_in_CR gamma R A')) e) (indicator (kc_interior A A') gamma e) 0.
{ exact L1e. }
{ exact L3. }
Qed.
