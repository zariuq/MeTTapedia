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
