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

Theorem xor_closed : forall c1 c2:set, is_color c1 -> is_color c2 -> is_color (color_xor c1 c2).
let c1. let c2.
assume H1: is_color c1.
assume H2: is_color c2.
Admitted.

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

Theorem chain_xor_zero_r : forall x:set -> set, chain_xor x zeroChain = x.
let x.
Admitted.

Theorem chain_xor_self : forall x:set -> set, chain_xor x x = zeroChain.
let x.
Admitted.

Definition symm_diff : (set -> prop) -> (set -> prop) -> (set -> prop) :=
  fun S T e => (S e /\ ~T e) \/ (T e /\ ~S e).

Theorem indicator_xor_symm_diff :
  forall S T:set -> prop, forall c:set,
    chain_xor (indicator S c) (indicator T c) = indicator (symm_diff S T) c.
Admitted.

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
Admitted.

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
Admitted.

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
  prove ~(union_set A A' e).
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
    + exact HA'.
Admitted.
