Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)).
Qed.

Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 nat_p_12.
Qed.

Theorem five_in_six : 5 :e 6.
exact ordsuccI2 5.
Qed.

Theorem nat_p_6 : nat_p 6.
exact nat_ordsucc 5 nat_p_5.
Qed.

Theorem nat_p_7 : nat_p 7.
exact nat_ordsucc 6 nat_p_6.
Qed.

Theorem ordinal_7 : ordinal 7.
exact nat_p_ordinal 7 nat_p_7.
Qed.

Theorem ordinal_12 : ordinal 12.
exact nat_p_ordinal 12 nat_p_12.
Qed.

Theorem ordinal_13 : ordinal 13.
exact nat_p_ordinal 13 nat_p_13.
Qed.

Theorem nat_p_8 : nat_p 8.
exact nat_ordsucc 7 nat_p_7.
Qed.

Theorem nat_p_9 : nat_p 9.
exact nat_ordsucc 8 nat_p_8.
Qed.

Theorem nat_p_10 : nat_p 10.
exact nat_ordsucc 9 nat_p_9.
Qed.

Theorem nat_p_11 : nat_p 11.
exact nat_ordsucc 10 nat_p_10.
Qed.

Theorem seven_in_8 : 7 :e 8.
exact ordsuccI2 7.
Qed.

Theorem seven_in_9 : 7 :e 9.
claim H8sub9: 8 c= 9.
  exact nat_trans 9 nat_p_9 8 (ordsuccI2 8).
exact H8sub9 7 seven_in_8.
Qed.

Theorem seven_in_10 : 7 :e 10.
claim H9sub10: 9 c= 10.
  exact nat_trans 10 nat_p_10 9 (ordsuccI2 9).
exact H9sub10 7 seven_in_9.
Qed.

Theorem seven_in_11 : 7 :e 11.
claim H10sub11: 10 c= 11.
  exact nat_trans 11 nat_p_11 10 (ordsuccI2 10).
exact H10sub11 7 seven_in_10.
Qed.

Theorem seven_in_12 : 7 :e 12.
claim H11sub12: 11 c= 12.
  exact nat_trans 12 nat_p_12 11 (ordsuccI2 11).
exact H11sub12 7 seven_in_11.
Qed.

Theorem six_in_7 : 6 :e 7.
exact ordsuccI2 6.
Qed.

Theorem six_in_12 : 6 :e 12.
claim H7sub12: 7 c= 12.
  exact nat_trans 12 nat_p_12 7 seven_in_12.
exact H7sub12 6 six_in_7.
Qed.

Theorem six_in_13 : 6 :e 13.
claim H12sub13: 12 c= 13.
  exact nat_trans 13 nat_p_13 12 (ordsuccI2 12).
exact H12sub13 6 six_in_12.
Qed.

Theorem pigeonhole_6_to_5 : forall f:set -> set,
  (forall i :e 6, f i :e 5) ->
  ~(forall i j :e 6, f i = f j -> i = j).
let f.
assume Hf5: forall i :e 6, f i :e 5.
exact PigeonHole_nat 5 nat_p_5 f Hf5.
Qed.

Theorem inj_13_to_5_false : forall f:set -> set,
  (forall i :e 13, f i :e 5) ->
  (forall i j :e 13, f i = f j -> i = j) ->
  False.
let f.
assume Hdom: forall i :e 13, f i :e 5.
assume Hinj: forall i j :e 13, f i = f j -> i = j.
claim H6sub13: 6 c= 13.
  let x. assume Hx: x :e 6.
  prove x :e 13.
  exact nat_trans 13 nat_p_13 6 six_in_13 x Hx.
claim Hf5_6: forall i :e 6, f i :e 5.
  let i. assume Hi: i :e 6.
  exact Hdom i (H6sub13 i Hi).
claim Hinj_6: forall i j :e 6, f i = f j -> i = j.
  let i. assume Hi: i :e 6.
  let j. assume Hj: j :e 6.
  assume Hfij: f i = f j.
  exact Hinj i (H6sub13 i Hi) j (H6sub13 j Hj) Hfij.
exact pigeonhole_6_to_5 f Hf5_6 Hinj_6.
Qed.

Theorem pigeonhole_13_5_collision_ordinals : forall f:set -> set,
  (forall i :e 13, f i :e 5) ->
  exists i j :e 13, f i = f j /\ i <> j.
let f.
assume Hdom: forall i :e 13, f i :e 5.
prove exists i j :e 13, f i = f j /\ i <> j.
apply xm (forall i j :e 13, f i = f j -> i = j).
- assume Hinj: forall i j :e 13, f i = f j -> i = j.
  claim Hfalse: False.
    exact inj_13_to_5_false f Hdom Hinj.
  exact FalseE Hfalse (exists i j :e 13, f i = f j /\ i <> j).
- assume Hnotinj: ~(forall i j :e 13, f i = f j -> i = j).
  prove exists i j :e 13, f i = f j /\ i <> j.
  apply dneg (exists i j :e 13, f i = f j /\ i <> j).
  assume Hno: ~(exists i j :e 13, f i = f j /\ i <> j).
  apply Hnotinj.
  prove forall i j :e 13, f i = f j -> i = j.
  let i. assume Hi: i :e 13.
  let j. assume Hj: j :e 13.
  assume Hfij: f i = f j.
  apply dneg (i = j).
  assume Hneq: i <> j.
  apply Hno.
  witness i.
  apply andI (i :e 13) (exists j :e 13, f i = f j /\ i <> j).
  - exact Hi.
  - witness j.
    apply andI (j :e 13) (f i = f j /\ i <> j).
    + exact Hj.
    + apply andI (f i = f j) (i <> j).
      * exact Hfij.
      * exact Hneq.
Qed.
