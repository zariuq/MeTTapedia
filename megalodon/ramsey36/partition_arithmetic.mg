Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)).
Qed.

Theorem nat_p_6 : nat_p 6.
exact nat_ordsucc 5 nat_p_5.
Qed.

Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13
      (nat_ordsucc 12 nat_p_12)))).
Qed.

Theorem in_12_17 : 12 :e 17.
prove 12 :e ordsucc 16.
apply ordsuccI1 16.
prove 12 :e 16.
apply ordsuccI1 15.
prove 12 :e 15.
apply ordsuccI1 14.
prove 12 :e 14.
apply ordsuccI1 13.
prove 12 :e 13.
exact ordsuccI2 12.
Qed.

Theorem twelve_subset_17 : 12 c= 17.
let x. assume Hx: x :e 12.
exact nat_trans 17 nat_p_17 12 in_12_17 x Hx.
Qed.

Theorem add_0_17_eq_17 : 0 + 17 = 17.
exact add_nat_0L 17 nat_p_17.
Qed.

Theorem add_1_16_eq_17 : 1 + 16 = 17.
prove 1 + ordsucc 15 = 17.
rewrite add_nat_SR 1 15 (nat_ordsucc 14 (nat_ordsucc 13 (nat_ordsucc 12 nat_p_12))).
prove ordsucc (1 + 15) = 17.
apply f_eq_i ordsucc.
prove 1 + 15 = 16.
rewrite add_nat_SR 1 14 (nat_ordsucc 13 (nat_ordsucc 12 nat_p_12)).
prove ordsucc (1 + 14) = 16.
apply f_eq_i ordsucc.
prove 1 + 14 = 15.
rewrite add_nat_SR 1 13 (nat_ordsucc 12 nat_p_12).
prove ordsucc (1 + 13) = 15.
apply f_eq_i ordsucc.
prove 1 + 13 = 14.
rewrite add_nat_SR 1 12 nat_p_12.
prove ordsucc (1 + 12) = 14.
apply f_eq_i ordsucc.
prove 1 + 12 = 13.
rewrite add_nat_SR 1 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
prove ordsucc (1 + 11) = 13.
apply f_eq_i ordsucc.
prove 1 + 11 = 12.
rewrite add_nat_SR 1 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))))).
prove ordsucc (1 + 10) = 12.
apply f_eq_i ordsucc.
prove 1 + 10 = 11.
rewrite add_nat_SR 1 9 (nat_ordsucc 8 (nat_ordsucc 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))).
prove ordsucc (1 + 9) = 11.
apply f_eq_i ordsucc.
prove 1 + 9 = 10.
rewrite add_nat_SR 1 8 (nat_ordsucc 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))).
prove ordsucc (1 + 8) = 10.
apply f_eq_i ordsucc.
prove 1 + 8 = 9.
rewrite add_nat_SR 1 7 (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))).
prove ordsucc (1 + 7) = 9.
apply f_eq_i ordsucc.
prove 1 + 7 = 8.
rewrite add_nat_SR 1 6 nat_p_6.
prove ordsucc (1 + 6) = 8.
apply f_eq_i ordsucc.
prove 1 + 6 = 7.
rewrite add_nat_SR 1 5 nat_p_5.
prove ordsucc (1 + 5) = 7.
apply f_eq_i ordsucc.
prove 1 + 5 = 6.
rewrite add_nat_SR 1 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)).
prove ordsucc (1 + 4) = 6.
apply f_eq_i ordsucc.
prove 1 + 4 = 5.
rewrite add_nat_SR 1 3 (nat_ordsucc 2 nat_2).
prove ordsucc (1 + 3) = 5.
apply f_eq_i ordsucc.
prove 1 + 3 = 4.
rewrite add_nat_SR 1 2 nat_2.
prove ordsucc (1 + 2) = 4.
apply f_eq_i ordsucc.
prove 1 + 2 = 3.
rewrite add_nat_SR 1 1 nat_1.
prove ordsucc (1 + 1) = 3.
rewrite add_nat_1_1_2.
prove ordsucc 2 = 3.
exact eq_i_refl 3.
Qed.

Theorem in_1_6 : 1 :e 6.
prove 1 :e ordsucc 5.
apply ordsuccI1 5.
prove 1 :e 5.
apply ordsuccI1 4.
prove 1 :e 4.
apply ordsuccI1 3.
prove 1 :e 3.
apply ordsuccI1 2.
prove 1 :e 2.
exact ordsuccI2 1.
Qed.

Theorem partition_case_n_eq_0 : forall V N Non:set, forall n:set,
  equip 17 V ->
  equip n N ->
  equip (17 + 0) Non ->
  n = 0 ->
  12 c= (17 + 0).
let V N Non n.
assume HeqV: equip 17 V.
assume HeqN: equip n N.
assume HeqNon: equip (17 + 0) Non.
assume Hn0: n = 0.
rewrite add_nat_0R 17.
exact twelve_subset_17.
Qed.

Theorem partition_case_n_eq_1_arithmetic : 12 c= 16.
Admitted.

Theorem partition_case_n_eq_1 : forall V N Non:set, forall n:set,
  equip 17 V ->
  equip n N ->
  equip 16 Non ->
  n = 1 ->
  exists S:set, S c= Non /\ equip 12 S.
let V N Non n.
assume HeqV: equip 17 V.
assume HeqN: equip n N.
assume HeqNon: equip 16 Non.
assume Hn1: n = 1.
claim H12_16: 12 c= 16.
  exact partition_case_n_eq_1_arithmetic.
exact equip_Subq_exists 12 16 Non H12_16 HeqNon.
Qed.

Theorem partition_17_5_implies_12_with_arithmetic : forall V N Non:set,
  equip 17 V ->
  N c= V ->
  Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  ~(exists T, T c= N /\ equip 6 T) ->
  (forall n:set, equip n N -> n :e 6 -> exists m:set, equip m Non /\ 12 c= m) ->
  exists S, S c= Non /\ equip 12 S.
Admitted.
