Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 nat_p_12.
Qed.

Theorem nat_p_14 : nat_p 14.
exact nat_ordsucc 13 nat_p_13.
Qed.

Theorem nat_p_15 : nat_p 15.
exact nat_ordsucc 14 nat_p_14.
Qed.

Theorem nat_p_16 : nat_p 16.
exact nat_ordsucc 15 nat_p_15.
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 nat_p_16.
Qed.

Theorem twelve_subset_12 : 12 c= 12.
let x. assume Hx: x :e 12. exact Hx.
Qed.

Theorem in_12_13 : 12 :e 13.
prove 12 :e ordsucc 12.
exact ordsuccI2 12.
Qed.

Theorem twelve_subset_13 : 12 c= 13.
let x. assume Hx: x :e 12.
exact nat_trans 13 nat_p_13 12 in_12_13 x Hx.
Qed.

Theorem in_12_14 : 12 :e 14.
prove 12 :e ordsucc 13.
apply ordsuccI1 13.
exact in_12_13.
Qed.

Theorem twelve_subset_14 : 12 c= 14.
let x. assume Hx: x :e 12.
exact nat_trans 14 nat_p_14 12 in_12_14 x Hx.
Qed.

Theorem in_12_15 : 12 :e 15.
prove 12 :e ordsucc 14.
apply ordsuccI1 14.
exact in_12_14.
Qed.

Theorem twelve_subset_15 : 12 c= 15.
let x. assume Hx: x :e 12.
exact nat_trans 15 nat_p_15 12 in_12_15 x Hx.
Qed.

Theorem in_12_16 : 12 :e 16.
prove 12 :e ordsucc 15.
apply ordsuccI1 15.
exact in_12_15.
Qed.

Theorem twelve_subset_16 : 12 c= 16.
let x. assume Hx: x :e 12.
exact nat_trans 16 nat_p_16 12 in_12_16 x Hx.
Qed.

Theorem in_12_17 : 12 :e 17.
prove 12 :e ordsucc 16.
apply ordsuccI1 16.
exact in_12_16.
Qed.

Theorem twelve_subset_17 : 12 c= 17.
let x. assume Hx: x :e 12.
exact nat_trans 17 nat_p_17 12 in_12_17 x Hx.
Qed.

Theorem nat_p_6 : nat_p 6.
exact nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))).
Qed.

Axiom equip_Subq_exists : forall k n V:set,
  k c= n ->
  equip n V ->
  exists U:set, U c= V /\ equip k U.

Theorem ordinal_In_implies_Subq : forall alpha beta:set,
  ordinal alpha -> ordinal beta -> beta :e alpha -> beta c= alpha.
let alpha beta.
assume Halpha: ordinal alpha.
assume Hbeta: ordinal beta.
assume Hba: beta :e alpha.
prove beta c= alpha.
claim HTS: TransSet alpha.
  exact ordinal_TransSet alpha Halpha.
exact HTS beta Hba.
Qed.

Theorem nat_In_Or_Subq_6 : forall n:set,
  nat_p n -> n :e 6 \/ 6 c= n.
let n.
assume Hn: nat_p n.
prove n :e 6 \/ 6 c= n.
claim Hord_n: ordinal n.
  exact nat_p_ordinal n Hn.
claim Hord_6: ordinal 6.
  exact nat_p_ordinal 6 nat_p_6.
exact ordinal_In_Or_Subq n 6 Hord_n Hord_6.
Qed.

Theorem no_6subset_bound_5 : forall N:set, forall n:set,
  nat_p n ->
  equip n N ->
  ~(exists T:set, T c= N /\ equip 6 T) ->
  n :e 6.
let N n.
assume Hn: nat_p n.
assume HeqN: equip n N.
assume Hno6: ~(exists T:set, T c= N /\ equip 6 T).
prove n :e 6.
claim HnNotSubq6: ~(6 c= n).
  assume H6n: 6 c= n.
  apply Hno6.
  prove exists T:set, T c= N /\ equip 6 T.
  exact equip_Subq_exists 6 n N H6n HeqN.
apply nat_In_Or_Subq_6 n Hn.
- assume Hn6: n :e 6.
  exact Hn6.
- assume H6n: 6 c= n.
  apply HnNotSubq6.
  exact H6n.
Qed.
