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

Theorem in_6_17 : 6 :e 17.
prove 6 :e ordsucc 16.
apply ordsuccI1 16.
prove 6 :e 16.
apply ordsuccI1 15.
prove 6 :e 15.
apply ordsuccI1 14.
prove 6 :e 14.
apply ordsuccI1 13.
prove 6 :e 13.
apply ordsuccI1 12.
prove 6 :e 12.
apply ordsuccI1 11.
prove 6 :e 11.
apply ordsuccI1 10.
prove 6 :e 10.
apply ordsuccI1 9.
prove 6 :e 9.
apply ordsuccI1 8.
prove 6 :e 8.
apply ordsuccI1 7.
prove 6 :e 7.
exact ordsuccI2 6.
Qed.

Theorem six_subset_17 : 6 c= 17.
let x. assume Hx: x :e 6.
exact nat_trans 17 nat_p_17 6 in_6_17 x Hx.
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

Theorem no_6subset_implies_small : forall N:set, forall n:set,
  nat_p n ->
  equip n N ->
  ~(exists T:set, T c= N /\ equip 6 T) ->
  ~(6 c= n).
let N n.
assume Hn: nat_p n.
assume HeqN: equip n N.
assume Hno6: ~(exists T:set, T c= N /\ equip 6 T).
prove ~(6 c= n).
assume H6n: 6 c= n.
apply Hno6.
prove exists T:set, T c= N /\ equip 6 T.
exact equip_Subq_exists 6 n N H6n HeqN.
Qed.

Theorem has_subset_from_cardinality : forall N:set, forall n:set,
  nat_p n ->
  6 c= n ->
  equip n N ->
  exists T:set, T c= N /\ equip 6 T.
let N n.
assume Hn: nat_p n.
assume H6n: 6 c= n.
assume HeqN: equip n N.
exact equip_Subq_exists 6 n N H6n HeqN.
Qed.

Theorem no_6subset_card_bound : forall N:set, forall n:set,
  nat_p n ->
  equip n N ->
  ~(exists T:set, T c= N /\ equip 6 T) ->
  n :e 6.
Admitted.

Theorem disjoint_union_card : forall V N Non:set, forall n m:set,
  nat_p n -> nat_p m ->
  N c= V -> Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  equip n N ->
  equip m Non ->
  equip (add_nat n m) V.
Admitted.

Theorem add_bound_17_5_12 : forall n m:set,
  nat_p n -> nat_p m ->
  n :e 6 ->
  add_nat n m = 17 ->
  12 c= m.
Admitted.
