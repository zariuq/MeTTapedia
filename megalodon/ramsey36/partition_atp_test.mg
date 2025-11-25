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

Theorem six_subset_17 : 6 c= 17.
Admitted.

Theorem twelve_subset_17 : 12 c= 17.
Admitted.

Theorem equip_Subq_exists : forall k n V:set,
  k c= n ->
  equip n V ->
  exists U:set, U c= V /\ equip k U.
Admitted.

Theorem partition_17_5_implies_12 : forall V N Non:set,
  equip 17 V ->
  N c= V ->
  Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  ~(exists T, T c= N /\ equip 6 T) ->
  exists S, S c= Non /\ equip 12 S.
Admitted.
