Axiom nat_p : set -> prop.
Axiom nat_0 : nat_p 0.
Axiom nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
Axiom nat_trans : forall n:set, nat_p n -> forall m:set, m :e n -> forall p:set, p :e m -> p :e n.
Axiom nat_p_ordinal : forall n:set, nat_p n -> ordinal n.

Definition equip : set -> set -> prop := fun X Y:set => exists f:set -> set, bij X Y f.

Axiom equip_ref : forall X, equip X X.

Theorem nat_p_6 : nat_p 6.
Admitted.

Theorem nat_p_12 : nat_p 12.
Admitted.

Theorem nat_p_17 : nat_p 17.
Admitted.

Axiom equip_Subq_exists : forall k n V:set,
  k c= n ->
  equip n V ->
  exists U:set, U c= V /\ equip k U.

Axiom six_subset_17 : 6 c= 17.
Axiom twelve_subset_17 : 12 c= 17.

Axiom partition_trichotomy : forall n:set,
  nat_p n -> (n :e 6 \/ n = 6 \/ 6 c= n).

Axiom nat_in_ordsucc : forall n m:set,
  nat_p n -> n :e ordsucc n.

Axiom disjoint_union_card_17 : forall V N Non:set, forall n m:set,
  nat_p n -> nat_p m ->
  equip n N ->
  equip m Non ->
  N c= V ->
  Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  equip 17 V ->
  (n :e 6 -> 12 c= m).

Theorem partition_17_5_implies_12 : forall V N Non:set,
  equip 17 V ->
  N c= V ->
  Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  ~(exists T, T c= N /\ equip 6 T) ->
  exists S, S c= Non /\ equip 12 S.
let V N Non.
assume HeqV: equip 17 V.
assume HNV: N c= V.
assume HNonV: Non c= V.
assume Hpart: forall x :e V, x :e N \/ x :e Non.
assume Hdisj: forall x, x :e N -> x /:e Non.
assume Hno6: ~(exists T, T c= N /\ equip 6 T).
prove exists S, S c= Non /\ equip 12 S.
Admitted.
