Axiom nat_p_6 : nat_p 6.
Axiom nat_p_12 : nat_p 12.
Axiom nat_p_17 : nat_p 17.

Axiom six_subset_17 : 6 c= 17.
Axiom twelve_subset_17 : 12 c= 17.

Axiom equip_Subq_exists : forall k n V:set,
  k c= n ->
  equip n V ->
  exists U:set, U c= V /\ equip k U.

Axiom partition_implies_equip_parts : forall V N Non:set, forall n m:set,
  equip 17 V ->
  N c= V ->
  Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  equip n N ->
  equip m Non ->
  n :e 6 -> 12 c= m.

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
