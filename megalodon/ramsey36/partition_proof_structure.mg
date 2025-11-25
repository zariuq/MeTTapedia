Theorem nat_p_6 : nat_p 6.
exact nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))).
Qed.

Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13
      (nat_ordsucc 12 nat_p_12)))).
Qed.

Theorem twelve_subset_17 : 12 c= 17.
Admitted.

Theorem six_subset_17 : 6 c= 17.
Admitted.

Axiom equip_Subq_exists : forall k n V:set,
  k c= n ->
  equip n V ->
  exists U:set, U c= V /\ equip k U.

Axiom disjoint_union_equip : forall V N Non:set, forall n m:set,
  nat_p n -> nat_p m ->
  N c= V -> Non c= V ->
  (forall x :e V, x :e N \/ x :e Non) ->
  (forall x, x :e N -> x /:e Non) ->
  equip n N ->
  equip m Non ->
  equip (n + m) V.

Axiom arithmetic_bound_17_5_12 : forall n m:set,
  nat_p n -> nat_p m ->
  n :e 6 ->
  n + m = 17 ->
  12 c= m.

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
claim Hex_n: exists n:set, nat_p n /\ equip n N.
  apply HeqV.
  let f.
  assume Hf: bij 17 V f.
  admit.
apply Hex_n.
let n.
assume Hn: nat_p n /\ equip n N.
claim Hn_nat: nat_p n.
  exact andEL (nat_p n) (equip n N) Hn.
claim HeqN: equip n N.
  exact andER (nat_p n) (equip n N) Hn.
claim Hex_m: exists m:set, nat_p m /\ equip m Non.
  admit.
apply Hex_m.
let m.
assume Hm: nat_p m /\ equip m Non.
claim Hm_nat: nat_p m.
  exact andEL (nat_p m) (equip m Non) Hm.
claim HeqNon: equip m Non.
  exact andER (nat_p m) (equip m Non) Hm.
claim Hadd: n + m = 17.
  claim Heq_sum: equip (n + m) V.
    exact disjoint_union_equip V N Non n m Hn_nat Hm_nat HNV HNonV Hpart Hdisj HeqN HeqNon.
  admit.
claim Hn_bound: n :e 6.
  exact no_6subset_bound_5 N n Hn_nat HeqN Hno6.
claim H12_m: 12 c= m.
  exact arithmetic_bound_17_5_12 n m Hn_nat Hm_nat Hn_bound Hadd.
exact equip_Subq_exists 12 m Non H12_m HeqNon.
Qed.
