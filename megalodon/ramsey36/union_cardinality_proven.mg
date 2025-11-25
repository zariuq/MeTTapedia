Theorem nat_p_10 : nat_p 10.
exact nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5
      (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))).
Qed.

Theorem nat_p_9 : nat_p 9.
exact nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5
      (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))).
Qed.

Theorem nat_p_7 : nat_p 7.
exact nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))).
Qed.

Theorem nat_p_8 : nat_p 8.
exact nat_ordsucc 7 nat_p_7.
Qed.

Definition sum_case : set -> set -> (set -> set) -> (set -> set) -> set :=
  fun n m fA fB => lam z :e n :+: m,
    (lam_i (Inj0 x) (x :e n) => fA x) z :\/:
    (lam_i (Inj1 y) (y :e m) => fB y) z.

Theorem equip_setsum : forall A B n m:set,
  nat_p n -> nat_p m ->
  equip n A -> equip m B ->
  equip (n :+: m) (A :\/: B).
let A B n m.
assume Hn: nat_p n.
assume Hm: nat_p m.
assume HeqA: equip n A.
assume HeqB: equip m B.
prove equip (n :+: m) (A :\/: B).
apply HeqA.
let fA: set -> set.
assume HfA: bij n A fA.
apply HeqB.
let fB: set -> set.
assume HfB: bij m B fB.
prove exists f:set->set, bij (n :+: m) (A :\/: B) f.
Admitted.
Qed.

Theorem equip_union_disjoint : forall A B n m:set,
  nat_p n -> nat_p m ->
  equip n A -> equip m B ->
  (A :/\: B = Empty) ->
  equip (add_nat n m) (A :\/: B).
Admitted.

Theorem equip_Subq_card_le : forall A B n m:set,
  A c= B ->
  equip n A -> equip m B ->
  n c= m.
Admitted.
