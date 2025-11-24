% Cardinality lemmas for partition arithmetic
% Needed for vertex_has_12_nonneighbors proof

% Basic lemma: disjoint union of finite sets
Theorem equip_disjoint_union : forall A B n m: set,
  nat_p n -> nat_p m ->
  equip n A -> equip m B ->
  (forall x, x :e A -> x /:e B) ->
  equip (n + m) (A :\/: B).
let A B n m.
assume Hn: nat_p n.
assume Hm: nat_p m.
assume HeqA: equip n A.
assume HeqB: equip m B.
assume Hdisj: forall x, x :e A -> x /:e B.
prove equip (n + m) (A :\/: B).
% Get bijections f: n -> A and g: m -> B
apply equip_bij n A HeqA.
let f: set -> set.
assume Hf: bij n A f.
apply equip_bij m B HeqB.
let g: set -> set.
assume Hg: bij m B g.
% Construct bijection h: (n + m) -> (A ∪ B)
% h(i) = f(i) if i < n, g(i - n) if i >= n
% But wait, n + m in set theory is ordinal addition
% Need to work with setsum (n :+: m) instead
sorry.
Admitted.
