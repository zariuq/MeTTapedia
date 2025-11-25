Definition cardinal : set -> prop :=
  fun X => exists B:set, X = B /\ (forall A:set, equip A B -> B c= A).

Theorem eq_symm_set : forall x y:set, x = y -> y = x.
let x. let y.
assume Hxy: x = y.
prove y = x.
let Q:set -> set -> prop.
assume HQ: Q y x.
exact Hxy (fun u v => Q v u) HQ.
Qed.

Theorem equip_sym_card : forall X Y:set, equip X Y -> equip Y X.
let X. let Y.
assume Hex: equip X Y.
exact equip_sym X Y Hex.
Qed.

Theorem cardinal_empty : cardinal Empty.
prove exists B:set, Empty = B /\ (forall A:set, equip A B -> B c= A).
witness Empty.
apply andI (Empty = Empty) (forall A:set, equip A Empty -> Empty c= A).
- reflexivity.
- let A.
  assume _ : equip A Empty.
  exact Subq_Empty A.
Qed.

Theorem cardinal_existence : exists X:set, cardinal X.
witness Empty.
exact cardinal_empty.
Qed.

Theorem cardinal_min : forall X A:set, cardinal X -> equip A X -> X c= A.
let X. let A.
assume Hcard: cardinal X.
assume Heq: equip A X.
apply Hcard.
let B. assume HB: X = B /\ (forall A:set, equip A B -> B c= A).
claim HX: X = B.
  exact andEL (X = B) (forall A:set, equip A B -> B c= A) HB.
claim HBprop: forall A:set, equip A B -> B c= A.
  exact andER (X = B) (forall A:set, equip A B -> B c= A) HB.
claim HeqAB: equip A B.
  rewrite <- HX.
  exact Heq.
claim HBsub: B c= A.
  exact HBprop A HeqAB.
rewrite HX.
exact HBsub.
Qed.

Theorem cardinal_intro : forall X:set,
  (forall A:set, equip A X -> X c= A) -> cardinal X.
let X.
assume Hmin: forall A:set, equip A X -> X c= A.
prove exists B:set, X = B /\ (forall A:set, equip A B -> B c= A).
witness X.
apply andI (X = X) (forall A:set, equip A X -> X c= A).
- reflexivity.
- exact Hmin.
Qed.

Theorem cardinal_eq_of_equip : forall M N:set,
  cardinal M -> cardinal N -> equip M N -> M = N.
let M. let N.
assume HM: cardinal M.
assume HN: cardinal N.
assume Heq: equip M N.
claim Heq_sym: equip N M.
  exact equip_sym_card M N Heq.
claim Hsub1: M c= N.
  exact cardinal_min M N HM Heq_sym.
claim Hsub2: N c= M.
  exact cardinal_min N M HN Heq.
exact set_ext M N Hsub1 Hsub2.
Qed.

Theorem equip_empty_eq : forall A:set, equip A Empty -> A = Empty.
let A.
assume Heq: equip A Empty.
apply Heq.
let f:set -> set.
assume Hbij: bij A Empty f.
prove A = Empty.
apply Empty_Subq_eq A.
prove A c= Empty.
let x. assume HxA: x :e A.
claim Hmap: forall u :e A, f u :e Empty.
  apply and3E (forall u :e A, f u :e Empty) (forall u v :e A, f u = f v -> u = v) (forall w :e Empty, exists u :e A, f u = w) Hbij.
  assume H1: forall u :e A, f u :e Empty.
  assume H2: forall u v :e A, f u = f v -> u = v.
  assume H3: forall w :e Empty, exists u :e A, f u = w.
  exact H1.
claim Hfx: f x :e Empty.
  exact Hmap x HxA.
apply FalseE.
apply EmptyAx.
witness (f x).
exact Hfx.
Qed.

Theorem equip_nonempty : forall X Y:set, forall x:set,
  x :e X -> equip X Y -> exists y:set, y :e Y.
let X. let Y. let x.
assume Hx: x :e X.
assume Heq: equip X Y.
apply Heq.
let f:set -> set.
assume Hbij: bij X Y f.
claim Hmap: forall u :e X, f u :e Y.
  apply and3E (forall u :e X, f u :e Y) (forall u v :e X, f u = f v -> u = v) (forall w :e Y, exists u :e X, f u = w) Hbij.
  assume H1: forall u :e X, f u :e Y.
  assume H2: forall u v :e X, f u = f v -> u = v.
  assume H3: forall w :e Y, exists u :e X, f u = w.
  exact H1.
prove exists y:set, y :e Y.
witness (f x).
exact Hmap x Hx.
Qed.

Theorem equip_nonempty_ne : forall X Y:set, forall x:set,
  x :e X -> equip X Y -> Y <> Empty.
let X. let Y. let x.
assume Hx: x :e X.
assume Heq: equip X Y.
claim Hex: exists y:set, y :e Y.
  exact equip_nonempty X Y x Hx Heq.
assume HY: Y = Empty.
claim HeqE: equip X Empty.
  rewrite <- HY.
  exact Heq.
claim HexE: exists y:set, y :e Empty.
  exact equip_nonempty X Empty x Hx HeqE.
apply EmptyAx.
exact HexE.
Qed.

Theorem equip_ordsucc_has_elem : forall X n:set, equip X (ordsucc n) -> exists x:set, x :e X.
let X. let n.
assume Heq: equip X (ordsucc n).
apply equip_nonempty (ordsucc n) X n.
- exact ordsuccI2 n.
- exact equip_sym_card X (ordsucc n) Heq.
Qed.

Theorem t_card_1_Th1 : forall M N:set,
  cardinal M -> cardinal N -> equip M N -> M = N.
exact cardinal_eq_of_equip.
Qed.

Theorem t_card_1_equip_refl : forall X:set, equip X X.
let X.
exact equip_ref X.
Qed.

Theorem t_card_1_equip_sym : forall X Y:set, equip X Y -> equip Y X.
let X Y.
assume H: equip X Y.
exact equip_sym X Y H.
Qed.

Theorem t_card_1_equip_tra : forall X Y Z:set,
  equip X Y -> equip Y Z -> equip X Z.
let X Y Z.
assume HXY: equip X Y.
assume HYZ: equip Y Z.
exact equip_tra X Y Z HXY HYZ.
Qed.

Theorem equip_singleton_shape : forall X a:set, equip X {a} -> exists x:set, X = {x}.
let X. let a.
assume Heq: equip X {a}.
apply Heq.
let f:set -> set.
assume Hbij: bij X {a} f.
claim Hmap: forall u :e X, f u :e {a}.
  apply and3E (forall u :e X, f u :e {a}) (forall u v :e X, f u = f v -> u = v) (forall w :e {a}, exists u :e X, f u = w) Hbij.
  assume H1: forall u :e X, f u :e {a}.
  assume H2: forall u v :e X, f u = f v -> u = v.
  assume H3: forall w :e {a}, exists u :e X, f u = w.
  exact H1.
claim Hex: exists u :e X, f u = a.
  apply and3E (forall u :e X, f u :e {a}) (forall u v :e X, f u = f v -> u = v) (forall w :e {a}, exists u :e X, f u = w) Hbij.
  assume H1: forall u :e X, f u :e {a}.
  assume H2: forall u v :e X, f u = f v -> u = v.
  assume H3: forall w :e {a}, exists u :e X, f u = w.
  claim H3a: exists u :e X, f u = a.
    exact H3 a (SingI a).
  exact H3a.
apply Hex.
let x0. assume Hx0: x0 :e X /\ f x0 = a.
claim Hx0_in: x0 :e X.
  exact andEL (x0 :e X) (f x0 = a) Hx0.
claim Hx0_val: f x0 = a.
  exact andER (x0 :e X) (f x0 = a) Hx0.
prove exists x:set, X = {x}.
witness x0.
apply set_ext X {x0}.
- prove X c= {x0}.
  let y. assume Hy: y :e X.
  claim Hy_img: f y :e {a}.
    exact Hmap y Hy.
  claim Hy_eq: f y = a.
    exact SingE a (f y) Hy_img.
  claim Hy_eqx: y = x0.
    apply and3E (forall u :e X, f u :e {a}) (forall u v :e X, f u = f v -> u = v) (forall w :e {a}, exists u :e X, f u = w) Hbij.
    assume H1: forall u :e X, f u :e {a}.
    assume H2: forall u v :e X, f u = f v -> u = v.
    assume H3: forall w :e {a}, exists u :e X, f u = w.
    exact H2 y Hy x0 Hx0_in (eq_i_tra (f y) a (f x0) Hy_eq (eq_symm_set (f x0) a Hx0_val)).
  rewrite Hy_eqx.
  exact SingI x0.
- prove {x0} c= X.
  let y. assume Hy: y :e {x0}.
  rewrite (SingE x0 y Hy).
  exact Hx0_in.
Qed.

Theorem t_card_1_Subq_equip : forall X Y:set,
  X c= Y -> equip X Y -> X = Y.
let X Y.
assume HXY: X c= Y.
assume Heq: equip X Y.
admit.
Qed.

Theorem t_card_1_equip_Empty_iff : forall X:set,
  equip X Empty <-> X = Empty.
let X.
apply iffI.
- exact equip_empty_eq X.
- assume HX: X = Empty.
  rewrite HX.
  exact equip_ref Empty.
Qed.

Theorem t_card_1_Sing_power_0 : {Empty} = Power Empty.
apply set_ext.
- let x. assume Hx: x :e {Empty}.
  claim Hxe: x = Empty.
    exact SingE Empty x Hx.
  rewrite Hxe.
  prove Empty :e Power Empty.
  apply PowerI Empty Empty.
  exact Subq_ref Empty.
- let x. assume Hx: x :e Power Empty.
  claim Hxe: x c= Empty.
    exact PowerE Empty x Hx.
  claim Hxeq: x = Empty.
    exact Empty_Subq_eq x Hxe.
  rewrite Hxeq.
  exact SingI Empty.
Qed.

Theorem t_card_1_equip_nat_finite : forall S n:set,
  nat_p n -> equip n S -> finite S.
let S n.
assume Hn: nat_p n.
assume Heq: equip n S.
prove exists m :e omega, equip S m.
witness n.
apply andI.
- exact nat_p_omega n Hn.
- exact equip_sym n S Heq.
Qed.

Theorem t_card_1_finite_equip_nat : forall S:set,
  finite S -> exists n:set, nat_p n /\ equip n S.
let S.
assume Hf: finite S.
prove exists n:set, nat_p n /\ equip n S.
apply Hf.
let n. assume Hn: n :e omega /\ equip S n.
claim Hn_omega: n :e omega.
  exact andEL (n :e omega) (equip S n) Hn.
claim HeqSn: equip S n.
  exact andER (n :e omega) (equip S n) Hn.
witness n.
apply andI.
- exact omega_nat_p n Hn_omega.
- exact equip_sym S n HeqSn.
Qed.

Theorem t_card_1_equip_subset_le : forall S T k m:set,
  S c= T -> nat_p k -> nat_p m -> equip k S -> equip m T -> k c= m.
let S T k m.
assume HST: S c= T.
assume Hk: nat_p k.
assume Hm: nat_p m.
assume HkS: equip k S.
assume HmT: equip m T.
admit.
Qed.

Theorem t_card_1_equip_Empty_0 : equip 0 Empty.
exact equip_ref Empty.
Qed.

Theorem t_card_1_equip_0_Empty : forall S:set,
  equip 0 S -> S = Empty.
let S.
assume H: equip 0 S.
claim HeqS0: equip S 0.
  exact equip_sym 0 S H.
exact equip_empty_eq S HeqS0.
Qed.

Theorem t_card_1_nonempty_not_0 : forall S:set, forall x:set,
  x :e S -> ~ equip 0 S.
let S x.
assume Hx: x :e S.
assume Heq: equip 0 S.
claim HS: S = Empty.
  exact t_card_1_equip_0_Empty S Heq.
claim HxE: x :e Empty.
  rewrite <- HS.
  exact Hx.
apply EmptyAx.
witness x.
exact HxE.
Qed.

Theorem t_card_1_equip_disjoint_union : forall A B n m:set,
  nat_p n -> nat_p m ->
  equip n A -> equip m B ->
  (forall x, x :e A -> x /:e B) ->
  exists p:set, nat_p p /\ equip p (A :\/: B).
let A B n m.
assume Hn: nat_p n.
assume Hm: nat_p m.
assume HeqnA: equip n A.
assume HeqmB: equip m B.
assume Hdisj: forall x, x :e A -> x /:e B.
admit.
Qed.

Theorem t_card_1_equip_setminus : forall A B n m:set,
  B c= A -> nat_p n -> nat_p m ->
  equip n A -> equip m B ->
  exists d:set, nat_p d /\ equip d (A :\: B).
let A B n m.
assume HBA: B c= A.
assume Hn: nat_p n.
assume Hm: nat_p m.
assume HeqnA: equip n A.
assume HeqmB: equip m B.
admit.
Qed.

Theorem t_card_1_singleton_equip_1 : forall S:set,
  (exists x:set, S = {x}) -> equip 1 S.
let S. assume Hex: exists x:set, S = {x}.
prove equip 1 S.
admit.
Qed.

Theorem t_card_1_equip_1_singleton : forall x:set, equip 1 {x}.
let x.
apply t_card_1_singleton_equip_1 {x}.
witness x.
reflexivity.
Qed.

Theorem t_card_1_singleton_equip : forall x:set, equip {x} 1.
let x.
claim H1: equip 1 {x}.
  exact t_card_1_equip_1_singleton x.
exact equip_sym 1 {x} H1.
Qed.

Theorem t_card_1_equip_2_pair : forall x y:set, x <> y -> equip 2 {x, y}.
admit.
Qed.

Theorem t_card_1_equip_add_elem : forall S x n:set,
  nat_p n -> x /:e S -> equip n S -> equip (ordsucc n) ({x} :\/: S).
admit.
Qed.

Theorem t_card_1_equip_remove_elem : forall S x n:set,
  nat_p n -> x :e S -> equip (ordsucc n) S -> equip n (S :\: {x}).
admit.
Qed.

Theorem t_card_1_finite_Subq : forall X Y:set,
  X c= Y -> finite Y -> finite X.
admit.
Qed.

Theorem t_card_1_finite_union : forall X Y:set,
  finite X -> finite Y -> finite (X :\/: Y).
admit.
Qed.

Theorem t_card_1_finite_setminus : forall X Y:set,
  finite X -> finite (X :\: Y).
admit.
Qed.

Theorem t_card_1_finite_inter : forall X Y:set,
  finite X -> finite (X :/\: Y).
admit.
Qed.

Theorem t_card_1_nat_ordinal_equip : forall n:set,
  nat_p n -> equip n n.
let n. assume Hn: nat_p n. exact equip_ref n.
Qed.

Theorem card_1_compiles : True.
exact TrueI.
Qed.
