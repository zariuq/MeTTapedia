(** Products of natural numbers: a factor of a positive number is at most the
    number, a product is zero only with a zero factor, and one only with
    both factors one.  For the reading of Lean's divisibility on Nat. **)

Theorem NatFactor_add_Subq : forall n, forall m, nat_p m -> n c= add_nat n m.
let n.
apply nat_ind.
- prove n c= add_nat n 0. rewrite add_nat_0R n. exact Subq_ref n.
- let m. assume Hm: nat_p m. assume IH: n c= add_nat n m.
  prove n c= add_nat n (ordsucc m).
  rewrite add_nat_SR n m Hm.
  exact Subq_tra n (add_nat n m) (ordsucc (add_nat n m)) IH (ordsuccI1 (add_nat n m)).
Qed.

Theorem NatFactor_mul_Subq : forall n, nat_p n -> forall m, nat_p m -> n c= mul_nat n (ordsucc m).
let n. assume Hn: nat_p n. let m. assume Hm: nat_p m.
rewrite mul_nat_SR n m Hm.
exact NatFactor_add_Subq n (mul_nat n m) (mul_nat_p n Hn m Hm).
Qed.

Theorem NatFactor_mul_zero : forall n, nat_p n -> forall m, nat_p m -> mul_nat n m = 0 -> n = 0 \/ m = 0.
let n. assume Hn: nat_p n. let m. assume Hm: nat_p m. assume H: mul_nat n m = 0.
apply nat_inv m Hm.
- assume Hm0: m = 0. apply orIR. exact Hm0.
- assume Hex: exists x, nat_p x /\ m = ordsucc x.
  apply Hex. let x. assume Hx: nat_p x /\ m = ordsucc x.
  apply Hx. assume Hx1: nat_p x. assume Hx2: m = ordsucc x.
  apply orIL.
  prove n = 0.
  apply Empty_Subq_eq.
  prove n c= 0.
  rewrite <- H. rewrite Hx2.
  exact NatFactor_mul_Subq n Hn x Hx1.
Qed.

Theorem NatFactor_Subq_1 : forall n, nat_p n -> n c= 1 -> n <> 0 -> n = 1.
let n. assume Hn: nat_p n. assume H1: n c= 1. assume H0: n <> 0.
apply nat_inv n Hn.
- assume Hn0: n = 0. apply FalseE. exact H0 Hn0.
- assume Hex: exists x, nat_p x /\ n = ordsucc x.
  apply Hex. let x. assume Hx: nat_p x /\ n = ordsucc x.
  apply Hx. assume Hx1: nat_p x. assume Hx2: n = ordsucc x.
  claim Lx: x :e 1.
  { apply H1. rewrite Hx2. exact ordsuccI2 x. }
  claim Lx0: x = 0.
  { apply ordsuccE 0 x Lx.
    - assume Hx0: x :e 0. apply FalseE. exact EmptyE x Hx0.
    - assume Hx0: x = 0. exact Hx0. }
  rewrite Hx2. rewrite Lx0. reflexivity.
Qed.

Theorem NatFactor_mul_one : forall n, nat_p n -> forall m, nat_p m -> mul_nat n m = 1 -> n = 1.
let n. assume Hn: nat_p n. let m. assume Hm: nat_p m. assume H: mul_nat n m = 1.
claim Lm: m <> 0.
{ assume Hm0: m = 0.
  apply neq_0_1.
  prove 0 = 1.
  rewrite <- H. rewrite Hm0. rewrite mul_nat_0R n. reflexivity. }
claim Ln: n <> 0.
{ assume Hn0: n = 0.
  apply neq_0_1.
  prove 0 = 1.
  rewrite <- H. rewrite Hn0. rewrite mul_nat_0L m Hm. reflexivity. }
apply NatFactor_Subq_1 n Hn.
- prove n c= 1.
  apply nat_inv m Hm.
  + assume Hm0: m = 0. apply FalseE. exact Lm Hm0.
  + assume Hex: exists x, nat_p x /\ m = ordsucc x.
    apply Hex. let x. assume Hx: nat_p x /\ m = ordsucc x.
    apply Hx. assume Hx1: nat_p x. assume Hx2: m = ordsucc x.
    rewrite <- H. rewrite Hx2.
    exact NatFactor_mul_Subq n Hn x Hx1.
- exact Ln.
Qed.

Theorem NatFactor_pred_In : forall w n, ordsucc w = n -> w :e n.
let w n. assume H: ordsucc w = n.
rewrite <- H. exact ordsuccI2 w.
Qed.

Theorem NatFactor_add_cancel : forall n, forall k, nat_p k -> add_nat n k = n -> k = 0.
let n. let k. assume Hk: nat_p k. assume H: add_nat n k = n.
apply nat_inv k Hk.
- assume Hk0: k = 0. exact Hk0.
- assume Hex: exists x, nat_p x /\ k = ordsucc x.
  apply Hex. let x. assume Hx: nat_p x /\ k = ordsucc x.
  apply Hx. assume Hx1: nat_p x. assume Hx2: k = ordsucc x.
  apply FalseE.
  claim L1: ordsucc (add_nat n x) = n.
  { rewrite <- add_nat_SR n x Hx1. rewrite <- Hx2. exact H. }
  claim L2: add_nat n x :e n.
  { exact NatFactor_pred_In (add_nat n x) n L1. }
  exact In_irref (add_nat n x) (NatFactor_add_Subq n x Hx1 (add_nat n x) L2).
Qed.

Theorem NatFactor_mul_cancel_one : forall p, nat_p p -> p <> 0 -> forall b, nat_p b -> mul_nat p b = p -> b = 1.
let p. assume Hp: nat_p p. assume Hp0: p <> 0. let b. assume Hb: nat_p b. assume H: mul_nat p b = p.
apply nat_inv b Hb.
- assume Hb0: b = 0. apply FalseE. apply Hp0.
  prove p = 0. rewrite <- H. rewrite Hb0. exact mul_nat_0R p.
- assume Hex: exists x, nat_p x /\ b = ordsucc x.
  apply Hex. let x. assume Hx: nat_p x /\ b = ordsucc x.
  apply Hx. assume Hx1: nat_p x. assume Hx2: b = ordsucc x.
  claim L1: add_nat p (mul_nat p x) = p.
  { rewrite <- mul_nat_SR p x Hx1. rewrite <- Hx2. exact H. }
  claim L2: mul_nat p x = 0.
  { exact NatFactor_add_cancel p (mul_nat p x) (mul_nat_p p Hp x Hx1) L1. }
  apply NatFactor_mul_zero p Hp x Hx1 L2.
  + assume Hp00: p = 0. apply FalseE. exact Hp0 Hp00.
  + assume Hx0: x = 0. rewrite Hx2. rewrite Hx0. reflexivity.
Qed.

Theorem NatFactor_two_Subq : forall n, nat_p n -> n <> 0 -> n <> 1 -> 2 c= n.
let n. assume Hn: nat_p n. assume H0: n <> 0. assume H1: n <> 1.
apply ordinal_In_Or_Subq n 2 (nat_p_ordinal n Hn) (nat_p_ordinal 2 nat_2).
- assume H: n :e 2. apply FalseE.
  apply ordsuccE 1 n H.
  + assume Hn1: n :e 1.
    apply ordsuccE 0 n Hn1.
    * assume Hn0: n :e 0. exact EmptyE n Hn0.
    * assume Hn0: n = 0. exact H0 Hn0.
  + assume Hn1: n = 1. exact H1 Hn1.
- assume H: 2 c= n. exact H.
Qed.

Theorem NatFactor_mul_1R : forall n, mul_nat n 1 = n.
let n.
rewrite mul_nat_SR n 0 nat_0. rewrite mul_nat_0R n. exact add_nat_0R n.
Qed.

Theorem NatFactor_Subq_eq : forall X Y Z, X c= Y -> Y = Z -> X c= Z.
let X Y Z. assume H: X c= Y. assume E: Y = Z.
rewrite <- E. exact H.
Qed.

Theorem NatFactor_In_eq : forall x Y Z, x :e Y -> Y = Z -> x :e Z.
let x Y Z. assume H: x :e Y. assume E: Y = Z.
rewrite <- E. exact H.
Qed.

Theorem NatFactor_two_not_Subq_1 : ~ (2 c= 1).
assume H: 2 c= 1.
exact In_irref 1 (H 1 In_1_2).
Qed.

Theorem NatFactor_two_not_Subq_0 : ~ (2 c= 0).
assume H: 2 c= 0.
exact EmptyE 0 (H 0 In_0_2).
Qed.

(** A natural number that is not one and whose factorisations have a factor
    one is at least two and has no divisor between two and itself. **)
Theorem NatFactor_irreducible_bounded : forall p, nat_p p -> p <> 1 ->
  (forall a, nat_p a -> forall b, nat_p b -> p = mul_nat a b -> a = 1 \/ b = 1) ->
  2 c= p /\ (forall m, nat_p m -> 2 c= m -> m :e p -> forall c, nat_p c -> p <> mul_nat m c).
let p. assume Hp: nat_p p. assume Hp1: p <> 1.
assume H: forall a, nat_p a -> forall b, nat_p b -> p = mul_nat a b -> a = 1 \/ b = 1.
claim Lp0: p <> 0.
{ assume Hp0: p = 0.
  claim L: p = mul_nat 0 0.
  { rewrite Hp0. rewrite mul_nat_0R 0. reflexivity. }
  apply H 0 nat_0 0 nat_0 L.
  - assume H01: 0 = 1. exact neq_0_1 H01.
  - assume H01: 0 = 1. exact neq_0_1 H01. }
apply andI.
- exact NatFactor_two_Subq p Hp Lp0 Hp1.
- let m. assume Hm: nat_p m. assume Hm2: 2 c= m. assume Hmp: m :e p.
  let c. assume Hc: nat_p c. assume Hpc: p = mul_nat m c.
  apply H m Hm c Hc Hpc.
  + assume Hm1: m = 1. exact NatFactor_two_not_Subq_1 (NatFactor_Subq_eq 2 m 1 Hm2 Hm1).
  + assume Hc1: c = 1.
    claim Lpm: p = m.
    { rewrite Hpc. rewrite Hc1. exact NatFactor_mul_1R m. }
    exact In_irref m (NatFactor_In_eq m p m Hmp Lpm).
Qed.

(** Conversely, a natural number that is at least two and has no divisor
    between two and itself is not one, and its factorisations have a factor one. **)
Theorem NatFactor_bounded_irreducible : forall p, nat_p p -> 2 c= p ->
  (forall m, nat_p m -> 2 c= m -> m :e p -> forall c, nat_p c -> p <> mul_nat m c) ->
  p <> 1 /\ (forall a, nat_p a -> forall b, nat_p b -> p = mul_nat a b -> a = 1 \/ b = 1).
let p. assume Hp: nat_p p. assume Hp2: 2 c= p.
assume H: forall m, nat_p m -> 2 c= m -> m :e p -> forall c, nat_p c -> p <> mul_nat m c.
claim Lp0: p <> 0.
{ assume Hp0: p = 0. exact NatFactor_two_not_Subq_0 (NatFactor_Subq_eq 2 p 0 Hp2 Hp0). }
apply andI.
- assume Hp1: p = 1. exact NatFactor_two_not_Subq_1 (NatFactor_Subq_eq 2 p 1 Hp2 Hp1).
- let a. assume Ha: nat_p a. let b. assume Hb: nat_p b. assume Hab: p = mul_nat a b.
  claim La0: a <> 0.
  { assume Ha0: a = 0. apply Lp0. rewrite Hab. rewrite Ha0. exact mul_nat_0L b Hb. }
  claim Lb0: b <> 0.
  { assume Hb0: b = 0. apply Lp0. rewrite Hab. rewrite Hb0. exact mul_nat_0R a. }
  claim Lap: a c= p.
  { apply nat_inv b Hb.
    - assume Hb0: b = 0. apply FalseE. exact Lb0 Hb0.
    - assume Hex: exists x, nat_p x /\ b = ordsucc x.
      apply Hex. let x. assume Hx: nat_p x /\ b = ordsucc x.
      apply Hx. assume Hx1: nat_p x. assume Hx2: b = ordsucc x.
      rewrite Hab. rewrite Hx2.
      exact NatFactor_mul_Subq a Ha x Hx1. }
  apply ordinal_trichotomy_or_impred a p (nat_p_ordinal a Ha) (nat_p_ordinal p Hp).
  + assume Hap: a :e p.
    apply ordinal_In_Or_Subq a 2 (nat_p_ordinal a Ha) (nat_p_ordinal 2 nat_2).
    * assume Ha2: a :e 2.
      apply orIL.
      apply ordsuccE 1 a Ha2.
      { assume Ha1: a :e 1.
        apply ordsuccE 0 a Ha1.
        - assume Ha00: a :e 0. apply FalseE. exact EmptyE a Ha00.
        - assume Ha00: a = 0. apply FalseE. exact La0 Ha00. }
      { assume Ha1: a = 1. exact Ha1. }
    * assume Ha2: 2 c= a.
      apply FalseE.
      exact H a Ha Ha2 Hap b Hb Hab.
  + assume Hap: a = p.
    apply orIR.
    apply NatFactor_mul_cancel_one p Hp Lp0 b Hb.
    claim L1: mul_nat a b = mul_nat p b.
    { exact f_eq_i (fun z => mul_nat z b) a p Hap. }
    prove mul_nat p b = p.
    rewrite <- L1. symmetry. exact Hab.
  + assume Hpa: p :e a.
    apply FalseE.
    exact In_irref p (Lap p Hpa).
Qed.

(** A natural number below or equal to another differs from it by a natural number. **)
Theorem NatFactor_Subq_add_ex : forall m, nat_p m -> forall k, nat_p k -> m c= k ->
  exists j, nat_p j /\ k = add_nat m j.
let m. assume Hm: nat_p m.
apply nat_ind.
- assume H: m c= 0.
  witness 0. apply andI.
  + exact nat_0.
  + prove 0 = add_nat m 0. rewrite add_nat_0R m. symmetry. exact Empty_Subq_eq m H.
- let k. assume Hk: nat_p k.
  assume IH: m c= k -> exists j, nat_p j /\ k = add_nat m j.
  assume H: m c= ordsucc k.
  apply ordinal_In_Or_Subq m (ordsucc k) (nat_p_ordinal m Hm) (nat_p_ordinal (ordsucc k) (nat_ordsucc k Hk)).
  + assume Hmk: m :e ordsucc k.
    apply IH (nat_ordsucc_trans k Hk m Hmk).
    let j. assume Hj: nat_p j /\ k = add_nat m j.
    apply Hj. assume Hj1: nat_p j. assume Hj2: k = add_nat m j.
    witness (ordsucc j). apply andI.
    * exact nat_ordsucc j Hj1.
    * prove ordsucc k = add_nat m (ordsucc j).
      rewrite add_nat_SR m j Hj1.
      exact f_eq_i ordsucc k (add_nat m j) Hj2.
  + assume Hkm: ordsucc k c= m.
    witness 0. apply andI.
    * exact nat_0.
    * prove ordsucc k = add_nat m 0. rewrite add_nat_0R m.
      exact set_ext (ordsucc k) m Hkm H.
Qed.

(** Addition on the right keeps the order, and a number between n and h is n
    plus something smaller than what h is n plus. **)
Theorem NatFactor_add_In : forall n, nat_p n -> forall d, nat_p d -> forall j :e d, add_nat n j :e add_nat n d.
let n. assume Hn: nat_p n.
apply nat_ind.
- let j. assume Hj: j :e 0. apply FalseE. exact EmptyE j Hj.
- let d. assume Hd: nat_p d. assume IH: forall j :e d, add_nat n j :e add_nat n d.
  let j. assume Hj: j :e ordsucc d.
  prove add_nat n j :e add_nat n (ordsucc d).
  rewrite add_nat_SR n d Hd.
  apply ordsuccE d j Hj.
  + assume Hjd: j :e d. exact ordsuccI1 (add_nat n d) (add_nat n j) (IH j Hjd).
  + assume Hjd: j = d. rewrite Hjd. exact ordsuccI2 (add_nat n d).
Qed.

Theorem NatFactor_between_add : forall n, nat_p n -> forall h, nat_p h -> forall x, nat_p x -> n c= x -> x :e h ->
  forall Q:prop, (forall j, nat_p j -> forall d, nat_p d -> x = add_nat n j -> h = add_nat n d -> j :e d -> Q) -> Q.
let n. assume Hn: nat_p n. let h. assume Hh: nat_p h. let x. assume Hx: nat_p x.
assume Hnx: n c= x. assume Hxh: x :e h.
let Q. assume K: forall j, nat_p j -> forall d, nat_p d -> x = add_nat n j -> h = add_nat n d -> j :e d -> Q.
apply NatFactor_Subq_add_ex n Hn x Hx Hnx.
let j. assume Hj: nat_p j /\ x = add_nat n j.
apply Hj. assume Hj1: nat_p j. assume Hj2: x = add_nat n j.
claim Lsx: ordsucc x c= h.
{ exact ordinal_ordsucc_In_Subq h (nat_p_ordinal h Hh) x Hxh. }
apply NatFactor_Subq_add_ex (ordsucc x) (nat_ordsucc x Hx) h Hh Lsx.
let e. assume He: nat_p e /\ h = add_nat (ordsucc x) e.
apply He. assume He1: nat_p e. assume He2: h = add_nat (ordsucc x) e.
claim Ld: nat_p (add_nat (ordsucc j) e).
{ exact add_nat_p (ordsucc j) (nat_ordsucc j Hj1) e He1. }
apply K j Hj1 (add_nat (ordsucc j) e) Ld Hj2.
- prove h = add_nat n (add_nat (ordsucc j) e).
  rewrite <- add_nat_asso n Hn (ordsucc j) (nat_ordsucc j Hj1) e He1.
  rewrite add_nat_SR n j Hj1.
  rewrite <- Hj2.
  exact He2.
- prove j :e add_nat (ordsucc j) e.
  exact NatFactor_add_Subq (ordsucc j) e He1 j (ordsuccI2 j).
Qed.

(** A number below a square has, with every proper factorisation, a factor
    below the square's root. **)
Theorem NatFactor_mul_Subq_R : forall n, nat_p n -> forall a, nat_p a -> forall b, nat_p b -> a c= b ->
  mul_nat n a c= mul_nat n b.
let n. assume Hn: nat_p n. let a. assume Ha: nat_p a. let b. assume Hb: nat_p b. assume Hab: a c= b.
apply NatFactor_Subq_add_ex a Ha b Hb Hab.
let e. assume He: nat_p e /\ b = add_nat a e.
apply He. assume He1: nat_p e. assume He2: b = add_nat a e.
rewrite He2.
rewrite mul_add_nat_distrL n Hn a Ha e He1.
exact NatFactor_add_Subq (mul_nat n a) (mul_nat n e) (mul_nat_p n Hn e He1).
Qed.

Theorem NatFactor_mul_Subq_both : forall s, nat_p s -> forall m, nat_p m -> forall c, nat_p c ->
  s c= m -> s c= c -> mul_nat s s c= mul_nat m c.
let s. assume Hs: nat_p s. let m. assume Hm: nat_p m. let c. assume Hc: nat_p c.
assume Hsm: s c= m. assume Hsc: s c= c.
claim L1: mul_nat s s c= mul_nat s c.
{ exact NatFactor_mul_Subq_R s Hs s Hs c Hc Hsc. }
claim L2: mul_nat c s c= mul_nat c m.
{ exact NatFactor_mul_Subq_R c Hc s Hs m Hm Hsm. }
claim L3: mul_nat s c c= mul_nat m c.
{ rewrite mul_nat_com s Hs c Hc. rewrite mul_nat_com m Hm c Hc. exact L2. }
exact Subq_tra (mul_nat s s) (mul_nat s c) (mul_nat m c) L1 L3.
Qed.

Theorem NatFactor_small_divisor : forall k, nat_p k -> forall s, nat_p s -> k :e mul_nat s s ->
  (forall j :e s, 2 c= j -> forall c, nat_p c -> k <> mul_nat j c) ->
  forall m, nat_p m -> 2 c= m -> m :e k -> forall c, nat_p c -> k <> mul_nat m c.
let k. assume Hk: nat_p k. let s. assume Hs: nat_p s. assume Hks: k :e mul_nat s s.
assume H: forall j :e s, 2 c= j -> forall c, nat_p c -> k <> mul_nat j c.
let m. assume Hm: nat_p m. assume Hm2: 2 c= m. assume Hmk: m :e k.
let c. assume Hc: nat_p c. assume Hkc: k = mul_nat m c.
apply ordinal_In_Or_Subq m s (nat_p_ordinal m Hm) (nat_p_ordinal s Hs).
- assume Hms: m :e s. exact H m Hms Hm2 c Hc Hkc.
- assume Hsm: s c= m.
  claim Lc0: c <> 0.
  { assume Hc0: c = 0.
    claim Lk0: k = 0.
    { rewrite Hkc. rewrite Hc0. exact mul_nat_0R m. }
    exact EmptyE m (NatFactor_In_eq m k 0 Hmk Lk0). }
  claim Lc1: c <> 1.
  { assume Hc1: c = 1.
    claim Lkm: k = m.
    { rewrite Hkc. rewrite Hc1. exact NatFactor_mul_1R m. }
    exact In_irref m (NatFactor_In_eq m k m Hmk Lkm). }
  apply ordinal_In_Or_Subq c s (nat_p_ordinal c Hc) (nat_p_ordinal s Hs).
  + assume Hcs: c :e s.
    claim Lkc: k = mul_nat c m.
    { rewrite mul_nat_com c Hc m Hm. exact Hkc. }
    exact H c Hcs (NatFactor_two_Subq c Hc Lc0 Lc1) m Hm Lkc.
  + assume Hsc: s c= c.
    claim L: mul_nat s s c= k.
    { rewrite Hkc. exact NatFactor_mul_Subq_both s Hs m Hm c Hc Hsm Hsc. }
    exact In_irref k (L k Hks).
Qed.

Theorem NatFactor_In_square : forall t, nat_p t -> forall q, nat_p q -> mul_nat (ordsucc t) t = q ->
  forall r :e q, forall k, add_nat (ordsucc t) r = k -> k :e mul_nat (ordsucc t) (ordsucc t).
let t. assume Ht: nat_p t. let q. assume Hq: nat_p q. assume Hmul: mul_nat (ordsucc t) t = q.
let r. assume Hr: r :e q. let k. assume Hadd: add_nat (ordsucc t) r = k.
rewrite <- Hadd.
rewrite mul_nat_SR (ordsucc t) t Ht.
rewrite Hmul.
exact NatFactor_add_In (ordsucc t) (nat_ordsucc t Ht) q Hq r Hr.
Qed.
