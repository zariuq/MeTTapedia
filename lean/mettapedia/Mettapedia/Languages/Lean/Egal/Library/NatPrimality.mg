(** Irreducible natural numbers, for Lean's Nat.prime_def_lt'.

    Lean's Nat.Prime p is Irreducible p in the monoid of natural numbers.
    The readings of Irreducible, IsUnit and Units are the generated ones; the
    monoid's product and unit are the fields of the instance.  Each Lean
    statement is carried to natural numbers of the theory (nat_p, mul_nat,
    inclusion), where Library/NatFactors.mg has the arithmetic. **)

Theorem LeanMonoidOf_unit : forall A operation unit power,
  (proj1 ((proj1 (Lean_MonoidOf A operation unit power)) 1)) 0 = unit.
let A operation unit power.
prove (proj1 ((proj1 (Lean_Monoid_mk_node A (Lean_SemigroupOf A operation)
  (Lean_One_mk_node A unit) 0 0 (Lean_NPow_mk_node A power) 0 0)) 1)) 0 = unit.
rewrite Lean_Monoid_mk_field1 A (Lean_SemigroupOf A operation)
  (Lean_One_mk_node A unit) 0 0 (Lean_NPow_mk_node A power) 0 0.
exact Lean_One_mk_field0 A unit.
Qed.

Theorem LeanNatMonoid_mul : forall a b :e Lean_Nat,
  (proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 a b = Lean_Nat_mul a b.
let a. assume Ha: a :e Lean_Nat. let b. assume Hb: b :e Lean_Nat.
prove (proj1 ((proj1 ((proj1 (Lean_MonoidOf Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat Lean_Nat_mul)
  (Lean_Nat_succ_node Lean_Nat_zero_node)
  (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => Lean_Nat_pow x n)))) 0)) 0)) 0 a b = Lean_Nat_mul a b.
rewrite Lean_MonoidOf_operation Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat Lean_Nat_mul)
  (Lean_Nat_succ_node Lean_Nat_zero_node)
  (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => Lean_Nat_pow x n)).
exact Lean_BinaryMap_apply Lean_Nat Lean_Nat Lean_Nat_mul a Ha b Hb.
Qed.

Theorem LeanNatMonoid_one : (proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0 = LeanNum 1.
prove (proj1 ((proj1 (Lean_MonoidOf Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat Lean_Nat_mul)
  (Lean_Nat_succ_node Lean_Nat_zero_node)
  (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => Lean_Nat_pow x n)))) 1)) 0 = LeanNum 1.
rewrite LeanMonoidOf_unit Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat Lean_Nat_mul)
  (Lean_Nat_succ_node Lean_Nat_zero_node)
  (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => Lean_Nat_pow x n)).
rewrite LeanNum_S 0 nat_0. rewrite LeanNum_0. reflexivity.
Qed.

(** Products and order between numerals. **)
Theorem LeanNat_mul_num : forall k, nat_p k -> forall j, nat_p j -> forall n, nat_p n ->
  LeanNum n = Lean_Nat_mul (LeanNum k) (LeanNum j) -> n = mul_nat k j.
let k. assume Hk: nat_p k. let j. assume Hj: nat_p j. let n. assume Hn: nat_p n.
assume H: LeanNum n = Lean_Nat_mul (LeanNum k) (LeanNum j).
apply LeanNum_inj n Hn (mul_nat k j) (mul_nat_p k Hk j Hj).
rewrite <- LeanNum_mul k Hk j Hj. exact H.
Qed.

Theorem LeanNat_le_Subq : forall m, nat_p m -> forall k, nat_p k ->
  0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum k) -> m c= k.
let m. assume Hm: nat_p m. let k. assume Hk: nat_p k.
assume H: 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum k).
apply Lean_Nat_le_index m Hm (LeanNum k) H.
let j. assume Hj: nat_p j /\ m c= j /\ LeanNum k = LeanNum j.
apply Hj. assume Hj12: nat_p j /\ m c= j. assume Hj3: LeanNum k = LeanNum j.
apply Hj12. assume Hj1: nat_p j. assume Hj2: m c= j.
claim L: k = j.
{ exact LeanNum_inj k Hk j Hj1 Hj3. }
rewrite L. exact Hj2.
Qed.

Theorem LeanNat_Subq_le : forall m, nat_p m -> forall k, nat_p k -> m c= k ->
  0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum k).
let m. assume Hm: nat_p m. let k. assume Hk: nat_p k. assume H: m c= k.
apply NatFactor_Subq_add_ex m Hm k Hk H.
let j. assume Hj: nat_p j /\ k = add_nat m j.
apply Hj. assume Hj1: nat_p j. assume Hj2: k = add_nat m j.
rewrite Hj2.
exact Lean_Nat_le_add_num m Hm j Hj1.
Qed.

Theorem LeanNat_mul_one : forall a b :e Lean_Nat, Lean_Nat_mul a b = LeanNum 1 -> a = LeanNum 1.
let a. assume Ha: a :e Lean_Nat. let b. assume Hb: b :e Lean_Nat.
assume H: Lean_Nat_mul a b = LeanNum 1.
apply Lean_Nat_num a Ha. let k. assume Hk: nat_p k /\ a = LeanNum k.
apply Hk. assume Hk1: nat_p k. assume Hk2: a = LeanNum k.
apply Lean_Nat_num b Hb. let j. assume Hj: nat_p j /\ b = LeanNum j.
apply Hj. assume Hj1: nat_p j. assume Hj2: b = LeanNum j.
claim L1: LeanNum (mul_nat k j) = LeanNum 1.
{ rewrite <- LeanNum_mul k Hk1 j Hj1. rewrite <- Hk2. rewrite <- Hj2. exact H. }
claim L2: mul_nat k j = 1.
{ exact LeanNum_inj (mul_nat k j) (mul_nat_p k Hk1 j Hj1) 1 nat_1 L1. }
claim L3: k = 1.
{ exact NatFactor_mul_one k Hk1 j Hj1 L2. }
rewrite Hk2. exact f_eq_i LeanNum k 1 L3.
Qed.

(** A disjunction proves what both of its sides prove. **)
Theorem LeanOr_elim : forall A B :e LeanProp, forall Q:prop, (0 :e A -> Q) -> (0 :e B -> Q) ->
  forall t :e Lean_Or_Prop A B, Q.
let A. assume HA: A :e LeanProp. let B. assume HB: B :e LeanProp. let Q.
assume H0: 0 :e A -> Q. assume H1: 0 :e B -> Q.
let t. assume Ht: t :e Lean_Or_Prop A B.
claim M0: (fun x0 :e A => 0) :e (Pi_ x0 :e A, {z :e 1 | Q}).
{ exact lam_Pi A (fun _ => {z :e 1 | Q}) (fun _ => 0)
    (fun x0 Hx0 => SepI 1 (fun _ => Q) 0 In_0_1 (H0 (Lean_prop_0_of A HA x0 Hx0))). }
claim M1: (fun x0 :e B => 0) :e (Pi_ x0 :e B, {z :e 1 | Q}).
{ exact lam_Pi B (fun _ => {z :e 1 | Q}) (fun _ => 0)
    (fun x0 Hx0 => SepI 1 (fun _ => Q) 0 In_0_1 (H1 (Lean_prop_0_of B HB x0 Hx0))). }
exact SepE2 1 (fun _ => Q) (Lean_Or_prec A B (fun x0 :e A => 0) (fun x0 :e B => 0) t)
  (Lean_Or_prec_type A B (fun _ => {z :e 1 | Q})
    (fun _ => PowerI 1 {z :e 1 | Q} (Sep_Subq 1 (fun _ => Q)))
    (fun x0 :e A => 0) M0 (fun x0 :e B => 0) M1 t Ht).
Qed.

(** The units of the natural numbers: one. **)
Theorem LeanNat_isUnit_elim : forall a :e Lean_Nat,
  0 :e Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a -> a = LeanNum 1.
let a. assume Ha: a :e Lean_Nat. assume H: 0 :e Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a.
claim L: forall x0 :e Lean_Nat, forall x1 :e Lean_Nat,
  forall x2 :e {z :e 1 | z :e Lean_Eq_Prop Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 x0 x1) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0)},
  forall x3 :e {z :e 1 | z :e Lean_Eq_Prop Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 x1 x0) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0)},
  0 :e Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid (Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid x0 x1 x2 x3)) a ->
  a = LeanNum 1.
{ let x0. assume H0: x0 :e Lean_Nat. let x1. assume H1: x1 :e Lean_Nat.
  let x2. assume H2: x2 :e {z :e 1 | z :e Lean_Eq_Prop Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 x0 x1) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0)}.
  let x3. assume H3: x3 :e {z :e 1 | z :e Lean_Eq_Prop Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 x1 x0) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0)}.
  assume Hv: 0 :e Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid (Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid x0 x1 x2 x3)) a.
  claim E1: (proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 x0 x1 = (proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0.
  { exact LeanEq_sound Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 x0 x1) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0) x2
      (SepE2 1 (fun z => z :e Lean_Eq_Prop Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 x0 x1) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0)) x2 H2). }
  claim E2: Lean_Nat_mul x0 x1 = LeanNum 1.
  { rewrite <- LeanNatMonoid_mul x0 H0 x1 H1. rewrite <- LeanNatMonoid_one. exact E1. }
  claim E3: x0 = LeanNum 1.
  { exact LeanNat_mul_one x0 H0 x1 H1 E2. }
  claim E4: Lean_Units_val Lean_Nat Lean_Nat_instMonoid (Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid x0 x1 x2 x3) = x0.
  { exact Lean_Units_val_mk Lean_Nat Lean_Nat_instMonoid x0 H0 x1 H1 x2 H2 x3 H3. }
  claim E5: Lean_Units_val Lean_Nat Lean_Nat_instMonoid (Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid x0 x1 x2 x3) = a.
  { exact LeanEq_sound Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid (Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid x0 x1 x2 x3)) a 0 Hv. }
  rewrite <- E5. rewrite E4. exact E3. }
apply LeanExists_elim (Lean_Units Lean_Nat Lean_Nat_instMonoid)
  (fun v_u :e (Lean_Units Lean_Nat Lean_Nat_instMonoid) => (Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid v_u) a))
  (a = LeanNum 1).
- let u. assume Hu: u :e Lean_Units Lean_Nat Lean_Nat_instMonoid.
  assume Hp: 0 :e (fun v_u :e (Lean_Units Lean_Nat Lean_Nat_instMonoid) => (Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid v_u) a)) u.
  claim Hval: 0 :e Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid u) a.
  { rewrite <- beta (Lean_Units Lean_Nat Lean_Nat_instMonoid)
      (fun v_u => Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid v_u) a) u Hu.
    exact Hp. }
  exact Lean_Units_ind Lean_Nat Lean_Nat_instMonoid
    (fun u => 0 :e Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid u) a -> a = LeanNum 1)
    L u Hu Hval.
- exact H.
Qed.

Theorem LeanNat_isUnit_intro : 0 :e Lean_IsUnit Lean_Nat Lean_Nat_instMonoid (LeanNum 1).
claim H1: LeanNum 1 :e Lean_Nat.
{ exact LeanNum_In 1 nat_1. }
claim Emul: (proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 (LeanNum 1) (LeanNum 1) = (proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0.
{ rewrite LeanNatMonoid_mul (LeanNum 1) H1 (LeanNum 1) H1. rewrite LeanNatMonoid_one.
  exact LeanNum_mul_eq 1 nat_1 1 nat_1 1 (NatFactor_mul_1R 1). }
claim G: 0 :e {z :e 1 | z :e Lean_Eq_Prop Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 (LeanNum 1) (LeanNum 1)) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0)}.
{ exact SepI 1 (fun z => z :e Lean_Eq_Prop Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 (LeanNum 1) (LeanNum 1)) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0)) 0 In_0_1
    (Lean_Eq_proof_of Lean_Nat ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 (LeanNum 1) (LeanNum 1)) ((proj1 ((proj1 Lean_Nat_instMonoid) 1)) 0) Emul). }
claim Hu: Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid (LeanNum 1) (LeanNum 1) 0 0 :e Lean_Units Lean_Nat Lean_Nat_instMonoid.
{ exact Lean_Units_mk_typed Lean_Nat Lean_Nat_instMonoid (LeanNum 1) H1 (LeanNum 1) H1 0 G 0 G. }
prove 0 :e Lean_Exists_Prop (Lean_Units Lean_Nat Lean_Nat_instMonoid)
  (fun v_u :e (Lean_Units Lean_Nat Lean_Nat_instMonoid) => (Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid v_u) (LeanNum 1))).
apply LeanExists_intro (Lean_Units Lean_Nat Lean_Nat_instMonoid)
  (fun v_u :e (Lean_Units Lean_Nat Lean_Nat_instMonoid) => (Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid v_u) (LeanNum 1)))
  (Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid (LeanNum 1) (LeanNum 1) 0 0) Hu.
rewrite beta (Lean_Units Lean_Nat Lean_Nat_instMonoid)
  (fun v_u => Lean_Eq_Prop Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid v_u) (LeanNum 1))
  (Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid (LeanNum 1) (LeanNum 1) 0 0) Hu.
apply Lean_Eq_proof_of Lean_Nat (Lean_Units_val Lean_Nat Lean_Nat_instMonoid (Lean_Units_mk_node Lean_Nat Lean_Nat_instMonoid (LeanNum 1) (LeanNum 1) 0 0)) (LeanNum 1).
exact Lean_Units_val_mk Lean_Nat Lean_Nat_instMonoid (LeanNum 1) H1 (LeanNum 1) H1 0 G 0 G.
Qed.

(** Irreducible in the natural numbers, in elementary terms. **)
Theorem LeanNat_irreducible_elim : forall p :e Lean_Nat,
  0 :e Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid p ->
  p <> LeanNum 1 /\ (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1).
let p. assume Hp: p :e Lean_Nat. assume H: 0 :e Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid p.
claim L: forall x0 :e (Pi_ ux :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p), Lean_False_Prop), forall x1 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))}, (p <> LeanNum 1 /\ (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1)).
{ let x0. assume H0: x0 :e (Pi_ ux :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p), Lean_False_Prop). let x1. assume H1: x1 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))}.
  apply andI.
  - assume Hp1: p = LeanNum 1.
    claim Hu: 0 :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p).
    { rewrite Hp1. exact LeanNat_isUnit_intro. }
    exact Lean_False_Prop_empty (x0 0) (ap_Pi (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p) (fun _ => Lean_False_Prop) x0 0 H0 Hu).
  - let a. assume Ha: a :e Lean_Nat. let b. assume Hb: b :e Lean_Nat. assume Hab: p = Lean_Nat_mul a b.
    claim Hg: x1 :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1))))).
    { exact SepE2 1 (fun z => z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))) x1 H1. }
    claim Hga: x1 a :e (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 a q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))).
    { exact ap_Pi Lean_Nat (fun q0 => (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1))))) x1 a Hg Ha. }
    claim Hgab: x1 a b :e (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 a b)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid b))).
    { exact ap_Pi Lean_Nat (fun q1 => (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 a q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))) (x1 a) b Hga Hb. }
    claim He: 0 :e Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 a b).
    { apply Lean_Eq_proof_of Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 a b). rewrite LeanNatMonoid_mul a Ha b Hb. exact Hab. }
    claim Hor: x1 a b 0 :e (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid b)).
    { exact ap_Pi (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 a b)) (fun _ => (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid b))) (x1 a b) 0 Hgab He. }
    exact LeanOr_elim (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a) (Lean_IsUnit_In Lean_Nat Lean_Nat_instMonoid Lean_Nat_instMonoid_In a Ha) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid b) (Lean_IsUnit_In Lean_Nat Lean_Nat_instMonoid Lean_Nat_instMonoid_In b Hb) (a = LeanNum 1 \/ b = LeanNum 1)
      (fun Hua: 0 :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid a) => orIL (a = LeanNum 1) (b = LeanNum 1) (LeanNat_isUnit_elim a Ha Hua))
      (fun Hub: 0 :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid b) => orIR (a = LeanNum 1) (b = LeanNum 1) (LeanNat_isUnit_elim b Hb Hub))
      (x1 a b 0) Hor. }
apply SepE2 1 (fun _ => exists w, w :e Lean_Irreducible Lean_Nat Lean_Nat_instMonoid p) 0 H.
let w. assume Hw: w :e Lean_Irreducible Lean_Nat Lean_Nat_instMonoid p.
claim Hh0: (fun x0 :e (Pi_ ux :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p), Lean_False_Prop) => (fun x1 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))} => 0)) :e (Pi_ x0 :e (Pi_ ux :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p), Lean_False_Prop), (Pi_ x1 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))}, {z :e 1 | (p <> LeanNum 1 /\ (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1))})).
{ exact lam_Pi (Pi_ ux :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p), Lean_False_Prop) (fun _ => (Pi_ x1 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))}, {z :e 1 | (p <> LeanNum 1 /\ (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1))})) (fun _ => (fun x1 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))} => 0))
    (fun x0 Hx0 => lam_Pi {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))} (fun _ => {z :e 1 | (p <> LeanNum 1 /\ (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1))}) (fun _ => 0)
      (fun x1 Hx1 => SepI 1 (fun _ => (p <> LeanNum 1 /\ (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1))) 0 In_0_1 (L x0 Hx0 x1 Hx1))). }
exact SepE2 1 (fun _ => (p <> LeanNum 1 /\ (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1))) (Lean_Irreducible_rec Lean_Nat Lean_Nat_instMonoid p (fun x0 :e (Pi_ ux :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p), Lean_False_Prop) => (fun x1 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))} => 0)) w)
  (Lean_Irreducible_rec_type Lean_Nat Lean_Nat_instMonoid p (fun _ => {z :e 1 | (p <> LeanNum 1 /\ (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1))}) (fun x0 :e (Pi_ ux :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p), Lean_False_Prop) => (fun x1 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))} => 0)) Hh0 w Hw).
Qed.

Theorem LeanNat_irreducible_intro : forall p :e Lean_Nat, p <> LeanNum 1 ->
  (forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1) ->
  0 :e Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid p.
let p. assume Hp: p :e Lean_Nat. assume Hp1: p <> LeanNum 1.
assume Hf: forall a b :e Lean_Nat, p = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1.
claim H0: 0 :e (Pi_ ux :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p), Lean_False_Prop).
{ exact Lean_refute_0 (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p) (Lean_IsUnit_In Lean_Nat Lean_Nat_instMonoid Lean_Nat_instMonoid_In p Hp) (fun Hu: 0 :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid p) => Hp1 (LeanNat_isUnit_elim p Hp Hu)). }
claim L2: forall q0 :e Lean_Nat, forall q1 :e Lean_Nat, forall q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), 0 :e (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)).
{ let q0. assume Hq0: q0 :e Lean_Nat. let q1. assume Hq1: q1 :e Lean_Nat.
  let q2. assume Hq2: q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)).
  claim E: p = Lean_Nat_mul q0 q1.
  { rewrite <- LeanNatMonoid_mul q0 Hq0 q1 Hq1. exact LeanEq_sound Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1) q2 Hq2. }
  apply Hf q0 Hq0 q1 Hq1 E.
  - assume Hq: q0 = LeanNum 1.
    claim Hu: 0 :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0).
    { rewrite Hq. exact LeanNat_isUnit_intro. }
    exact Lean_Or_inl_proof_ok (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1) 0 Hu.
  - assume Hq: q1 = LeanNum 1.
    claim Hu: 0 :e (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1).
    { rewrite Hq. exact LeanNat_isUnit_intro. }
    exact Lean_Or_inr_proof_ok (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1) 0 Hu. }
claim H1b: 0 :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1))))).
{ exact Pi_0_In Lean_Nat (fun q0 => (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))
    (fun q0 Hq0 => Pi_0_In Lean_Nat (fun q1 => (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1))))
      (fun q1 Hq1 => Pi_0_In (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)) (fun _ => (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))
        (fun q2 Hq2 => L2 q0 Hq0 q1 Hq1 q2 Hq2))). }
claim H1: 0 :e {z :e 1 | z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))}.
{ exact SepI 1 (fun z => z :e (Pi_ q0 :e Lean_Nat, (Pi_ q1 :e Lean_Nat, (Pi_ q2 :e (Lean_Eq_Prop Lean_Nat p ((proj1 ((proj1 ((proj1 Lean_Nat_instMonoid) 0)) 0)) 0 q0 q1)), (Lean_Or_Prop (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q0) (Lean_IsUnit Lean_Nat Lean_Nat_instMonoid q1)))))) 0 In_0_1 H1b. }
exact SepI 1 (fun _ => exists w, w :e Lean_Irreducible Lean_Nat Lean_Nat_instMonoid p) 0 In_0_1
  (fun P K => K (Lean_Irreducible_mk_node Lean_Nat Lean_Nat_instMonoid p 0 0) (Lean_Irreducible_mk_typed Lean_Nat Lean_Nat_instMonoid p 0 H0 0 H1)).
Qed.

(** The hypotheses of Lean's statement, between numerals. **)
Theorem LeanNat_le_two : forall j, nat_p j -> forall x :e (Lean_Nat_le_Prop (LeanNum 2) (LeanNum j)), 2 c= j.
let j. assume Hj: nat_p j. let x. assume Hx: x :e (Lean_Nat_le_Prop (LeanNum 2) (LeanNum j)).
exact LeanNat_le_Subq 2 nat_2 j Hj (Lean_prop_0_of (Lean_Nat_le_Prop (LeanNum 2) (LeanNum j)) (Lean_Nat_le_Prop_prop (LeanNum 2) (LeanNum j)) x Hx).
Qed.

Theorem LeanNat_lt_In : forall j, nat_p j -> forall k, nat_p k ->
  0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k) -> j :e k.
let j. assume Hj: nat_p j. let k. assume Hk: nat_p k.
assume H: 0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k).
claim L: 0 :e Lean_Nat_le_Prop (LeanNum (ordsucc j)) (LeanNum k).
{ rewrite LeanNum_S j Hj. exact H. }
exact LeanNat_le_Subq (ordsucc j) (nat_ordsucc j Hj) k Hk L j (ordsuccI2 j).
Qed.

Theorem LeanNat_In_lt : forall j, nat_p j -> forall k, nat_p k -> j :e k ->
  0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k).
let j. assume Hj: nat_p j. let k. assume Hk: nat_p k. assume Hjk: j :e k.
rewrite <- LeanNum_S j Hj.
exact LeanNat_Subq_le (ordsucc j) (nat_ordsucc j Hj) k Hk (ordinal_ordsucc_In_Subq k (nat_p_ordinal k Hk) j Hjk).
Qed.

Theorem LeanNat_divides_elim : forall k, nat_p k -> forall j, nat_p j ->
  0 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))) -> exists i, nat_p i /\ k = mul_nat j i.
let k. assume Hk: nat_p k. let j. assume Hj: nat_p j. assume H: 0 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))).
apply LeanExists_elim Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c))) (exists i, nat_p i /\ k = mul_nat j i).
- let c. assume Hc: c :e Lean_Nat. assume Hpc: 0 :e (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c))) c.
  claim E: (LeanNum k) = Lean_Nat_mul (LeanNum j) c.
  { apply LeanEq_sound Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) c) 0.
    rewrite <- beta Lean_Nat (fun v_c => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c))) c Hc.
    exact Hpc. }
  apply Lean_Nat_num c Hc. let i. assume Hi: nat_p i /\ c = LeanNum i.
  apply Hi. assume Hi1: nat_p i. assume Hi2: c = LeanNum i.
  witness i. apply andI.
  + exact Hi1.
  + apply LeanNat_mul_num j Hj i Hi1 k Hk. rewrite <- Hi2. exact E.
- exact H.
Qed.

Theorem LeanNat_divides_intro : forall k, nat_p k -> forall j, nat_p j -> forall i, nat_p i ->
  k = mul_nat j i -> 0 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))).
let k. assume Hk: nat_p k. let j. assume Hj: nat_p j. let i. assume Hi: nat_p i. assume H: k = mul_nat j i.
apply LeanExists_intro Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c))) (LeanNum i) (LeanNum_In i Hi).
rewrite beta Lean_Nat (fun v_c => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c))) (LeanNum i) (LeanNum_In i Hi).
apply Lean_Eq_proof_of Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) (LeanNum i)).
rewrite H. symmetry. exact LeanNum_mul j Hj i Hi.
Qed.

(** Lean's Nat.prime_def_lt' at a numeral, in each direction. **)
Theorem LeanNat_bounded_of_irreducible : forall k, nat_p k -> 0 :e (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)) -> 0 :e (Lean_And_Prop (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))))).
let k. assume Hk: nat_p k. assume H: 0 :e (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)).
claim Hp: (LeanNum k) :e Lean_Nat.
{ exact LeanNum_In k Hk. }
apply LeanNat_irreducible_elim (LeanNum k) Hp H.
assume E1: (LeanNum k) <> LeanNum 1.
assume E2: forall a b :e Lean_Nat, (LeanNum k) = Lean_Nat_mul a b -> a = LeanNum 1 \/ b = LeanNum 1.
claim N1: k <> 1.
{ assume Hk1: k = 1. apply E1. exact f_eq_i LeanNum k 1 Hk1. }
claim N2: forall a, nat_p a -> forall b, nat_p b -> k = mul_nat a b -> a = 1 \/ b = 1.
{ let a. assume Ha: nat_p a. let b. assume Hb: nat_p b. assume Hab: k = mul_nat a b.
  claim L: (LeanNum k) = Lean_Nat_mul (LeanNum a) (LeanNum b).
  { rewrite Hab. symmetry. exact LeanNum_mul a Ha b Hb. }
  apply E2 (LeanNum a) (LeanNum_In a Ha) (LeanNum b) (LeanNum_In b Hb) L.
  - assume Ha1: LeanNum a = LeanNum 1. apply orIL. exact LeanNum_inj a Ha 1 nat_1 Ha1.
  - assume Hb1: LeanNum b = LeanNum 1. apply orIR. exact LeanNum_inj b Hb 1 nat_1 Hb1. }
apply NatFactor_irreducible_bounded k Hk N1 N2.
assume B1: 2 c= k.
assume B2: forall m, nat_p m -> 2 c= m -> m :e k -> forall c, nat_p c -> k <> mul_nat m c.
claim C: forall m :e Lean_Nat, forall x :e (Lean_Nat_le_Prop (LeanNum 2) m), forall y :e (Lean_Nat_le_Prop (Lean_Nat_succ_node m) (LeanNum k)), forall z :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul m v_c)))), False.
{ let m. assume Hm: m :e Lean_Nat.
  apply Lean_Nat_num m Hm. let j. assume Hj: nat_p j /\ m = LeanNum j.
  apply Hj. assume Hj1: nat_p j. assume Hj2: m = LeanNum j.
  rewrite Hj2.
  let x. assume Hx: x :e (Lean_Nat_le_Prop (LeanNum 2) (LeanNum j)). let y. assume Hy: y :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k)). let z. assume Hz: z :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))).
  claim J2: 2 c= j.
  { exact LeanNat_le_two j Hj1 x Hx. }
  claim Jk: j :e k.
  { exact LeanNat_lt_In j Hj1 k Hk (Lean_prop_0_of (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k)) (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k)) y Hy). }
  apply LeanNat_divides_elim k Hk j Hj1 (Lean_prop_0_of (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))) (Lean_Exists_Prop_prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))) z Hz).
  let i. assume Hi: nat_p i /\ k = mul_nat j i.
  apply Hi. assume Hi1: nat_p i. assume Hi2: k = mul_nat j i.
  exact B2 j Hj1 J2 Jk i Hi1 Hi2. }
exact Lean_And_intro_proof_ok (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) 0 (LeanNat_Subq_le 2 nat_2 k Hk B1) 0
  (Pi_0_In Lean_Nat (fun v_m => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))))
    (fun m Hm => Pi_0_In (Lean_Nat_le_Prop (LeanNum 2) m) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul m v_c)))), Lean_False_Prop)))
      (fun x Hx => Pi_0_In (Lean_Nat_le_Prop (Lean_Nat_succ_node m) (LeanNum k)) (fun _ => (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul m v_c)))), Lean_False_Prop))
        (fun y Hy => Pi_0_In (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul m v_c)))) (fun _ => Lean_False_Prop)
          (fun z Hz => FalseE (C m Hm x Hx y Hy z Hz) (0 :e Lean_False_Prop)))))).
Qed.

Theorem LeanNat_irreducible_of_bounded : forall k, nat_p k -> 0 :e (Lean_And_Prop (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))))) -> 0 :e (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)).
let k. assume Hk: nat_p k. assume H: 0 :e (Lean_And_Prop (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))))).
claim HL: 0 :e (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)).
{ exact LeanAnd_left (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Lean_Nat_le_Prop_prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) (LeanPi_prop Lean_Nat (fun v_m => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) (fun v_m Hv_m => (LeanPi_prop (Lean_Nat_le_Prop (LeanNum 2) v_m) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))) (fun x Hx => LeanPi_prop (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)) (fun _ => (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)) (fun y Hy => LeanPi_prop (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))) (fun _ => Lean_False_Prop) (fun z Hz => Lean_False_Prop_prop)))))) 0 H. }
claim HA: 0 :e (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))).
{ exact LeanAnd_right (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Lean_Nat_le_Prop_prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) (LeanPi_prop Lean_Nat (fun v_m => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) (fun v_m Hv_m => (LeanPi_prop (Lean_Nat_le_Prop (LeanNum 2) v_m) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))) (fun x Hx => LeanPi_prop (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)) (fun _ => (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)) (fun y Hy => LeanPi_prop (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))) (fun _ => Lean_False_Prop) (fun z Hz => Lean_False_Prop_prop)))))) 0 H. }
claim B1: 2 c= k.
{ exact LeanNat_le_Subq 2 nat_2 k Hk HL. }
claim B2: forall m, nat_p m -> 2 c= m -> m :e k -> forall c, nat_p c -> k <> mul_nat m c.
{ let m. assume Hm: nat_p m. assume Hm2: 2 c= m. assume Hmk: m :e k.
  let c. assume Hc: nat_p c. assume Hkc: k = mul_nat m c.
  claim U0: 0 (LeanNum m) :e (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) (LeanNum m)), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum m)) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop))).
  { exact ap_Pi Lean_Nat (fun v_m => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) 0 (LeanNum m) HA (LeanNum_In m Hm). }
  claim U1: 0 (LeanNum m) 0 :e (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum m)) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop)).
  { exact ap_Pi (Lean_Nat_le_Prop (LeanNum 2) (LeanNum m)) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum m)) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop))) (0 (LeanNum m)) 0 U0 (LeanNat_Subq_le 2 nat_2 m Hm Hm2). }
  claim U2: 0 (LeanNum m) 0 0 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop).
  { exact ap_Pi (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum m)) (LeanNum k)) (fun _ => (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop)) (0 (LeanNum m) 0) 0 U1 (LeanNat_In_lt m Hm k Hk Hmk). }
  claim U3: 0 (LeanNum m) 0 0 0 :e Lean_False_Prop.
  { exact ap_Pi (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))) (fun _ => Lean_False_Prop) (0 (LeanNum m) 0 0) 0 U2 (LeanNat_divides_intro k Hk m Hm c Hc Hkc). }
  exact Lean_False_Prop_empty (0 (LeanNum m) 0 0 0) U3. }
apply NatFactor_bounded_irreducible k Hk B1 B2.
assume N1: k <> 1.
assume N2: forall a, nat_p a -> forall b, nat_p b -> k = mul_nat a b -> a = 1 \/ b = 1.
apply LeanNat_irreducible_intro (LeanNum k) (LeanNum_In k Hk).
- assume Hk1: (LeanNum k) = LeanNum 1. exact N1 (LeanNum_inj k Hk 1 nat_1 Hk1).
- let a. assume Ha: a :e Lean_Nat. let b. assume Hb: b :e Lean_Nat. assume Hab: (LeanNum k) = Lean_Nat_mul a b.
  apply Lean_Nat_num a Ha. let ka. assume Hka: nat_p ka /\ a = LeanNum ka.
  apply Hka. assume Ha1: nat_p ka. assume Ha2: a = LeanNum ka.
  apply Lean_Nat_num b Hb. let kb. assume Hkb: nat_p kb /\ b = LeanNum kb.
  apply Hkb. assume Hb1: nat_p kb. assume Hb2: b = LeanNum kb.
  claim L: k = mul_nat ka kb.
  { apply LeanNat_mul_num ka Ha1 kb Hb1 k Hk. rewrite <- Ha2. rewrite <- Hb2. exact Hab. }
  apply N2 ka Ha1 kb Hb1 L.
  + assume E: ka = 1. apply orIL. rewrite Ha2. exact f_eq_i LeanNum ka 1 E.
  + assume E: kb = 1. apply orIR. rewrite Hb2. exact f_eq_i LeanNum kb 1 E.
Qed.

(** Lean's Nat.prime_def_lt': a natural number is irreducible exactly when it
    is at least two and no number from two up to it divides it. **)
Theorem LeanNat_prime_def_lt : forall p :e Lean_Nat, 0 :e (Lean_Iff_Prop (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid p) (Lean_And_Prop (Lean_Nat_le_Prop (LeanNum 2) p) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) p), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat p (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))))).
let p. assume Hp: p :e Lean_Nat.
apply Lean_Nat_num p Hp. let k. assume Hk: nat_p k /\ p = LeanNum k.
apply Hk. assume Hk1: nat_p k. assume Hk2: p = LeanNum k.
rewrite Hk2.
exact LeanIff_intro (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)) (Lean_Irreducible_Prop_prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)) (Lean_And_Prop (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))))) (Lean_And_Prop_prop (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))))
  (LeanNat_bounded_of_irreducible k Hk1) (LeanNat_irreducible_of_bounded k Hk1).
Qed.

(** Deciding a numeral: it is irreducible when it is at least two and no
    smaller number from two on divides it, each case refuted on its own; it
    is not when one such number does. **)
Theorem LeanNat_prime_by_cases : forall k, nat_p k -> 2 c= k ->
  (forall j :e k, 2 c= j -> 0 /:e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c))))) -> 0 :e (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)).
let k. assume Hk: nat_p k. assume Hk2: 2 c= k.
assume Hc: forall j :e k, 2 c= j -> 0 /:e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))).
apply LeanNat_irreducible_of_bounded k Hk.
claim C: forall m :e Lean_Nat, forall x :e (Lean_Nat_le_Prop (LeanNum 2) m), forall y :e (Lean_Nat_le_Prop (Lean_Nat_succ_node m) (LeanNum k)), forall z :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul m v_c)))), False.
{ let m. assume Hm: m :e Lean_Nat.
  apply Lean_Nat_num m Hm. let j. assume Hj: nat_p j /\ m = LeanNum j.
  apply Hj. assume Hj1: nat_p j. assume Hj2: m = LeanNum j.
  rewrite Hj2.
  let x. assume Hx: x :e (Lean_Nat_le_Prop (LeanNum 2) (LeanNum j)). let y. assume Hy: y :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k)). let z. assume Hz: z :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))).
  claim J2: 2 c= j.
  { exact LeanNat_le_two j Hj1 x Hx. }
  claim Jk: j :e k.
  { exact LeanNat_lt_In j Hj1 k Hk (Lean_prop_0_of (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k)) (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum k)) y Hy). }
  exact Hc j Jk J2 (Lean_prop_0_of (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))) (Lean_Exists_Prop_prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))) z Hz). }
exact Lean_And_intro_proof_ok (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) 0 (LeanNat_Subq_le 2 nat_2 k Hk Hk2) 0
  (Pi_0_In Lean_Nat (fun v_m => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))))
    (fun m Hm => Pi_0_In (Lean_Nat_le_Prop (LeanNum 2) m) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul m v_c)))), Lean_False_Prop)))
      (fun x Hx => Pi_0_In (Lean_Nat_le_Prop (Lean_Nat_succ_node m) (LeanNum k)) (fun _ => (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul m v_c)))), Lean_False_Prop))
        (fun y Hy => Pi_0_In (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul m v_c)))) (fun _ => Lean_False_Prop)
          (fun z Hz => FalseE (C m Hm x Hx y Hy z Hz) (0 :e Lean_False_Prop)))))).
Qed.

Theorem LeanNat_composite : forall k, nat_p k -> forall m, nat_p m -> forall c, nat_p c ->
  2 c= m -> m :e k -> mul_nat m c = k -> 0 /:e (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)).
let k. assume Hk: nat_p k. let m. assume Hm: nat_p m. let c. assume Hc: nat_p c.
assume Hm2: 2 c= m. assume Hmk: m :e k. assume Hmul: mul_nat m c = k.
claim Hkc: k = mul_nat m c.
{ symmetry. exact Hmul. }
assume H: 0 :e (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)).
claim R: 0 :e (Lean_And_Prop (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))))).
{ exact LeanNat_bounded_of_irreducible k Hk H. }
claim HA: 0 :e (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))).
{ exact LeanAnd_right (Lean_Nat_le_Prop (LeanNum 2) (LeanNum k)) (Lean_Nat_le_Prop_prop (LeanNum 2) (LeanNum k)) (Pi_ v_m :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) (LeanPi_prop Lean_Nat (fun v_m => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) (fun v_m Hv_m => (LeanPi_prop (Lean_Nat_le_Prop (LeanNum 2) v_m) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop))) (fun x Hx => LeanPi_prop (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)) (fun _ => (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)) (fun y Hy => LeanPi_prop (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))) (fun _ => Lean_False_Prop) (fun z Hz => Lean_False_Prop_prop)))))) 0 R. }
claim U0: 0 (LeanNum m) :e (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) (LeanNum m)), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum m)) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop))).
{ exact ap_Pi Lean_Nat (fun v_m => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum 2) v_m), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_m) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul v_m v_c)))), Lean_False_Prop)))) 0 (LeanNum m) HA (LeanNum_In m Hm). }
claim U1: 0 (LeanNum m) 0 :e (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum m)) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop)).
{ exact ap_Pi (Lean_Nat_le_Prop (LeanNum 2) (LeanNum m)) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum m)) (LeanNum k)), (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop))) (0 (LeanNum m)) 0 U0 (LeanNat_Subq_le 2 nat_2 m Hm Hm2). }
claim U2: 0 (LeanNum m) 0 0 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop).
{ exact ap_Pi (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum m)) (LeanNum k)) (fun _ => (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))), Lean_False_Prop)) (0 (LeanNum m) 0) 0 U1 (LeanNat_In_lt m Hm k Hk Hmk). }
claim U3: 0 (LeanNum m) 0 0 0 :e Lean_False_Prop.
{ exact ap_Pi (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum m) v_c)))) (fun _ => Lean_False_Prop) (0 (LeanNum m) 0 0) 0 U2 (LeanNat_divides_intro k Hk m Hm c Hc Hkc). }
exact Lean_False_Prop_empty (0 (LeanNum m) 0 0 0) U3.
Qed.

(** The same with the cases up to the root only: a numeral below the square
    of s is irreducible when no number from two up to s divides it. **)
Theorem LeanNat_prime_by_small_cases : forall k, nat_p k -> forall s, nat_p s -> 2 c= k -> k :e mul_nat s s ->
  (forall j :e s, 2 c= j -> 0 /:e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c))))) -> 0 :e (Lean_Irreducible_Prop Lean_Nat Lean_Nat_instMonoid (LeanNum k)).
let k. assume Hk: nat_p k. let s. assume Hs: nat_p s. assume Hk2: 2 c= k. assume Hks: k :e mul_nat s s.
assume Hsmall: forall j :e s, 2 c= j -> 0 /:e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))).
claim Hn: forall j :e s, 2 c= j -> forall c, nat_p c -> k <> mul_nat j c.
{ let j. assume Hjs: j :e s. assume Hj2: 2 c= j. let c. assume Hc: nat_p c. assume Hkc: k = mul_nat j c.
  exact Hsmall j Hjs Hj2 (LeanNat_divides_intro k Hk j (nat_p_trans s Hs j Hjs) c Hc Hkc). }
apply LeanNat_prime_by_cases k Hk Hk2.
let j. assume Hjk: j :e k. assume Hj2: 2 c= j. assume Hex: 0 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum k) (Lean_Nat_mul (LeanNum j) v_c)))).
claim Hj: nat_p j.
{ exact nat_p_trans k Hk j Hjk. }
apply LeanNat_divides_elim k Hk j Hj Hex.
let i. assume Hi: nat_p i /\ k = mul_nat j i.
apply Hi. assume Hi1: nat_p i. assume Hi2: k = mul_nat j i.
exact NatFactor_small_divisor k Hk s Hs Hks Hn j Hj Hj2 Hjk i Hi1 Hi2.
Qed.
