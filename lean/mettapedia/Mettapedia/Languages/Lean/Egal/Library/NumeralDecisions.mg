(** Decisions about numerals: Nat.le and Eq between literals (LeanNum),
    read after the general facts about decidable propositions (Decidable.mg).
    For targets whose families include Nat.le and Eq. **)

(** Nat.le on numerals: reflexivity, then one step at a time. **)
Theorem Lean_Nat_le_refl_num : forall m, 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum m).
let m. exact Lean_Nat_le_refl_proof_ok (LeanNum m).
Qed.

Theorem Lean_Nat_le_succ_num : forall m n, nat_p n ->
  0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum n) -> 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum (ordsucc n)).
let m n. assume Hn: nat_p n. assume H: 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum n).
apply SepE2 1 (fun x:set => exists w, w :e Lean_Nat_le (LeanNum m) (LeanNum n)) 0 H.
let w. assume Hw: w :e Lean_Nat_le (LeanNum m) (LeanNum n).
rewrite LeanNum_S n Hn.
exact Lean_Nat_le_step_proof_ok (LeanNum m) (LeanNum n) (LeanNum_In n Hn) w Hw.
Qed.

(** At any distance: m <= m + k. **)
Theorem Lean_Nat_le_add_num : forall m, nat_p m -> forall k, nat_p k ->
  0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum (add_nat m k)).
let m. assume Hm: nat_p m.
apply nat_ind.
- prove 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum (add_nat m 0)).
  rewrite add_nat_0R m.
  exact Lean_Nat_le_refl_num m.
- let k. assume Hk: nat_p k. assume IH: 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum (add_nat m k)).
  prove 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum (add_nat m (ordsucc k))).
  rewrite add_nat_SR m k Hk.
  exact Lean_Nat_le_succ_num m (add_nat m k) (add_nat_p m Hm k Hk) IH.
Qed.

(** Every proof of Nat.le (LeanNum m) i has i = LeanNum k with m c= k:
    induction through Nat.le's recursor into Prop. **)
Theorem Lean_Nat_le_index : forall m, nat_p m -> forall i, 0 :e Lean_Nat_le_Prop (LeanNum m) i ->
  exists k, nat_p k /\ m c= k /\ i = LeanNum k.
let m. assume Hm: nat_p m. let i. assume Hi: 0 :e Lean_Nat_le_Prop (LeanNum m) i.
claim HC: forall j t, {z :e 1 | exists k, nat_p k /\ m c= k /\ j = LeanNum k} :e LeanProp.
{ let j t. exact PowerI 1 {z :e 1 | exists k, nat_p k /\ m c= k /\ j = LeanNum k}
    (Sep_Subq 1 (fun z => exists k, nat_p k /\ m c= k /\ j = LeanNum k)). }
claim H0: 0 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ LeanNum m = LeanNum k}.
{ apply SepI 1 (fun z => exists k, nat_p k /\ m c= k /\ LeanNum m = LeanNum k) 0 In_0_1.
  witness m. apply and3I.
  - exact Hm.
  - exact Subq_ref m.
  - reflexivity. }
claim LS: forall x0 :e Lean_Nat, forall x1 :e Lean_Nat_le (LeanNum m) x0,
  forall y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k},
  0 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ Lean_Nat_succ_node x0 = LeanNum k}.
{ let x0. assume Hx0: x0 :e Lean_Nat. let x1. assume Hx1: x1 :e Lean_Nat_le (LeanNum m) x0.
  let y1. assume Hy1: y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k}.
  apply SepE2 1 (fun z => exists k, nat_p k /\ m c= k /\ x0 = LeanNum k) y1 Hy1.
  let k. assume Hk: nat_p k /\ m c= k /\ x0 = LeanNum k.
  apply and3E (nat_p k) (m c= k) (x0 = LeanNum k) Hk.
  assume Hk1: nat_p k. assume Hk2: m c= k. assume Hk3: x0 = LeanNum k.
  apply SepI 1 (fun z => exists k, nat_p k /\ m c= k /\ Lean_Nat_succ_node x0 = LeanNum k) 0 In_0_1.
  witness (ordsucc k). apply and3I.
  - exact nat_ordsucc k Hk1.
  - exact Subq_tra m k (ordsucc k) Hk2 (ordsuccI1 k).
  - rewrite LeanNum_S k Hk1. rewrite Hk3. reflexivity. }
claim LP: Lean_Nat_le_prec (LeanNum m) 0 (fun x0 :e Lean_Nat => (fun x1 :e (Lean_Nat_le (LeanNum m) x0) =>
    (fun y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k} => 0))) i 0
  :e {z :e 1 | exists k, nat_p k /\ m c= k /\ i = LeanNum k}.
{ exact Lean_Nat_le_prec_type (LeanNum m) (fun j t => {z :e 1 | exists k, nat_p k /\ m c= k /\ j = LeanNum k}) HC 0 H0
    (fun x0 :e Lean_Nat => (fun x1 :e (Lean_Nat_le (LeanNum m) x0) =>
      (fun y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k} => 0)))
    (lam_Pi Lean_Nat (fun x0 => (Pi_ x1 :e (Lean_Nat_le (LeanNum m) x0), (Pi_ y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k}, {z :e 1 | exists k, nat_p k /\ m c= k /\ Lean_Nat_succ_node x0 = LeanNum k})))
      (fun x0 => (fun x1 :e (Lean_Nat_le (LeanNum m) x0) => (fun y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k} => 0)))
      (fun x0 Hx0 => lam_Pi (Lean_Nat_le (LeanNum m) x0) (fun x1 => (Pi_ y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k}, {z :e 1 | exists k, nat_p k /\ m c= k /\ Lean_Nat_succ_node x0 = LeanNum k}))
        (fun x1 => (fun y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k} => 0))
        (fun x1 Hx1 => lam_Pi {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k} (fun y1 => {z :e 1 | exists k, nat_p k /\ m c= k /\ Lean_Nat_succ_node x0 = LeanNum k})
          (fun y1 => 0) (fun y1 Hy1 => LS x0 Hx0 x1 Hx1 y1 Hy1))))
    i 0 Hi. }
exact SepE2 1 (fun z => exists k, nat_p k /\ m c= k /\ i = LeanNum k)
  (Lean_Nat_le_prec (LeanNum m) 0 (fun x0 :e Lean_Nat => (fun x1 :e (Lean_Nat_le (LeanNum m) x0) =>
    (fun y1 :e {z :e 1 | exists k, nat_p k /\ m c= k /\ x0 = LeanNum k} => 0))) i 0) LP.
Qed.

Theorem Lean_Nat_le_num_not : forall m, nat_p m -> forall n, nat_p n -> n :e m ->
  0 /:e Lean_Nat_le_Prop (LeanNum m) (LeanNum n).
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. assume Hnm: n :e m.
assume H: 0 :e Lean_Nat_le_Prop (LeanNum m) (LeanNum n).
apply Lean_Nat_le_index m Hm (LeanNum n) H.
let k. assume Hk: nat_p k /\ m c= k /\ LeanNum n = LeanNum k.
apply and3E (nat_p k) (m c= k) (LeanNum n = LeanNum k) Hk.
assume Hk1: nat_p k. assume Hk2: m c= k. assume Hk3: LeanNum n = LeanNum k.
claim Lnk: n = k.
{ exact LeanNum_inj n Hn k Hk1 Hk3. }
apply In_irref n.
claim Lk: n :e k.
{ exact Hk2 n Hnm. }
exact In_eq_r n k n (eq_sym_i n k Lnk) Lk.
Qed.

(** Eq on numerals. **)
Theorem Lean_Eq_num_refl : forall m, 0 :e Lean_Eq_Prop Lean_Nat (LeanNum m) (LeanNum m).
let m. exact Lean_Eq_refl_proof_ok Lean_Nat (LeanNum m).
Qed.

Theorem Lean_Eq_num_not : forall m, nat_p m -> forall n, nat_p n -> m <> n ->
  0 /:e Lean_Eq_Prop Lean_Nat (LeanNum m) (LeanNum n).
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. assume Hmn: m <> n.
assume H: 0 :e Lean_Eq_Prop Lean_Nat (LeanNum m) (LeanNum n).
apply Hmn. exact LeanNum_inj m Hm n Hn (LeanEq_sound Lean_Nat (LeanNum m) (LeanNum n) 0 H).
Qed.

(** Distinct ordinals: one is a member of the other. **)
Theorem neq_of_In_l : forall m n, n :e m -> m <> n.
let m n. assume H: n :e m. assume Heq: m = n.
exact In_irref n (Heq (fun a b => n :e a) H).
Qed.

Theorem neq_of_In_r : forall m n, m :e n -> m <> n.
let m n. assume H: m :e n. assume Heq: m = n.
exact In_irref m (Heq (fun a b => m :e b) H).
Qed.
