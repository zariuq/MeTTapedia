(** Lean's order on natural numbers as its instance writes it: a < b is
    LT.lt at the instance instLTNat, whose relation is Nat.le (a + 1) b. **)

Theorem LeanNat_lt_le : forall a b :e Lean_Nat,
  Lean_LT_lt Lean_Nat Lean_instLTNat a b = Lean_Nat_le_Prop (Lean_Nat_succ_node a) b.
let a. assume Ha: a :e Lean_Nat. let b. assume Hb: b :e Lean_Nat.
claim Hrel: (fun v_n :e Lean_Nat => (Sigma Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n))))
  :e (Pi_ ux :e Lean_Nat, (Pi_ ux :e Lean_Nat, LeanProp)).
{ exact lam_Pi Lean_Nat (fun _ => (Pi_ ux :e Lean_Nat, LeanProp))
    (fun v_n => (Sigma Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n))))
    (fun v_n Hn => lam_Pi Lean_Nat (fun _ => LeanProp) (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n))
      (fun m Hm => Lean_Nat_le_Prop_prop (Lean_Nat_succ_node v_n) m)). }
rewrite Lean_instLTNat_unfold.
rewrite Lean_LT_lt_mk Lean_Nat (fun v_n :e Lean_Nat => (Sigma Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n)))) Hrel.
rewrite beta Lean_Nat (fun v_n => (Sigma Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n)))) a Ha.
rewrite beta Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node a)) b Hb.
reflexivity.
Qed.

(** Nat.le between any two natural numbers of Lean, by their numerals. **)
Theorem LeanNat_le_succ_right : forall a b :e Lean_Nat,
  0 :e Lean_Nat_le_Prop a b -> 0 :e Lean_Nat_le_Prop a (Lean_Nat_succ_node b).
let a. assume Ha: a :e Lean_Nat. let b. assume Hb: b :e Lean_Nat.
assume H: 0 :e Lean_Nat_le_Prop a b.
apply Lean_Nat_num a Ha. let k. assume Hk: nat_p k /\ a = LeanNum k.
apply Hk. assume Hk1: nat_p k. assume Hk2: a = LeanNum k.
apply Lean_Nat_num b Hb. let j. assume Hj: nat_p j /\ b = LeanNum j.
apply Hj. assume Hj1: nat_p j. assume Hj2: b = LeanNum j.
claim L: 0 :e Lean_Nat_le_Prop (LeanNum k) (LeanNum j).
{ rewrite <- Hk2. rewrite <- Hj2. exact H. }
rewrite Hk2. rewrite Hj2. rewrite <- LeanNum_S j Hj1.
exact Lean_Nat_le_succ_num k j Hj1 L.
Qed.

Theorem LeanNat_lt_succ_of_lt : forall a b :e Lean_Nat,
  0 :e (Lean_LT_lt Lean_Nat Lean_instLTNat a b) -> 0 :e (Lean_LT_lt Lean_Nat Lean_instLTNat a (Lean_Nat_succ_node b)).
let a. assume Ha: a :e Lean_Nat. let b. assume Hb: b :e Lean_Nat.
assume H: 0 :e (Lean_LT_lt Lean_Nat Lean_instLTNat a b).
claim Hsb: Lean_Nat_succ_node b :e Lean_Nat.
{ exact Lean_Nat_succ_typed b Hb. }
rewrite LeanNat_lt_le a Ha (Lean_Nat_succ_node b) Hsb.
apply LeanNat_le_succ_right (Lean_Nat_succ_node a) (Lean_Nat_succ_typed a Ha) b Hb.
rewrite <- LeanNat_lt_le a Ha b Hb. exact H.
Qed.

(** Subtraction between numerals, as Lean's Nat.sub computes it. **)
Theorem LeanNat_sub_add_num : forall n, nat_p n -> forall d, nat_p d ->
  Lean_Nat_sub (LeanNum (add_nat n d)) (LeanNum n) = LeanNum d.
let n. assume Hn: nat_p n. let d. assume Hd: nat_p d.
rewrite add_nat_com n Hn d Hd.
exact LeanNum_sub_add n Hn d Hd.
Qed.

Theorem LeanNat_sub_self_add : forall a, nat_p a -> forall e, nat_p e ->
  Lean_Nat_sub (LeanNum a) (LeanNum (add_nat a e)) = LeanNum 0.
let a. assume Ha: nat_p a.
apply nat_ind.
- prove Lean_Nat_sub (LeanNum a) (LeanNum (add_nat a 0)) = LeanNum 0.
  rewrite add_nat_0R a.
  claim L1: Lean_Nat_sub (LeanNum (add_nat 0 a)) (LeanNum a) = LeanNum 0.
  { exact LeanNum_sub_add a Ha 0 nat_0. }
  claim L2: Lean_Nat_sub (LeanNum (add_nat 0 a)) (LeanNum a) = Lean_Nat_sub (LeanNum a) (LeanNum a).
  { exact f_eq_i (fun z => Lean_Nat_sub (LeanNum z) (LeanNum a)) (add_nat 0 a) a (add_nat_0L a Ha). }
  rewrite <- L2. exact L1.
- let e. assume He: nat_p e.
  assume IH: Lean_Nat_sub (LeanNum a) (LeanNum (add_nat a e)) = LeanNum 0.
  prove Lean_Nat_sub (LeanNum a) (LeanNum (add_nat a (ordsucc e))) = LeanNum 0.
  rewrite add_nat_SR a e He.
  rewrite LeanNum_S (add_nat a e) (add_nat_p a Ha e He).
  rewrite Lean_Nat_sub_eq_2 (LeanNum a) (LeanNum_In a Ha) (LeanNum (add_nat a e)) (LeanNum_In (add_nat a e) (add_nat_p a Ha e He)).
  rewrite IH.
  exact Lean_Nat_pred_eq_1.
Qed.

Theorem LeanNat_sub_trunc : forall a, nat_p a -> forall b, nat_p b -> a c= b ->
  Lean_Nat_sub (LeanNum a) (LeanNum b) = LeanNum 0.
let a. assume Ha: nat_p a. let b. assume Hb: nat_p b. assume Hab: a c= b.
apply NatFactor_Subq_add_ex a Ha b Hb Hab.
let e. assume He: nat_p e /\ b = add_nat a e.
apply He. assume He1: nat_p e. assume He2: b = add_nat a e.
rewrite He2. exact LeanNat_sub_self_add a Ha e He1.
Qed.

(** Lean's Nat.decidableLoHi._proof_1: a property holds from lo up to hi
    exactly when it holds at lo + x for every x below hi - lo. **)
Theorem LeanNat_lo_hi_shift : forall v_lo :e Lean_Nat, forall v_hi :e Lean_Nat, forall v_P :e (Pi_ ux :e Lean_Nat, LeanProp),
  0 :e (Lean_Iff_Prop (Pi_ v_x :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (Lean_Nat_sub v_hi v_lo)), (v_P (Lean_Nat_add v_lo v_x)))) (Pi_ v_x :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop v_lo v_x), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) v_hi), (v_P v_x))))).
let v_lo. assume Hlo: v_lo :e Lean_Nat. let v_hi. assume Hhi: v_hi :e Lean_Nat.
let v_P. assume HP: v_P :e (Pi_ ux :e Lean_Nat, LeanProp).
apply Lean_Nat_num v_lo Hlo. let l. assume Hl0: nat_p l /\ v_lo = LeanNum l.
apply Hl0. assume Hl: nat_p l. assume Hl2: v_lo = LeanNum l.
apply Lean_Nat_num v_hi Hhi. let h. assume Hh0: nat_p h /\ v_hi = LeanNum h.
apply Hh0. assume Hh: nat_p h. assume Hh2: v_hi = LeanNum h.
rewrite Hl2. rewrite Hh2.
claim Lp: (Pi_ v_x :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (Lean_Nat_sub (LeanNum h) (LeanNum l))), (v_P (Lean_Nat_add (LeanNum l) v_x)))) :e LeanProp.
{ exact LeanPi_prop Lean_Nat (fun v_x => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (Lean_Nat_sub (LeanNum h) (LeanNum l))), (v_P (Lean_Nat_add (LeanNum l) v_x))))
    (fun x Hx => LeanPi_prop (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_sub (LeanNum h) (LeanNum l))) (fun _ => (v_P (Lean_Nat_add (LeanNum l) x)))
      (fun w Hw => (ap_Pi Lean_Nat (fun _ => LeanProp) v_P (Lean_Nat_add (LeanNum l) x) HP (Lean_Nat_add_In (LeanNum l) (LeanNum_In l Hl) x Hx)))). }
claim Rp: (Pi_ v_x :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum l) v_x), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (LeanNum h)), (v_P v_x)))) :e LeanProp.
{ exact LeanPi_prop Lean_Nat (fun v_x => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum l) v_x), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (LeanNum h)), (v_P v_x))))
    (fun x Hx => LeanPi_prop (Lean_Nat_le_Prop (LeanNum l) x) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (LeanNum h)), (v_P x)))
      (fun u Hu => LeanPi_prop (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (LeanNum h)) (fun _ => (v_P x))
        (fun w Hw => (ap_Pi Lean_Nat (fun _ => LeanProp) v_P x HP Hx)))). }
apply LeanIff_intro (Pi_ v_x :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (Lean_Nat_sub (LeanNum h) (LeanNum l))), (v_P (Lean_Nat_add (LeanNum l) v_x)))) Lp (Pi_ v_x :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum l) v_x), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (LeanNum h)), (v_P v_x)))) Rp.
- assume HL: 0 :e (Pi_ v_x :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (Lean_Nat_sub (LeanNum h) (LeanNum l))), (v_P (Lean_Nat_add (LeanNum l) v_x)))).
  claim G1: forall x :e Lean_Nat, forall u :e (Lean_Nat_le_Prop (LeanNum l) x), forall w :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (LeanNum h)), 0 :e (v_P x).
  { let x. assume Hx: x :e Lean_Nat.
    apply Lean_Nat_num x Hx. let k. assume Hk: nat_p k /\ x = LeanNum k.
    apply Hk. assume Hk1: nat_p k. assume Hk2: x = LeanNum k.
    rewrite Hk2.
    let u. assume Hu: u :e (Lean_Nat_le_Prop (LeanNum l) (LeanNum k)). let w. assume Hw: w :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum k)) (LeanNum h)).
    claim Llk: l c= k.
    { exact LeanNat_le_Subq l Hl k Hk1 (Lean_prop_0_of (Lean_Nat_le_Prop (LeanNum l) (LeanNum k)) (Lean_Nat_le_Prop_prop (LeanNum l) (LeanNum k)) u Hu). }
    claim Lkh: k :e h.
    { exact LeanNat_lt_In k Hk1 h Hh (Lean_prop_0_of (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum k)) (LeanNum h)) (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node (LeanNum k)) (LeanNum h)) w Hw). }
    apply NatFactor_between_add l Hl h Hh k Hk1 Llk Lkh.
    let j. assume Hj1: nat_p j. let d. assume Hd: nat_p d.
    assume Ekj: k = add_nat l j. assume Ehd: h = add_nat l d. assume Hjd: j :e d.
    claim A0: 0 (LeanNum j) :e (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (Lean_Nat_sub (LeanNum h) (LeanNum l))), (v_P (Lean_Nat_add (LeanNum l) (LeanNum j)))).
    { exact ap_Pi Lean_Nat (fun v_x => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (Lean_Nat_sub (LeanNum h) (LeanNum l))), (v_P (Lean_Nat_add (LeanNum l) v_x)))) 0 (LeanNum j) HL (LeanNum_In j Hj1). }
    claim Hlt: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (Lean_Nat_sub (LeanNum h) (LeanNum l))).
    { rewrite Ehd. rewrite LeanNat_sub_add_num l Hl d Hd. exact LeanNat_In_lt j Hj1 d Hd Hjd. }
    claim A1: 0 (LeanNum j) 0 :e (v_P (Lean_Nat_add (LeanNum l) (LeanNum j))).
    { exact ap_Pi (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (Lean_Nat_sub (LeanNum h) (LeanNum l))) (fun _ => (v_P (Lean_Nat_add (LeanNum l) (LeanNum j)))) (0 (LeanNum j)) 0 A0 Hlt. }
    claim Ex: (Lean_Nat_add (LeanNum l) (LeanNum j)) = LeanNum k.
    { rewrite Ekj. exact LeanNum_add l Hl j Hj1. }
    prove 0 :e (v_P (LeanNum k)).
    rewrite <- Ex.
    exact Lean_prop_0_of (v_P (Lean_Nat_add (LeanNum l) (LeanNum j))) (ap_Pi Lean_Nat (fun _ => LeanProp) v_P (Lean_Nat_add (LeanNum l) (LeanNum j)) HP (Lean_Nat_add_In (LeanNum l) (LeanNum_In l Hl) (LeanNum j) (LeanNum_In j Hj1))) (0 (LeanNum j) 0) A1. }
  exact Pi_0_In Lean_Nat (fun v_x => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum l) v_x), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (LeanNum h)), (v_P v_x))))
    (fun x Hx => Pi_0_In (Lean_Nat_le_Prop (LeanNum l) x) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (LeanNum h)), (v_P x)))
      (fun u Hu => Pi_0_In (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (LeanNum h)) (fun _ => (v_P x))
        (fun w Hw => G1 x Hx u Hu w Hw))).
- assume HR: 0 :e (Pi_ v_x :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum l) v_x), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (LeanNum h)), (v_P v_x)))).
  claim G2: forall x :e Lean_Nat, forall w :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_sub (LeanNum h) (LeanNum l))), 0 :e (v_P (Lean_Nat_add (LeanNum l) x)).
  { let x. assume Hx: x :e Lean_Nat.
    apply Lean_Nat_num x Hx. let j. assume Hj: nat_p j /\ x = LeanNum j.
    apply Hj. assume Hj1: nat_p j. assume Hj2: x = LeanNum j.
    rewrite Hj2.
    let w. assume Hw: w :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (Lean_Nat_sub (LeanNum h) (LeanNum l))).
    apply ordinal_In_Or_Subq h l (nat_p_ordinal h Hh) (nat_p_ordinal l Hl).
    - assume Hhl: h :e l.
      apply FalseE.
      claim S0: (Lean_Nat_sub (LeanNum h) (LeanNum l)) = LeanNum 0.
      { exact LeanNat_sub_trunc h Hh l Hl (nat_trans l Hl h Hhl). }
      claim W0: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum 0)).
      { rewrite <- S0. exact Lean_prop_0_of (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (Lean_Nat_sub (LeanNum h) (LeanNum l))) (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node (LeanNum j)) (Lean_Nat_sub (LeanNum h) (LeanNum l))) w Hw. }
      exact EmptyE j (LeanNat_lt_In j Hj1 0 nat_0 W0).
    - assume Hlh: l c= h.
      apply NatFactor_Subq_add_ex l Hl h Hh Hlh.
      let d. assume Hd: nat_p d /\ h = add_nat l d.
      apply Hd. assume Hd1: nat_p d. assume Hd2: h = add_nat l d.
      claim W1: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum d)).
      { rewrite <- LeanNat_sub_add_num l Hl d Hd1. rewrite <- Hd2.
        exact Lean_prop_0_of (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (Lean_Nat_sub (LeanNum h) (LeanNum l))) (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node (LeanNum j)) (Lean_Nat_sub (LeanNum h) (LeanNum l))) w Hw. }
      claim Jd: j :e d.
      { exact LeanNat_lt_In j Hj1 d Hd1 W1. }
      claim Ex: (Lean_Nat_add (LeanNum l) (LeanNum j)) = (LeanNum (add_nat l j)).
      { exact LeanNum_add l Hl j Hj1. }
      rewrite Ex.
      claim B0: 0 (LeanNum (add_nat l j)) :e (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum l) (LeanNum (add_nat l j))), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum (add_nat l j))) (LeanNum h)), (v_P (LeanNum (add_nat l j))))).
      { exact ap_Pi Lean_Nat (fun v_x => (Pi_ ux :e (Lean_Nat_le_Prop (LeanNum l) v_x), (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (LeanNum h)), (v_P v_x)))) 0 (LeanNum (add_nat l j)) HR (LeanNum_In (add_nat l j) (add_nat_p l Hl j Hj1)). }
      claim B1: 0 (LeanNum (add_nat l j)) 0 :e (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum (add_nat l j))) (LeanNum h)), (v_P (LeanNum (add_nat l j)))).
      { exact ap_Pi (Lean_Nat_le_Prop (LeanNum l) (LeanNum (add_nat l j))) (fun _ => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum (add_nat l j))) (LeanNum h)), (v_P (LeanNum (add_nat l j))))) (0 (LeanNum (add_nat l j))) 0 B0 (Lean_Nat_le_add_num l Hl j Hj1). }
      claim Hlt: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum (add_nat l j))) (LeanNum h)).
      { rewrite Hd2.
        exact LeanNat_In_lt (add_nat l j) (add_nat_p l Hl j Hj1) (add_nat l d) (add_nat_p l Hl d Hd1) (NatFactor_add_In l Hl d Hd1 j Jd). }
      claim B2: 0 (LeanNum (add_nat l j)) 0 0 :e (v_P (LeanNum (add_nat l j))).
      { exact ap_Pi (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum (add_nat l j))) (LeanNum h)) (fun _ => (v_P (LeanNum (add_nat l j)))) (0 (LeanNum (add_nat l j)) 0) 0 B1 Hlt. }
      exact Lean_prop_0_of (v_P (LeanNum (add_nat l j))) (ap_Pi Lean_Nat (fun _ => LeanProp) v_P (LeanNum (add_nat l j)) HP (LeanNum_In (add_nat l j) (add_nat_p l Hl j Hj1))) (0 (LeanNum (add_nat l j)) 0 0) B2. }
  exact Pi_0_In Lean_Nat (fun v_x => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x) (Lean_Nat_sub (LeanNum h) (LeanNum l))), (v_P (Lean_Nat_add (LeanNum l) v_x))))
    (fun x Hx => Pi_0_In (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_sub (LeanNum h) (LeanNum l))) (fun _ => (v_P (Lean_Nat_add (LeanNum l) x)))
      (fun w Hw => G2 x Hx w Hw)).
Qed.

(** Nothing is below zero. **)
Theorem LeanNat_not_lt_zero : forall a :e Lean_Nat, 0 :e (Lean_LT_lt Lean_Nat Lean_instLTNat a (LeanNum 0)) -> False.
let a. assume Ha: a :e Lean_Nat. assume H: 0 :e (Lean_LT_lt Lean_Nat Lean_instLTNat a (LeanNum 0)).
apply Lean_Nat_num a Ha. let j. assume Hj: nat_p j /\ a = LeanNum j.
apply Hj. assume Hj1: nat_p j. assume Hj2: a = LeanNum j.
claim L: 0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum 0).
{ rewrite <- Hj2. rewrite <- LeanNat_lt_le a Ha (LeanNum 0) (LeanNum_In 0 nat_0). exact H. }
exact EmptyE j (LeanNat_lt_In j Hj1 0 nat_0 L).
Qed.
