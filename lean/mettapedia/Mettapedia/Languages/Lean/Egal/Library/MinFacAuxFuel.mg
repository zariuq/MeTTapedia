(** The fuel of Lean's Nat.minFacAux suffices: its source equation.

    Nat.minFacAux n x is read as its fuelled form at fuel n + 3.  A level of
    the fuelled form consults the level below at x + 2, and only where
    the square of x is at most n; there (n + 2) - x drops by two.  That difference is a rank
    for the recursion, so above it the fuel no longer matters
    (Library/RankedRecursion.mg), and the reading satisfies Lean's equation
    for every n and x. **)

Definition LeanMinFacAux_rank : set -> set -> set :=
  fun n x => LeanNat_ord (Lean_Nat_sub (Lean_Nat_add n (LeanNum 2)) x).

(** One level, with r for the level below at x + 2. **)
Definition LeanMinFacAux_step : set -> set -> set -> set := fun n x r =>
  Lean_dite Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) (Lean_Nat_decLt n (Lean_Nat_mul x x))
    (fun v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) => n)
    (fun v_h :e (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)), Lean_False_Prop) =>
      (Lean_dite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) (Lean_Nat_decidable_dvd x n) (fun v_x4 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) => x) (fun v_x4 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))), Lean_False_Prop) => r))).

Theorem LeanMinFacAux_level : forall k, nat_p k -> forall n :e Lean_Nat, forall x :e Lean_Nat,
  Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc k)) n x
    = LeanMinFacAux_step n x (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum k) n (Lean_Nat_add x (LeanNum 2))).
let k. assume Hk: nat_p k. let n. assume Hn: n :e Lean_Nat. let x. assume Hx: x :e Lean_Nat.
rewrite LeanNum_S k Hk.
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel_case0 (LeanNum k) (LeanNum_In k Hk) n Hn x Hx.
Qed.

(** The level below is observed only where the square of x is at most n. **)
Theorem LeanMinFacAux_step_guarded : forall n :e Lean_Nat, forall x :e Lean_Nat, forall r r2,
  (0 /:e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) -> r = r2) ->
  LeanMinFacAux_step n x r = LeanMinFacAux_step n x r2.
let n. assume Hn: n :e Lean_Nat. let x. assume Hx: x :e Lean_Nat. let r r2.
assume Hr: 0 /:e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) -> r = r2.
prove Lean_dite Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) (Lean_Nat_decLt n (Lean_Nat_mul x x))
    (fun v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) => n)
    (fun v_h :e (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)), Lean_False_Prop) => (Lean_dite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) (Lean_Nat_decidable_dvd x n) (fun v_x4 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) => x) (fun v_x4 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))), Lean_False_Prop) => r)))
  = Lean_dite Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) (Lean_Nat_decLt n (Lean_Nat_mul x x))
    (fun v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) => n)
    (fun v_h :e (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)), Lean_False_Prop) => (Lean_dite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) (Lean_Nat_decidable_dvd x n) (fun v_x4 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) => x) (fun v_x4 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))), Lean_False_Prop) => r2))).
apply Lean_dite_guarded Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x))
  (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x))
  (Lean_Nat_decLt n (Lean_Nat_mul x x)) (Lean_Nat_decLt_In n Hn (Lean_Nat_mul x x) (Lean_Nat_mul_In x Hx x Hx))
  (fun h => n) (fun h => (Lean_dite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) (Lean_Nat_decidable_dvd x n) (fun v_x4 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) => x) (fun v_x4 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))), Lean_False_Prop) => r))) (fun h => n) (fun h => (Lean_dite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) (Lean_Nat_decidable_dvd x n) (fun v_x4 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) => x) (fun v_x4 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))), Lean_False_Prop) => r2))).
- assume H: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)). reflexivity.
- assume H: 0 /:e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)).
  prove (Lean_dite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) (Lean_Nat_decidable_dvd x n) (fun v_x4 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) => x) (fun v_x4 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))), Lean_False_Prop) => r)) = (Lean_dite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) (Lean_Nat_decidable_dvd x n) (fun v_x4 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))) => x) (fun v_x4 :e (Pi_ ux :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))), Lean_False_Prop) => r2)).
  rewrite Hr H. reflexivity.
Qed.

(** Where the square of x is at most n, the rank at x + 2 is below the rank at x, and at most n. **)
Theorem LeanMinFacAux_rank_drop : forall n, nat_p n -> forall x, nat_p x ->
  0 /:e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum n)) (Lean_Nat_mul (LeanNum x) (LeanNum x)) ->
  LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)) :e LeanMinFacAux_rank (LeanNum n) (LeanNum x)
  /\ LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)) :e ordsucc n.
let n. assume Hn: nat_p n. let x. assume Hx: nat_p x.
assume H: 0 /:e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum n)) (Lean_Nat_mul (LeanNum x) (LeanNum x)).
claim L1: mul_nat x x :e ordsucc n.
{ apply Lean_Nat_le_num_In (ordsucc n) (nat_ordsucc n Hn) (mul_nat x x) (mul_nat_p x Hx x Hx).
  rewrite LeanNum_S n Hn.
  rewrite <- LeanNum_mul x Hx x Hx.
  exact H. }
claim L2: x c= n.
{ apply Subq_tra x (mul_nat x x) n.
  - apply nat_inv x Hx.
    + assume Hx0: x = 0. rewrite Hx0. exact Subq_Empty (mul_nat 0 0).
    + assume Hex: exists w, nat_p w /\ x = ordsucc w.
      apply Hex. let w. assume Hw: nat_p w /\ x = ordsucc w.
      apply Hw. assume Hw1: nat_p w. assume Hw2: x = ordsucc w.
      claim Lw: mul_nat x (ordsucc w) = mul_nat x x.
      { rewrite <- Hw2. reflexivity. }
      exact NatFactor_Subq_eq x (mul_nat x (ordsucc w)) (mul_nat x x) (NatFactor_mul_Subq x Hx w Hw1) Lw.
  - exact nat_ordsucc_trans n Hn (mul_nat x x) L1. }
apply NatFactor_Subq_add_ex x Hx n Hn L2.
let d. assume Hd: nat_p d /\ n = add_nat x d.
apply Hd. assume Hd1: nat_p d. assume Hd2: n = add_nat x d.
claim Ldx: add_nat d x = n.
{ rewrite add_nat_com d Hd1 x Hx. symmetry. exact Hd2. }
claim Ln2: add_nat n 2 = ordsucc (ordsucc n).
{ prove add_nat n (ordsucc (ordsucc 0)) = ordsucc (ordsucc n).
  rewrite add_nat_SR n (ordsucc 0) nat_1. rewrite add_nat_SR n 0 nat_0. rewrite add_nat_0R n. reflexivity. }
claim LA: add_nat (ordsucc (ordsucc d)) x = add_nat n 2.
{ rewrite add_nat_SL (ordsucc d) (nat_ordsucc d Hd1) x Hx.
  rewrite add_nat_SL d Hd1 x Hx.
  rewrite Ldx. symmetry. exact Ln2. }
claim LB: add_nat d (add_nat x 2) = add_nat n 2.
{ rewrite <- add_nat_asso d Hd1 x Hx 2 nat_2.
  rewrite Ldx. reflexivity. }
claim R1: LeanMinFacAux_rank (LeanNum n) (LeanNum x) = ordsucc (ordsucc d).
{ prove LeanNat_ord (Lean_Nat_sub (Lean_Nat_add (LeanNum n) (LeanNum 2)) (LeanNum x)) = ordsucc (ordsucc d).
  rewrite LeanNum_add n Hn 2 nat_2.
  rewrite LeanNum_sub_eq (ordsucc (ordsucc d)) (nat_ordsucc (ordsucc d) (nat_ordsucc d Hd1)) x Hx (add_nat n 2) LA.
  exact LeanNat_ord_num (ordsucc (ordsucc d)) (nat_ordsucc (ordsucc d) (nat_ordsucc d Hd1)). }
claim R2: LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)) = d.
{ prove LeanNat_ord (Lean_Nat_sub (Lean_Nat_add (LeanNum n) (LeanNum 2)) (Lean_Nat_add (LeanNum x) (LeanNum 2))) = d.
  rewrite LeanNum_add n Hn 2 nat_2.
  rewrite LeanNum_add x Hx 2 nat_2.
  rewrite LeanNum_sub_eq d Hd1 (add_nat x 2) (add_nat_p x Hx 2 nat_2) (add_nat n 2) LB.
  exact LeanNat_ord_num d Hd1. }
apply andI.
- rewrite R2. rewrite R1.
  exact ordsuccI1 (ordsucc d) d (ordsuccI2 d).
- rewrite R2.
  apply nat_Subq_In_ordsucc d Hd1 n Hn.
  prove d c= n.
  rewrite <- Ldx.
  exact NatFactor_add_Subq d x Hx.
Qed.

Theorem LeanMinFacAux_layers : forall n, nat_p n ->
  RankedLayers Lean_Nat (LeanMinFacAux_rank (LeanNum n))
    (fun k x => Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum k) (LeanNum n) x).
let n. assume Hn: nat_p n.
let k. assume Hk: nat_p k. let l. assume Hl: nat_p l. let x. assume Hx: x :e Lean_Nat.
apply Lean_Nat_num x Hx. let j. assume Hj: nat_p j /\ x = LeanNum j.
apply Hj. assume Hj1: nat_p j. assume Hj2: x = LeanNum j.
rewrite Hj2.
assume Hagree: forall y :e Lean_Nat,
  LeanMinFacAux_rank (LeanNum n) y :e LeanMinFacAux_rank (LeanNum n) (LeanNum j) ->
  Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum k) (LeanNum n) y = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum l) (LeanNum n) y.
prove Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc k)) (LeanNum n) (LeanNum j) = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc l)) (LeanNum n) (LeanNum j).
rewrite LeanMinFacAux_level k Hk (LeanNum n) (LeanNum_In n Hn) (LeanNum j) (LeanNum_In j Hj1).
rewrite LeanMinFacAux_level l Hl (LeanNum n) (LeanNum_In n Hn) (LeanNum j) (LeanNum_In j Hj1).
apply LeanMinFacAux_step_guarded (LeanNum n) (LeanNum_In n Hn) (LeanNum j) (LeanNum_In j Hj1)
  (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum k) (LeanNum n) (Lean_Nat_add (LeanNum j) (LeanNum 2)))
  (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum l) (LeanNum n) (Lean_Nat_add (LeanNum j) (LeanNum 2))).
assume Hguard: 0 /:e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum n)) (Lean_Nat_mul (LeanNum j) (LeanNum j)).
apply Hagree (Lean_Nat_add (LeanNum j) (LeanNum 2)) (Lean_Nat_add_In (LeanNum j) (LeanNum_In j Hj1) (LeanNum 2) (LeanNum_In 2 nat_2)).
apply LeanMinFacAux_rank_drop n Hn j Hj1 Hguard.
assume Hdrop: LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum j) (LeanNum 2)) :e LeanMinFacAux_rank (LeanNum n) (LeanNum j).
assume Hbound: LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum j) (LeanNum 2)) :e ordsucc n.
exact Hdrop.
Qed.

(** One level in the plain conditionals of Lean's equation.  A conditional
    whose branches do not consult the proof of the guard and the plain
    conditional are the same recursion on the decision, so the two sides are
    equal by their definitions (Library/DecisionTruth.mg states this for one
    conditional as Lean_dite_plain). **)
Theorem LeanMinFacAux_step_plain : forall n x r,
  LeanMinFacAux_step n x r
    = Lean_ite Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_mul x x)) (Lean_Nat_decLt n (Lean_Nat_mul x x)) n
        (Lean_ite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat n (Lean_Nat_mul x v_c))))
          (Lean_Nat_decidable_dvd x n) x r).
let n x r.
reflexivity.
Qed.

(** Lean's equation Nat.minFacAux.eq_1, for the reading. **)
Theorem LeanMinFacAux_equation : forall v_n :e Lean_Nat, forall v_x :e Lean_Nat, (Lean_Nat_minFacAux v_n v_x) = (Lean_ite Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n) (Lean_Nat_mul v_x v_x)) (Lean_Nat_decLt v_n (Lean_Nat_mul v_x v_x)) v_n (Lean_ite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat v_n (Lean_Nat_mul v_x v_c)))) (Lean_Nat_decidable_dvd v_x v_n) v_x (Lean_Nat_minFacAux v_n (Lean_Nat_add v_x (LeanNum 2))))).
let v_n. assume Hvn: v_n :e Lean_Nat. let v_x. assume Hvx: v_x :e Lean_Nat.
apply Lean_Nat_num v_n Hvn. let n. assume Hn: nat_p n /\ v_n = LeanNum n.
apply Hn. assume Hn1: nat_p n. assume Hn2: v_n = LeanNum n.
apply Lean_Nat_num v_x Hvx. let x. assume Hx: nat_p x /\ v_x = LeanNum x.
apply Hx. assume Hx1: nat_p x. assume Hx2: v_x = LeanNum x.
rewrite Hn2. rewrite Hx2.
claim Lfuel: Lean_Nat_add (LeanNum n) (LeanNum 3) = LeanNum (ordsucc (ordsucc (ordsucc n))).
{ rewrite LeanNum_add n Hn1 3 nat_3.
  prove LeanNum (add_nat n (ordsucc (ordsucc (ordsucc 0)))) = LeanNum (ordsucc (ordsucc (ordsucc n))).
  rewrite add_nat_SR n (ordsucc (ordsucc 0)) nat_2. rewrite add_nat_SR n (ordsucc 0) nat_1.
  rewrite add_nat_SR n 0 nat_0. rewrite add_nat_0R n. reflexivity. }
claim Lread: forall y :e Lean_Nat, Lean_Nat_minFacAux (LeanNum n) y
  = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (ordsucc (ordsucc n)))) (LeanNum n) y.
{ let y. assume Hy: y :e Lean_Nat.
  rewrite <- Lfuel.
  reflexivity. }
claim L1: Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (ordsucc (ordsucc n)))) (LeanNum n) (LeanNum x)
  = LeanMinFacAux_step (LeanNum n) (LeanNum x)
      (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (ordsucc n))) (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2))).
{ exact LeanMinFacAux_level (ordsucc (ordsucc n)) (nat_ordsucc (ordsucc n) (nat_ordsucc n Hn1))
    (LeanNum n) (LeanNum_In n Hn1) (LeanNum x) (LeanNum_In x Hx1). }
claim L2: LeanMinFacAux_step (LeanNum n) (LeanNum x)
      (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (ordsucc n))) (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)))
  = LeanMinFacAux_step (LeanNum n) (LeanNum x)
      (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (ordsucc (ordsucc n)))) (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2))).
{ apply LeanMinFacAux_step_guarded (LeanNum n) (LeanNum_In n Hn1) (LeanNum x) (LeanNum_In x Hx1)
    (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (ordsucc n))) (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)))
    (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (ordsucc (ordsucc n)))) (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2))).
  assume Hguard: 0 /:e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum n)) (Lean_Nat_mul (LeanNum x) (LeanNum x)).
  apply LeanMinFacAux_rank_drop n Hn1 x Hx1 Hguard.
  assume Hdrop: LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)) :e LeanMinFacAux_rank (LeanNum n) (LeanNum x).
  assume Hbound: LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)) :e ordsucc n.
  exact RankedLayers_stable Lean_Nat (LeanMinFacAux_rank (LeanNum n))
    (fun k y => Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum k) (LeanNum n) y) (LeanMinFacAux_layers n Hn1)
    (ordsucc (ordsucc n)) (nat_ordsucc (ordsucc n) (nat_ordsucc n Hn1))
    (ordsucc (ordsucc (ordsucc n))) (nat_ordsucc (ordsucc (ordsucc n)) (nat_ordsucc (ordsucc n) (nat_ordsucc n Hn1)))
    (Lean_Nat_add (LeanNum x) (LeanNum 2)) (Lean_Nat_add_In (LeanNum x) (LeanNum_In x Hx1) (LeanNum 2) (LeanNum_In 2 nat_2))
    (ordsuccI1 (ordsucc n) (LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2))) Hbound)
    (ordsuccI1 (ordsucc (ordsucc n)) (LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)))
      (ordsuccI1 (ordsucc n) (LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2))) Hbound)). }
rewrite Lread (LeanNum x) (LeanNum_In x Hx1).
rewrite Lread (Lean_Nat_add (LeanNum x) (LeanNum 2)) (Lean_Nat_add_In (LeanNum x) (LeanNum_In x Hx1) (LeanNum 2) (LeanNum_In 2 nat_2)).
rewrite L1. rewrite L2.
exact LeanMinFacAux_step_plain (LeanNum n) (LeanNum x)
  (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MinFacAux_sourceFuel (LeanNum (ordsucc (ordsucc (ordsucc n)))) (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2))).
Qed.

(** The least factor is at least two.  By the equation, Nat.minFacAux n x is
    n, or x, or its value at x + 2 where the rank is smaller: for n and x at
    least two, so is the value. **)
Theorem LeanMinFacAux_two_le : forall n, nat_p n -> 2 c= n ->
  forall j, nat_p j -> forall x, nat_p x -> 2 c= x -> LeanMinFacAux_rank (LeanNum n) (LeanNum x) = j ->
  exists m, nat_p m /\ (Lean_Nat_minFacAux (LeanNum n) (LeanNum x) = LeanNum m /\ 2 c= m).
let n. assume Hn: nat_p n. assume Hn2: 2 c= n.
apply nat_complete_ind.
let j. assume Hj: nat_p j.
assume IH: forall i :e j, forall x, nat_p x -> 2 c= x -> LeanMinFacAux_rank (LeanNum n) (LeanNum x) = i ->
  exists m, nat_p m /\ (Lean_Nat_minFacAux (LeanNum n) (LeanNum x) = LeanNum m /\ 2 c= m).
let x. assume Hx: nat_p x. assume Hx2: 2 c= x.
assume Hrank: LeanMinFacAux_rank (LeanNum n) (LeanNum x) = j.
rewrite LeanMinFacAux_equation (LeanNum n) (LeanNum_In n Hn) (LeanNum x) (LeanNum_In x Hx).
apply Lean_ite_truth Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum n)) (Lean_Nat_mul (LeanNum x) (LeanNum x)))
  (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node (LeanNum n)) (Lean_Nat_mul (LeanNum x) (LeanNum x)))
  (Lean_Nat_decLt (LeanNum n) (Lean_Nat_mul (LeanNum x) (LeanNum x)))
  (Lean_Nat_decLt_In (LeanNum n) (LeanNum_In n Hn) (Lean_Nat_mul (LeanNum x) (LeanNum x)) (Lean_Nat_mul_In (LeanNum x) (LeanNum_In x Hx) (LeanNum x) (LeanNum_In x Hx)))
  (LeanNum n)
  (Lean_ite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum x) v_c)))) (Lean_Nat_decidable_dvd (LeanNum x) (LeanNum n)) (LeanNum x) (Lean_Nat_minFacAux (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2))))
  (fun v => exists m, nat_p m /\ (v = LeanNum m /\ 2 c= m)).
- assume H: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum n)) (Lean_Nat_mul (LeanNum x) (LeanNum x))).
  prove exists m, nat_p m /\ (LeanNum n = LeanNum m /\ 2 c= m).
  witness n. apply andI.
  + exact Hn.
  + apply andI.
    * reflexivity.
    * exact Hn2.
- assume Hguard: 0 /:e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum n)) (Lean_Nat_mul (LeanNum x) (LeanNum x))).
  apply Lean_ite_truth Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum x) v_c))))
    (Lean_Exists_Prop_prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum x) v_c))))
    (Lean_Nat_decidable_dvd (LeanNum x) (LeanNum n))
    (Lean_Nat_decidable_dvd_In (LeanNum x) (LeanNum_In x Hx) (LeanNum n) (LeanNum_In n Hn))
    (LeanNum x) (Lean_Nat_minFacAux (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)))
    (fun v => exists m, nat_p m /\ (v = LeanNum m /\ 2 c= m)).
  + assume H: 0 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum x) v_c)))).
    prove exists m, nat_p m /\ (LeanNum x = LeanNum m /\ 2 c= m).
    witness x. apply andI.
    * exact Hx.
    * apply andI.
      { reflexivity. }
      { exact Hx2. }
  + assume H: 0 /:e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum x) v_c)))).
    apply LeanMinFacAux_rank_drop n Hn x Hx Hguard.
    assume Hdrop: LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)) :e LeanMinFacAux_rank (LeanNum n) (LeanNum x).
    assume Hbound: LeanMinFacAux_rank (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)) :e ordsucc n.
    claim Lnext: Lean_Nat_add (LeanNum x) (LeanNum 2) = LeanNum (add_nat x 2).
    { exact LeanNum_add x Hx 2 nat_2. }
    claim Lin: LeanMinFacAux_rank (LeanNum n) (LeanNum (add_nat x 2)) :e j.
    { rewrite <- Lnext. rewrite <- Hrank. exact Hdrop. }
    claim Lrefl: LeanMinFacAux_rank (LeanNum n) (LeanNum (add_nat x 2)) = LeanMinFacAux_rank (LeanNum n) (LeanNum (add_nat x 2)).
    { reflexivity. }
    prove exists m, nat_p m /\ (Lean_Nat_minFacAux (LeanNum n) (Lean_Nat_add (LeanNum x) (LeanNum 2)) = LeanNum m /\ 2 c= m).
    rewrite Lnext.
    exact IH (LeanMinFacAux_rank (LeanNum n) (LeanNum (add_nat x 2))) Lin (add_nat x 2) (add_nat_p x Hx 2 nat_2)
      (Subq_tra 2 x (add_nat x 2) Hx2 (NatFactor_add_Subq x 2 nat_2)) Lrefl.
Qed.

Theorem LeanMinFac_two_le : forall n, nat_p n -> 2 c= n ->
  exists m, nat_p m /\ (Lean_Nat_minFac (LeanNum n) = LeanNum m /\ 2 c= m).
let n. assume Hn: nat_p n. assume Hn2: 2 c= n.
rewrite Lean_Nat_minFac_unfold (LeanNum n).
apply Lean_ite_truth Lean_Nat
  (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum 2) v_c))))
  (Lean_Exists_Prop_prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum 2) v_c))))
  (Lean_Nat_decidable_dvd (LeanNum 2) (LeanNum n))
  (Lean_Nat_decidable_dvd_In (LeanNum 2) (LeanNum_In 2 nat_2) (LeanNum n) (LeanNum_In n Hn))
  (LeanNum 2) (Lean_Nat_minFacAux (LeanNum n) (LeanNum 3))
  (fun v => exists m, nat_p m /\ (v = LeanNum m /\ 2 c= m)).
- assume H: 0 :e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum 2) v_c)))).
  prove exists m, nat_p m /\ (LeanNum 2 = LeanNum m /\ 2 c= m).
  witness 2. apply andI.
  + exact nat_2.
  + apply andI.
    * reflexivity.
    * exact Subq_ref 2.
- assume H: 0 /:e (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat (LeanNum n) (Lean_Nat_mul (LeanNum 2) v_c)))).
  claim Lrefl: LeanMinFacAux_rank (LeanNum n) (LeanNum 3) = LeanMinFacAux_rank (LeanNum n) (LeanNum 3).
  { reflexivity. }
  prove exists m, nat_p m /\ (Lean_Nat_minFacAux (LeanNum n) (LeanNum 3) = LeanNum m /\ 2 c= m).
  exact LeanMinFacAux_two_le n Hn Hn2 (LeanMinFacAux_rank (LeanNum n) (LeanNum 3))
    (LeanNat_ord_nat (Lean_Nat_sub (Lean_Nat_add (LeanNum n) (LeanNum 2)) (LeanNum 3))
      (Lean_Nat_sub_In (Lean_Nat_add (LeanNum n) (LeanNum 2)) (Lean_Nat_add_In (LeanNum n) (LeanNum_In n Hn) (LeanNum 2) (LeanNum_In 2 nat_2)) (LeanNum 3) (LeanNum_In 3 nat_3)))
    3 nat_3 (ordsuccI1 2) Lrefl.
Qed.
