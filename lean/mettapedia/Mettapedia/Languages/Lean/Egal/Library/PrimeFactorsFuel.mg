(** The fuel of Lean's Nat.primeFactorsList suffices: its source equations.

    Nat.primeFactorsList n is read as its fuelled form at fuel n + 1.  At
    n = k + 2 a level consults the level below at n divided by its least
    factor, which is below n because that factor is at least two
    (Library/MinFacAuxFuel.mg).  The state is its own rank
    (Library/RankedRecursion.mg). **)

(** A positive number divided by a number that is at least two is smaller. **)
Theorem LeanNat_div_two_lt : forall b, nat_p b -> forall m, nat_p m -> 2 c= m ->
  exists q, nat_p q /\ (Lean_Nat_div (LeanNum (ordsucc b)) (LeanNum m) = LeanNum q /\ q :e ordsucc b).
let b. assume Hb: nat_p b. let m. assume Hm: nat_p m. assume H2: 2 c= m.
apply nat_inv m Hm.
- assume Hm0: m = 0. apply FalseE.
  exact NatFactor_two_not_Subq_0 (NatFactor_Subq_eq 2 m 0 H2 Hm0).
- assume Hex: exists m1, nat_p m1 /\ m = ordsucc m1.
  apply Hex. let m1. assume Hm1p: nat_p m1 /\ m = ordsucc m1.
  apply Hm1p. assume Hm1: nat_p m1. assume Em: m = ordsucc m1.
  apply nat_inv m1 Hm1.
  + assume Hm10: m1 = 0. apply FalseE.
    claim Lm: m = 1.
    { rewrite Em. rewrite Hm10. reflexivity. }
    exact NatFactor_two_not_Subq_1 (NatFactor_Subq_eq 2 m 1 H2 Lm).
  + assume Hex2: exists m2, nat_p m2 /\ m1 = ordsucc m2.
    apply Hex2. let m2. assume Hm2p: nat_p m2 /\ m1 = ordsucc m2.
    apply Hm2p. assume Hm2: nat_p m2. assume Em1: m1 = ordsucc m2.
    apply nat_euclid m1 Hm1 (ordsucc b) (nat_ordsucc b Hb).
    let q. assume Hq: nat_p q /\ (exists r, nat_p r /\ (r :e ordsucc m1 /\ ordsucc b = add_nat (mul_nat q (ordsucc m1)) r)).
    apply Hq. assume Hq1: nat_p q.
    assume Hq2: exists r, nat_p r /\ (r :e ordsucc m1 /\ ordsucc b = add_nat (mul_nat q (ordsucc m1)) r).
    apply Hq2. let r. assume Hr: nat_p r /\ (r :e ordsucc m1 /\ ordsucc b = add_nat (mul_nat q (ordsucc m1)) r).
    apply Hr. assume Hr1: nat_p r. assume Hr2: r :e ordsucc m1 /\ ordsucc b = add_nat (mul_nat q (ordsucc m1)) r.
    apply Hr2. assume Hr3: r :e ordsucc m1. assume Hr4: ordsucc b = add_nat (mul_nat q (ordsucc m1)) r.
    witness q. apply andI.
    * exact Hq1.
    * apply andI.
      { rewrite Em. rewrite Hr4. exact Lean_Nat_div_num m1 Hm1 r Hr1 Hr3 q Hq1. }
      { prove q :e ordsucc b.
        apply nat_inv q Hq1.
        - assume Hq0: q = 0. rewrite Hq0. exact nat_0_in_ordsucc b Hb.
        - assume Hexw: exists w, nat_p w /\ q = ordsucc w.
          apply Hexw. let w. assume Hw: nat_p w /\ q = ordsucc w.
          apply Hw. assume Hw1: nat_p w. assume Ew: q = ordsucc w.
          claim L0: 0 :e q.
          { rewrite Ew. exact nat_0_in_ordsucc w Hw1. }
          claim Lqm: nat_p (mul_nat q m2).
          { exact mul_nat_p q Hq1 m2 Hm2. }
          claim L1: 0 :e add_nat q (mul_nat q m2).
          { exact NatFactor_add_Subq q (mul_nat q m2) Lqm 0 L0. }
          claim L2: add_nat q 0 :e add_nat q (add_nat q (mul_nat q m2)).
          { exact NatFactor_add_In q Hq1 (add_nat q (mul_nat q m2)) (add_nat_p q Hq1 (mul_nat q m2) Lqm) 0 L1. }
          claim Lgen: forall z, z = q -> z :e add_nat q (add_nat q (mul_nat q m2)) -> q :e add_nat q (add_nat q (mul_nat q m2)).
          { let z. assume Ez: z = q. rewrite Ez.
            assume Hz: q :e add_nat q (add_nat q (mul_nat q m2)). exact Hz. }
          claim L3: mul_nat q (ordsucc m1) = add_nat q (add_nat q (mul_nat q m2)).
          { rewrite mul_nat_SR q m1 Hm1. rewrite Em1. rewrite mul_nat_SR q m2 Hm2. reflexivity. }
          claim L4: q :e mul_nat q (ordsucc m1).
          { rewrite L3. exact Lgen (add_nat q 0) (add_nat_0R q) L2. }
          claim L5: mul_nat q (ordsucc m1) c= ordsucc b.
          { rewrite Hr4. exact NatFactor_add_Subq (mul_nat q (ordsucc m1)) r Hr1. }
          exact L5 q L4. }
Qed.

(** The state that the level at t + 2 consults. **)
Theorem LeanPrimeFactors_next : forall t, nat_p t ->
  exists q, nat_p q /\ (Lean_Nat_div (Lean_Nat_add (LeanNum t) (LeanNum 2)) (Lean_Nat_minFac (Lean_Nat_add (LeanNum t) (LeanNum 2))) = LeanNum q /\ q :e ordsucc (ordsucc t)).
let t. assume Ht: nat_p t.
claim Ladd: Lean_Nat_add (LeanNum t) (LeanNum 2) = LeanNum (ordsucc (ordsucc t)).
{ rewrite LeanNum_add t Ht 2 nat_2.
  prove LeanNum (add_nat t (ordsucc (ordsucc 0))) = LeanNum (ordsucc (ordsucc t)).
  rewrite add_nat_SR t (ordsucc 0) nat_1. rewrite add_nat_SR t 0 nat_0. rewrite add_nat_0R t. reflexivity. }
rewrite Ladd.
claim L2: 2 c= ordsucc (ordsucc t).
{ exact NatFactor_two_Subq (ordsucc (ordsucc t)) (nat_ordsucc (ordsucc t) (nat_ordsucc t Ht))
    (neq_ordsucc_0 (ordsucc t))
    (fun H: ordsucc (ordsucc t) = 1 => neq_ordsucc_0 t (ordsucc_inj (ordsucc t) 0 H)). }
apply LeanMinFac_two_le (ordsucc (ordsucc t)) (nat_ordsucc (ordsucc t) (nat_ordsucc t Ht)) L2.
let m. assume Hm: nat_p m /\ (Lean_Nat_minFac (LeanNum (ordsucc (ordsucc t))) = LeanNum m /\ 2 c= m).
apply Hm. assume Hm1: nat_p m.
assume Hm2: Lean_Nat_minFac (LeanNum (ordsucc (ordsucc t))) = LeanNum m /\ 2 c= m.
apply Hm2. assume Hm3: Lean_Nat_minFac (LeanNum (ordsucc (ordsucc t))) = LeanNum m. assume Hm4: 2 c= m.
rewrite Hm3.
exact LeanNat_div_two_lt (ordsucc t) (nat_ordsucc t Ht) m Hm1 Hm4.
Qed.

Theorem LeanPrimeFactors_layers : RankedLayers Lean_Nat LeanNat_ord
  (fun k s => Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (LeanNum k) s).
let k. assume Hk: nat_p k. let l. assume Hl: nat_p l. let x. assume Hx: x :e Lean_Nat.
apply Lean_Nat_num x Hx. let s. assume Hs: nat_p s /\ x = LeanNum s.
apply Hs. assume Hs1: nat_p s. assume Hs2: x = LeanNum s.
rewrite Hs2.
assume Hagree: forall y :e Lean_Nat, LeanNat_ord y :e LeanNat_ord (LeanNum s) ->
  Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (LeanNum k) y = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (LeanNum l) y.
prove Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (LeanNum (ordsucc k)) (LeanNum s) = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (LeanNum (ordsucc l)) (LeanNum s).
rewrite LeanNum_S k Hk. rewrite LeanNum_S l Hl.
apply nat_inv s Hs1.
- assume Es: s = 0. rewrite Es.
  rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case0 (LeanNum k) (LeanNum_In k Hk).
  rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case0 (LeanNum l) (LeanNum_In l Hl).
  reflexivity.
- assume Hex: exists s1, nat_p s1 /\ s = ordsucc s1.
  apply Hex. let s1. assume Hs1p: nat_p s1 /\ s = ordsucc s1.
  apply Hs1p. assume Hs11: nat_p s1. assume Es: s = ordsucc s1.
  apply nat_inv s1 Hs11.
  + assume Es1: s1 = 0. rewrite Es. rewrite Es1.
    rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case1 (LeanNum k) (LeanNum_In k Hk).
    rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case1 (LeanNum l) (LeanNum_In l Hl).
    reflexivity.
  + assume Hex2: exists t, nat_p t /\ s1 = ordsucc t.
    apply Hex2. let t. assume Htp: nat_p t /\ s1 = ordsucc t.
    apply Htp. assume Ht: nat_p t. assume Et: s1 = ordsucc t.
    apply LeanPrimeFactors_next t Ht.
    let q. assume Hq: nat_p q /\ (Lean_Nat_div (Lean_Nat_add (LeanNum t) (LeanNum 2)) (Lean_Nat_minFac (Lean_Nat_add (LeanNum t) (LeanNum 2))) = LeanNum q /\ q :e ordsucc (ordsucc t)).
    apply Hq. assume Hq1: nat_p q.
    assume Hq2: Lean_Nat_div (Lean_Nat_add (LeanNum t) (LeanNum 2)) (Lean_Nat_minFac (Lean_Nat_add (LeanNum t) (LeanNum 2))) = LeanNum q /\ q :e ordsucc (ordsucc t).
    apply Hq2. assume Hq3: Lean_Nat_div (Lean_Nat_add (LeanNum t) (LeanNum 2)) (Lean_Nat_minFac (Lean_Nat_add (LeanNum t) (LeanNum 2))) = LeanNum q. assume Hq4: q :e ordsucc (ordsucc t).
    claim Lrank: LeanNat_ord (LeanNum q) :e LeanNat_ord (LeanNum s).
    { rewrite LeanNat_ord_num q Hq1. rewrite LeanNat_ord_num s Hs1. rewrite Es. rewrite Et. exact Hq4. }
    rewrite Es. rewrite Et.
    rewrite LeanNum_S (ordsucc t) (nat_ordsucc t Ht). rewrite LeanNum_S t Ht.
    rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case2 (LeanNum k) (LeanNum_In k Hk) (LeanNum t) (LeanNum_In t Ht).
    rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case2 (LeanNum l) (LeanNum_In l Hl) (LeanNum t) (LeanNum_In t Ht).
    rewrite Hq3.
    rewrite Hagree (LeanNum q) (LeanNum_In q Hq1) Lrank.
    reflexivity.
Qed.

(** Lean's equations Nat.primeFactorsList.eq_1, eq_2 and eq_3, for the reading. **)
Theorem LeanPrimeFactors_equation_1 : (Lean_Nat_primeFactorsList (LeanNum 0)) = (Lean_List_nil_node Lean_Nat).
prove Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (Lean_Nat_succ_node (LeanNum 0)) (LeanNum 0) = Lean_List_nil_node Lean_Nat.
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case0 (LeanNum 0) (LeanNum_In 0 nat_0).
Qed.

Theorem LeanPrimeFactors_equation_2 : (Lean_Nat_primeFactorsList (LeanNum 1)) = (Lean_List_nil_node Lean_Nat).
prove Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (Lean_Nat_succ_node (LeanNum 1)) (LeanNum 1) = Lean_List_nil_node Lean_Nat.
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case1 (LeanNum 1) (LeanNum_In 1 nat_1).
Qed.

Theorem LeanPrimeFactors_equation_3 : forall v_k :e Lean_Nat, (Lean_Nat_primeFactorsList (Lean_Nat_succ_node (Lean_Nat_succ_node v_k))) = (Lean_List_cons_node Lean_Nat (Lean_Nat_minFac (Lean_Nat_add v_k (LeanNum 2))) (Lean_Nat_primeFactorsList (Lean_Nat_div (Lean_Nat_add v_k (LeanNum 2)) (Lean_Nat_minFac (Lean_Nat_add v_k (LeanNum 2)))))).
let v_k. assume Hvk: v_k :e Lean_Nat.
apply Lean_Nat_num v_k Hvk. let t. assume Htp: nat_p t /\ v_k = LeanNum t.
apply Htp. assume Ht: nat_p t. assume Et: v_k = LeanNum t.
rewrite Et.
apply LeanPrimeFactors_next t Ht.
let q. assume Hq: nat_p q /\ (Lean_Nat_div (Lean_Nat_add (LeanNum t) (LeanNum 2)) (Lean_Nat_minFac (Lean_Nat_add (LeanNum t) (LeanNum 2))) = LeanNum q /\ q :e ordsucc (ordsucc t)).
apply Hq. assume Hq1: nat_p q.
assume Hq2: Lean_Nat_div (Lean_Nat_add (LeanNum t) (LeanNum 2)) (Lean_Nat_minFac (Lean_Nat_add (LeanNum t) (LeanNum 2))) = LeanNum q /\ q :e ordsucc (ordsucc t).
apply Hq2. assume Hq3: Lean_Nat_div (Lean_Nat_add (LeanNum t) (LeanNum 2)) (Lean_Nat_minFac (Lean_Nat_add (LeanNum t) (LeanNum 2))) = LeanNum q. assume Hq4: q :e ordsucc (ordsucc t).
rewrite Hq3.
prove Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (Lean_Nat_succ_node (Lean_Nat_succ_node (Lean_Nat_succ_node (LeanNum t)))) (Lean_Nat_succ_node (Lean_Nat_succ_node (LeanNum t)))
  = Lean_List_cons_node Lean_Nat (Lean_Nat_minFac (Lean_Nat_add (LeanNum t) (LeanNum 2)))
      (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (Lean_Nat_succ_node (LeanNum q)) (LeanNum q)).
rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel_case2 (Lean_Nat_succ_node (Lean_Nat_succ_node (LeanNum t)))
  (Lean_Nat_succ_typed (Lean_Nat_succ_node (LeanNum t)) (Lean_Nat_succ_typed (LeanNum t) (LeanNum_In t Ht)))
  (LeanNum t) (LeanNum_In t Ht).
rewrite Hq3.
rewrite <- LeanNum_S t Ht.
rewrite <- LeanNum_S (ordsucc t) (nat_ordsucc t Ht).
rewrite <- LeanNum_S q Hq1.
claim Lr1: LeanNat_ord (LeanNum q) :e ordsucc (ordsucc t).
{ rewrite LeanNat_ord_num q Hq1. exact Hq4. }
claim Lr2: LeanNat_ord (LeanNum q) :e ordsucc q.
{ rewrite LeanNat_ord_num q Hq1. exact ordsuccI2 q. }
claim Lstable: Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (LeanNum (ordsucc (ordsucc t))) (LeanNum q) = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (LeanNum (ordsucc q)) (LeanNum q).
{ exact RankedLayers_stable Lean_Nat LeanNat_ord (fun k s => Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_PrimeFactorsList_sourceFuel (LeanNum k) s) LeanPrimeFactors_layers
    (ordsucc (ordsucc t)) (nat_ordsucc (ordsucc t) (nat_ordsucc t Ht)) (ordsucc q) (nat_ordsucc q Hq1)
    (LeanNum q) (LeanNum_In q Hq1) Lr1 Lr2. }
rewrite Lstable.
reflexivity.
Qed.
