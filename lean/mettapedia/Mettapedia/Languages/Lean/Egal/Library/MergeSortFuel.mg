(** The fuel of Lean's List.mergeSort suffices: its source equations.

    List.mergeSort l le is read as its fuelled form at fuel length l + 1.  On
    a list of at least two elements a level consults the level below at the
    two halves that splitInTwo returns.  The type of splitInTwo states their
    lengths, and both are below the length of the list: the length is the
    rank (Library/RankedRecursion.mg). **)

Definition LeanMergeSort_split : set -> set -> set := fun A l =>
  Lean_List_MergeSort_Internal_splitInTwo A (Lean_List_length A l)
    (Lean_Subtype_mk_node (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_List_length A l)) l 0).

Definition LeanMergeSort_half1 : set -> set -> set := fun A l =>
  Lean_Subtype_val (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))
    (Lean_Prod_fst (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l)).

Definition LeanMergeSort_half2 : set -> set -> set := fun A l =>
  Lean_Subtype_val (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))
    (Lean_Prod_snd (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l)).

Theorem LeanMergeSort_split_In : forall A, forall l :e (Lean_List A),
  LeanMergeSort_split A l :e Lean_Prod (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))).
let A l. assume Hl: l :e (Lean_List A).
claim Lrefl: Lean_List_length A l = Lean_List_length A l.
{ reflexivity. }
claim L0: 0 :e Lean_ProofField ((fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_List_length A l)) l).
{ apply Lean_ProofField_intro ((fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_List_length A l)) l).
  rewrite beta (Lean_List A) (fun v_l => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_List_length A l)) l Hl.
  exact Lean_Eq_proof_of Lean_Nat (Lean_List_length A l) (Lean_List_length A l) Lrefl. }
exact Lean_List_MergeSort_Internal_splitInTwo_In A (Lean_List_length A l) (Lean_List_length_In A l Hl)
  (Lean_Subtype_mk_node (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_List_length A l)) l 0)
  (Lean_Subtype_mk_typed (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_List_length A l)) l Hl 0 L0).
Qed.

Theorem LeanMergeSort_half1_In : forall A, forall l :e (Lean_List A), LeanMergeSort_half1 A l :e (Lean_List A).
let A l. assume Hl: l :e (Lean_List A).
exact Lean_Subtype_val_In (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))
  (Lean_Prod_fst (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l))
  (Lean_Prod_fst_In (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l) (LeanMergeSort_split_In A l Hl)).
Qed.

Theorem LeanMergeSort_half2_In : forall A, forall l :e (Lean_List A), LeanMergeSort_half2 A l :e (Lean_List A).
let A l. assume Hl: l :e (Lean_List A).
exact Lean_Subtype_val_In (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))
  (Lean_Prod_snd (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l))
  (Lean_Prod_snd_In (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l) (LeanMergeSort_split_In A l Hl)).
Qed.

(** The lengths of the halves, from the type of splitInTwo. **)
Theorem LeanMergeSort_half1_length : forall A, forall l :e (Lean_List A),
  Lean_List_length A (LeanMergeSort_half1 A l) = Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2).
let A l. assume Hl: l :e (Lean_List A).
exact LeanSubtype_length_val A (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2))
  (Lean_Prod_fst (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l))
  (Lean_Prod_fst_In (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l) (LeanMergeSort_split_In A l Hl)).
Qed.

Theorem LeanMergeSort_half2_length : forall A, forall l :e (Lean_List A),
  Lean_List_length A (LeanMergeSort_half2 A l) = Lean_Nat_div (Lean_List_length A l) (LeanNum 2).
let A l. assume Hl: l :e (Lean_List A).
exact LeanSubtype_length_val A (Lean_Nat_div (Lean_List_length A l) (LeanNum 2))
  (Lean_Prod_snd (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l))
  (Lean_Prod_snd_In (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length A l) (LeanNum 1)) (LeanNum 2)))) (Lean_Subtype (Lean_List A) (fun v_l :e (Lean_List A) => Lean_Eq_Prop Lean_Nat (Lean_List_length A v_l) (Lean_Nat_div (Lean_List_length A l) (LeanNum 2)))) (LeanMergeSort_split A l) (LeanMergeSort_split_In A l Hl)).
Qed.

(** Each half of a list of at least two elements is shorter than the list. **)
Theorem LeanMergeSort_halves_below : forall A, forall a :e A, forall b :e A, forall xs :e (Lean_List A),
  LeanNat_ord (Lean_List_length A (LeanMergeSort_half1 A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)))) :e LeanNat_ord (Lean_List_length A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)))
  /\ LeanNat_ord (Lean_List_length A (LeanMergeSort_half2 A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)))) :e LeanNat_ord (Lean_List_length A (Lean_List_cons_node A a (Lean_List_cons_node A b xs))).
let A a. assume Ha: a :e A. let b. assume Hb: b :e A. let xs. assume Hxs: xs :e (Lean_List A).
claim Hl: (Lean_List_cons_node A a (Lean_List_cons_node A b xs)) :e (Lean_List A).
{ exact Lean_List_cons_typed A a Ha (Lean_List_cons_node A b xs) (Lean_List_cons_typed A b Hb xs Hxs). }
apply Lean_Nat_num (Lean_List_length A xs) (Lean_List_length_In A xs Hxs).
let j. assume Hj: nat_p j /\ Lean_List_length A xs = LeanNum j.
apply Hj. assume Hj1: nat_p j. assume Hj2: Lean_List_length A xs = LeanNum j.
claim Hn: nat_p (ordsucc (ordsucc j)).
{ exact nat_ordsucc (ordsucc j) (nat_ordsucc j Hj1). }
claim Ll: Lean_List_length A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)) = LeanNum (ordsucc (ordsucc j)).
{ exact LeanListLength_cons_num A a Ha (Lean_List_cons_node A b xs) (Lean_List_cons_typed A b Hb xs Hxs)
    (ordsucc j) (nat_ordsucc j Hj1) (LeanListLength_cons_num A b Hb xs Hxs j Hj1 Hj2). }
rewrite LeanMergeSort_half1_length A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)) Hl.
rewrite LeanMergeSort_half2_length A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)) Hl.
rewrite Ll.
apply LeanNat_halves (ordsucc (ordsucc j)) Hn.
let p. assume Hp: nat_p p /\ (exists q, nat_p q /\ (ordsucc (ordsucc j) = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum (ordsucc (ordsucc j))) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum (ordsucc (ordsucc j))) (LeanNum 2) = LeanNum q)))).
apply Hp. assume Hp1: nat_p p.
assume Hp2: exists q, nat_p q /\ (ordsucc (ordsucc j) = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum (ordsucc (ordsucc j))) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum (ordsucc (ordsucc j))) (LeanNum 2) = LeanNum q))).
apply Hp2. let q. assume Hq: nat_p q /\ (ordsucc (ordsucc j) = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum (ordsucc (ordsucc j))) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum (ordsucc (ordsucc j))) (LeanNum 2) = LeanNum q))).
apply Hq. assume Hq1: nat_p q.
assume Hq2: ordsucc (ordsucc j) = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum (ordsucc (ordsucc j))) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum (ordsucc (ordsucc j))) (LeanNum 2) = LeanNum q)).
apply Hq2. assume Hq3: ordsucc (ordsucc j) = add_nat p q.
assume Hq3b: (q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum (ordsucc (ordsucc j))) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum (ordsucc (ordsucc j))) (LeanNum 2) = LeanNum q).
apply Hq3b. assume Hq3c: q c= p /\ p c= ordsucc q.
assume Hq4: Lean_Nat_div (Lean_Nat_add (LeanNum (ordsucc (ordsucc j))) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum (ordsucc (ordsucc j))) (LeanNum 2) = LeanNum q.
apply Hq3c. assume Hqp: q c= p. assume Hpq: p c= ordsucc q.
apply Hq4. assume Hq5: Lean_Nat_div (Lean_Nat_add (LeanNum (ordsucc (ordsucc j))) (LeanNum 1)) (LeanNum 2) = LeanNum p. assume Hq6: Lean_Nat_div (LeanNum (ordsucc (ordsucc j))) (LeanNum 2) = LeanNum q.
rewrite Hq5. rewrite Hq6.
rewrite LeanNat_ord_num p Hp1. rewrite LeanNat_ord_num q Hq1.
rewrite LeanNat_ord_num (ordsucc (ordsucc j)) Hn.
claim Lp0: 0 :e p.
{ apply nat_inv p Hp1.
  - assume Ep: p = 0.
    apply FalseE.
    claim Eq0: q = 0.
    { apply Empty_Subq_eq. rewrite <- Ep. exact Hqp. }
    apply neq_ordsucc_0 (ordsucc j).
    prove ordsucc (ordsucc j) = 0.
    rewrite Hq3. rewrite Ep. rewrite Eq0. exact add_nat_0R 0.
  - assume Hex: exists w, nat_p w /\ p = ordsucc w.
    apply Hex. let w. assume Hw: nat_p w /\ p = ordsucc w.
    apply Hw. assume Hw1: nat_p w. assume Ew: p = ordsucc w.
    rewrite Ew. exact nat_0_in_ordsucc w Hw1. }
claim Lq0: 0 :e q.
{ apply nat_inv q Hq1.
  - assume Eq0: q = 0.
    apply FalseE.
    claim Lp1: p c= ordsucc 0.
    { rewrite <- Eq0. exact Hpq. }
    claim Lnp: ordsucc (ordsucc j) = p.
    { rewrite Hq3. rewrite Eq0. exact add_nat_0R p. }
    claim Lj: ordsucc j :e ordsucc 0.
    { apply Lp1. rewrite <- Lnp. exact ordsuccI2 (ordsucc j). }
    apply ordsuccE 0 (ordsucc j) Lj.
    + assume H: ordsucc j :e 0. exact EmptyE (ordsucc j) H.
    + assume H: ordsucc j = 0. exact neq_ordsucc_0 j H.
  - assume Hex: exists w, nat_p w /\ q = ordsucc w.
    apply Hex. let w. assume Hw: nat_p w /\ q = ordsucc w.
    apply Hw. assume Hw1: nat_p w. assume Ew: q = ordsucc w.
    rewrite Ew. exact nat_0_in_ordsucc w Hw1. }
apply andI.
- prove p :e ordsucc (ordsucc j).
  rewrite Hq3. exact nat_In_add_pos p Hp1 q Hq1 Lq0.
- prove q :e ordsucc (ordsucc j).
  rewrite Hq3. rewrite add_nat_com p Hp1 q Hq1. exact nat_In_add_pos q Hq1 p Hp1 Lp0.
Qed.

(** A list is empty, or has one element, or at least two. **)
Theorem LeanList_cases2 : forall A, forall Q : set -> prop,
  Q (Lean_List_nil_node A) ->
  (forall a :e A, Q (Lean_List_cons_node A a (Lean_List_nil_node A))) ->
  (forall a :e A, forall b :e A, forall xs :e (Lean_List A), Q (Lean_List_cons_node A a (Lean_List_cons_node A b xs))) ->
  forall l :e (Lean_List A), Q l.
let A Q. assume H0: Q (Lean_List_nil_node A).
assume H1: forall a :e A, Q (Lean_List_cons_node A a (Lean_List_nil_node A)).
assume H2: forall a :e A, forall b :e A, forall xs :e (Lean_List A), Q (Lean_List_cons_node A a (Lean_List_cons_node A b xs)).
apply Lean_List_ind A Q.
- exact H0.
- let a. assume Ha: a :e A. let t. assume Ht: t :e (Lean_List A). assume IH: Q t.
  claim Lcons: forall b :e A, forall xs :e (Lean_List A),
    Q (Lean_List_cons_node A a xs) -> Q (Lean_List_cons_node A a (Lean_List_cons_node A b xs)).
  { let b. assume Hb: b :e A. let xs. assume Hxs: xs :e (Lean_List A).
    assume IH2: Q (Lean_List_cons_node A a xs).
    exact H2 a Ha b Hb xs Hxs. }
  exact Lean_List_ind A (fun t2 => Q (Lean_List_cons_node A a t2)) (H1 a Ha) Lcons t Ht.
Qed.

(** One level on a list of at least two elements. **)
Theorem LeanMergeSort_level_at : forall f :e Lean_Nat, forall u, nat_p u -> forall A :e LeanUniv u,
  forall le :e (Pi_ ux :e A, (Pi_ ux :e A, Lean_Bool)), forall a :e A, forall b :e A, forall xs :e (Lean_List A),
  Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node f) A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)) le
    = Lean_List_merge A (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel f A (LeanMergeSort_half1 A (Lean_List_cons_node A a (Lean_List_cons_node A b xs))) le)
        (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel f A (LeanMergeSort_half2 A (Lean_List_cons_node A a (Lean_List_cons_node A b xs))) le) le.
let f. assume Hf: f :e Lean_Nat. let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u.
let le. assume Hle: le :e (Pi_ ux :e A, (Pi_ ux :e A, Lean_Bool)). let a. assume Ha: a :e A. let b. assume Hb: b :e A.
let xs. assume Hxs: xs :e (Lean_List A).
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel_case2 f Hf u Hu A HA le Hle a Ha b Hb xs Hxs.
Qed.

Theorem LeanMergeSort_layers : forall u, nat_p u -> forall A :e LeanUniv u, forall le :e (Pi_ ux :e A, (Pi_ ux :e A, Lean_Bool)),
  RankedLayers (Lean_List A) (fun x => LeanNat_ord (Lean_List_length A x))
    (fun k x => Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum k) A x le).
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u. let le. assume Hle: le :e (Pi_ ux :e A, (Pi_ ux :e A, Lean_Bool)).
let k. assume Hk: nat_p k. let m. assume Hm: nat_p m.
prove forall x :e (Lean_List A),
  (forall y :e (Lean_List A), LeanNat_ord (Lean_List_length A y) :e LeanNat_ord (Lean_List_length A x) ->
    Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum k) A y le = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum m) A y le) ->
  Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum (ordsucc k)) A x le = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum (ordsucc m)) A x le.
rewrite LeanNum_S k Hk. rewrite LeanNum_S m Hm.
apply LeanList_cases2 A (fun x =>
  (forall y :e (Lean_List A), LeanNat_ord (Lean_List_length A y) :e LeanNat_ord (Lean_List_length A x) ->
    Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum k) A y le = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum m) A y le) ->
  Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node (LeanNum k)) A x le = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node (LeanNum m)) A x le).
- assume Hagree: forall y :e (Lean_List A), LeanNat_ord (Lean_List_length A y) :e LeanNat_ord (Lean_List_length A (Lean_List_nil_node A)) ->
    Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum k) A y le = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum m) A y le.
  rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel_case0 (LeanNum k) (LeanNum_In k Hk) u Hu A HA le Hle.
  rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel_case0 (LeanNum m) (LeanNum_In m Hm) u Hu A HA le Hle.
  reflexivity.
- let a. assume Ha: a :e A.
  assume Hagree: forall y :e (Lean_List A), LeanNat_ord (Lean_List_length A y) :e LeanNat_ord (Lean_List_length A (Lean_List_cons_node A a (Lean_List_nil_node A))) ->
    Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum k) A y le = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum m) A y le.
  rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel_case1 (LeanNum k) (LeanNum_In k Hk) u Hu A HA le Hle a Ha.
  rewrite Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel_case1 (LeanNum m) (LeanNum_In m Hm) u Hu A HA le Hle a Ha.
  reflexivity.
- let a. assume Ha: a :e A. let b. assume Hb: b :e A. let xs. assume Hxs: xs :e (Lean_List A).
  assume Hagree: forall y :e (Lean_List A), LeanNat_ord (Lean_List_length A y) :e LeanNat_ord (Lean_List_length A (Lean_List_cons_node A a (Lean_List_cons_node A b xs))) ->
    Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum k) A y le = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum m) A y le.
  claim Hl: (Lean_List_cons_node A a (Lean_List_cons_node A b xs)) :e (Lean_List A).
  { exact Lean_List_cons_typed A a Ha (Lean_List_cons_node A b xs) (Lean_List_cons_typed A b Hb xs Hxs). }
  rewrite LeanMergeSort_level_at (LeanNum k) (LeanNum_In k Hk) u Hu A HA le Hle a Ha b Hb xs Hxs.
  rewrite LeanMergeSort_level_at (LeanNum m) (LeanNum_In m Hm) u Hu A HA le Hle a Ha b Hb xs Hxs.
  apply LeanMergeSort_halves_below A a Ha b Hb xs Hxs.
  assume Hb1: LeanNat_ord (Lean_List_length A (LeanMergeSort_half1 A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)))) :e LeanNat_ord (Lean_List_length A (Lean_List_cons_node A a (Lean_List_cons_node A b xs))).
  assume Hb2: LeanNat_ord (Lean_List_length A (LeanMergeSort_half2 A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)))) :e LeanNat_ord (Lean_List_length A (Lean_List_cons_node A a (Lean_List_cons_node A b xs))).
  rewrite Hagree (LeanMergeSort_half1 A (Lean_List_cons_node A a (Lean_List_cons_node A b xs))) (LeanMergeSort_half1_In A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)) Hl) Hb1.
  rewrite Hagree (LeanMergeSort_half2 A (Lean_List_cons_node A a (Lean_List_cons_node A b xs))) (LeanMergeSort_half2_In A (Lean_List_cons_node A a (Lean_List_cons_node A b xs)) Hl) Hb2.
  reflexivity.
Qed.

(** Above the length of a list, the fuel at fuel length + 1. **)
Theorem LeanMergeSort_at_length : forall u, nat_p u -> forall A :e LeanUniv u, forall le :e (Pi_ ux :e A, (Pi_ ux :e A, Lean_Bool)),
  forall f :e Lean_Nat, forall h :e (Lean_List A),
  LeanNat_ord (Lean_List_length A h) :e LeanNat_ord f ->
  Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel f A h le = Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node (Lean_List_length A h)) A h le.
let u. assume Hu: nat_p u. let A. assume HA: A :e LeanUniv u. let le. assume Hle: le :e (Pi_ ux :e A, (Pi_ ux :e A, Lean_Bool)).
let f. assume Hf: f :e Lean_Nat. let h. assume Hh: h :e (Lean_List A).
assume Hbelow: LeanNat_ord (Lean_List_length A h) :e LeanNat_ord f.
claim Hlen: Lean_List_length A h :e Lean_Nat.
{ exact Lean_List_length_In A h Hh. }
claim Ef: f = LeanNum (LeanNat_ord f).
{ exact LeanNat_ord_eq f Hf. }
claim Eh: Lean_Nat_succ_node (Lean_List_length A h) = LeanNum (ordsucc (LeanNat_ord (Lean_List_length A h))).
{ rewrite LeanNum_S (LeanNat_ord (Lean_List_length A h)) (LeanNat_ord_nat (Lean_List_length A h) Hlen).
  rewrite <- LeanNat_ord_eq (Lean_List_length A h) Hlen.
  reflexivity. }
rewrite Eh.
rewrite Ef.
exact RankedLayers_stable (Lean_List A) (fun x => LeanNat_ord (Lean_List_length A x))
  (fun k x => Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (LeanNum k) A x le) (LeanMergeSort_layers u Hu A HA le Hle)
  (LeanNat_ord f) (LeanNat_ord_nat f Hf)
  (ordsucc (LeanNat_ord (Lean_List_length A h))) (nat_ordsucc (LeanNat_ord (Lean_List_length A h)) (LeanNat_ord_nat (Lean_List_length A h) Hlen))
  h Hh Hbelow (ordsuccI2 (LeanNat_ord (Lean_List_length A h))).
Qed.

(** Lean's equations List.mergeSort.eq_1, eq_2 and eq_3, for the reading. **)
Theorem LeanMergeSort_equation_1 : forall l_u_1, nat_p l_u_1 -> forall v_u945 :e LeanUniv l_u_1, forall v_x :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)), (Lean_List_mergeSort v_u945 (Lean_List_nil_node v_u945) v_x) = (Lean_List_nil_node v_u945).
let l_u_1. assume Hu: nat_p l_u_1. let v_u945. assume HA: v_u945 :e LeanUniv l_u_1.
let v_x. assume Hle: v_x :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)).
prove Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node (Lean_List_length v_u945 (Lean_List_nil_node v_u945))) v_u945 (Lean_List_nil_node v_u945) v_x = Lean_List_nil_node v_u945.
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel_case0 (Lean_List_length v_u945 (Lean_List_nil_node v_u945))
  (Lean_List_length_In v_u945 (Lean_List_nil_node v_u945) (Lean_List_nil_typed v_u945)) l_u_1 Hu v_u945 HA v_x Hle.
Qed.

Theorem LeanMergeSort_equation_2 : forall l_u_1, nat_p l_u_1 -> forall v_u945 :e LeanUniv l_u_1, forall v_x :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)), forall v_a :e v_u945, (Lean_List_mergeSort v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_nil_node v_u945)) v_x) = (Lean_List_cons_node v_u945 v_a (Lean_List_nil_node v_u945)).
let l_u_1. assume Hu: nat_p l_u_1. let v_u945. assume HA: v_u945 :e LeanUniv l_u_1.
let v_x. assume Hle: v_x :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)). let v_a. assume Ha: v_a :e v_u945.
prove Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_nil_node v_u945)))) v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_nil_node v_u945)) v_x
  = Lean_List_cons_node v_u945 v_a (Lean_List_nil_node v_u945).
exact Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel_case1 (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_nil_node v_u945)))
  (Lean_List_length_In v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_nil_node v_u945))
    (Lean_List_cons_typed v_u945 v_a Ha (Lean_List_nil_node v_u945) (Lean_List_nil_typed v_u945)))
  l_u_1 Hu v_u945 HA v_x Hle v_a Ha.
Qed.

Theorem LeanMergeSort_equation_3 : forall l_u_1, nat_p l_u_1 -> forall v_u945 :e LeanUniv l_u_1, forall v_x :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)), forall v_a :e v_u945, forall v_b :e v_u945, forall v_xs :e (Lean_List v_u945), (Lean_List_mergeSort v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) v_x) = (Lean_List_merge v_u945 (Lean_List_mergeSort v_u945 (Lean_Subtype_val (Lean_List v_u945) (fun v_l :e (Lean_List v_u945) => (Lean_Eq_Prop Lean_Nat (Lean_List_length v_u945 v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (LeanNum 1)) (LeanNum 2)))) (Lean_Prod_fst (Lean_Subtype (Lean_List v_u945) (fun v_l :e (Lean_List v_u945) => (Lean_Eq_Prop Lean_Nat (Lean_List_length v_u945 v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (LeanNum 1)) (LeanNum 2))))) (Lean_Subtype (Lean_List v_u945) (fun v_l :e (Lean_List v_u945) => (Lean_Eq_Prop Lean_Nat (Lean_List_length v_u945 v_l) (Lean_Nat_div (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (LeanNum 2))))) (Lean_List_MergeSort_Internal_splitInTwo v_u945 (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (Lean_Subtype_mk_node (Lean_List v_u945) (fun v_l :e (Lean_List v_u945) => (Lean_Eq_Prop Lean_Nat (Lean_List_length v_u945 v_l) (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))))) (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) 0)))) v_x) (Lean_List_mergeSort v_u945 (Lean_Subtype_val (Lean_List v_u945) (fun v_l :e (Lean_List v_u945) => (Lean_Eq_Prop Lean_Nat (Lean_List_length v_u945 v_l) (Lean_Nat_div (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (LeanNum 2)))) (Lean_Prod_snd (Lean_Subtype (Lean_List v_u945) (fun v_l :e (Lean_List v_u945) => (Lean_Eq_Prop Lean_Nat (Lean_List_length v_u945 v_l) (Lean_Nat_div (Lean_Nat_add (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (LeanNum 1)) (LeanNum 2))))) (Lean_Subtype (Lean_List v_u945) (fun v_l :e (Lean_List v_u945) => (Lean_Eq_Prop Lean_Nat (Lean_List_length v_u945 v_l) (Lean_Nat_div (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (LeanNum 2))))) (Lean_List_MergeSort_Internal_splitInTwo v_u945 (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (Lean_Subtype_mk_node (Lean_List v_u945) (fun v_l :e (Lean_List v_u945) => (Lean_Eq_Prop Lean_Nat (Lean_List_length v_u945 v_l) (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))))) (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) 0)))) v_x) v_x).
let l_u_1. assume Hu: nat_p l_u_1. let v_u945. assume HA: v_u945 :e LeanUniv l_u_1.
let v_x. assume Hle: v_x :e (Pi_ ux :e v_u945, (Pi_ ux :e v_u945, Lean_Bool)). let v_a. assume Ha: v_a :e v_u945. let v_b. assume Hb: v_b :e v_u945.
let v_xs. assume Hxs: v_xs :e (Lean_List v_u945).
claim Hl: (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) :e Lean_List v_u945.
{ exact Lean_List_cons_typed v_u945 v_a Ha (Lean_List_cons_node v_u945 v_b v_xs) (Lean_List_cons_typed v_u945 v_b Hb v_xs Hxs). }
claim Hlen: Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) :e Lean_Nat.
{ exact Lean_List_length_In v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) Hl. }
prove Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)))) v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) v_x
  = Lean_List_merge v_u945
      (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node (Lean_List_length v_u945 (LeanMergeSort_half1 v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))))) v_u945 (LeanMergeSort_half1 v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) v_x)
      (Lean_Mettapedia_Languages_Lean_Recursion_FuelCore_MergeSort_sourceFuel (Lean_Nat_succ_node (Lean_List_length v_u945 (LeanMergeSort_half2 v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))))) v_u945 (LeanMergeSort_half2 v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) v_x)
      v_x.
rewrite LeanMergeSort_level_at (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) Hlen l_u_1 Hu v_u945 HA v_x Hle v_a Ha v_b Hb v_xs Hxs.
apply LeanMergeSort_halves_below v_u945 v_a Ha v_b Hb v_xs Hxs.
assume Hb1: LeanNat_ord (Lean_List_length v_u945 (LeanMergeSort_half1 v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)))) :e LeanNat_ord (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))).
assume Hb2: LeanNat_ord (Lean_List_length v_u945 (LeanMergeSort_half2 v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)))) :e LeanNat_ord (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))).
rewrite LeanMergeSort_at_length l_u_1 Hu v_u945 HA v_x Hle (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) Hlen
  (LeanMergeSort_half1 v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (LeanMergeSort_half1_In v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) Hl) Hb1.
rewrite LeanMergeSort_at_length l_u_1 Hu v_u945 HA v_x Hle (Lean_List_length v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) Hlen
  (LeanMergeSort_half2 v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs))) (LeanMergeSort_half2_In v_u945 (Lean_List_cons_node v_u945 v_a (Lean_List_cons_node v_u945 v_b v_xs)) Hl) Hb2.
reflexivity.
Qed.
