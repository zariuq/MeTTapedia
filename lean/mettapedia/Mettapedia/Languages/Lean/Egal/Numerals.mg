(** Natural numbers in three roles, kept apart.

   Three kinds of natural number meet in this interpretation:
     - Egal's own ordinals 0, 1, 2, ... (nat_p): universe levels, constructor
       tags, arities and positions in the generated signatures;
     - Lean's Nat, the generated family Lean_Nat, whose values are nodes;
     - the integers printed by a CeTTa run, which are text.
   A Lean literal n and a CeTTa integer n are both read as LeanNum n: the
   ordinal n carried into Lean_Nat by zero and successor.  LeanNum is
   injective, so distinct integers are read as distinct Lean naturals.

   The ordinal and the Lean reading of a number coincide for 0, 1 and 2
   (LeanNum_0_ord, LeanNum_1_ord, LeanNum_2_ord) and differ from 3 on
   (LeanNum_3_not_3).  A confusion of the two roles would therefore pass
   every check that only uses 0, 1 and 2; the controls use larger numbers.

   LeanNum itself, with LeanNum_0, LeanNum_S, LeanNum_In and LeanNum_inj, is
   generated with the Nat family, so that the families after it read their
   closed natural indices as literals. **)

(** Positive examples: the two readings coincide on 0, 1 and 2. **)

Theorem LeanNum_0_ord : LeanNum 0 = 0.
rewrite LeanNum_0.
prove setsum (setsum 0 (SeqAt (SeqCons 0 (SeqCons 0 SeqNil)) 0)) (TupArgs 0 SeqNil) = 0.
rewrite Lean_Nat_O0 (TupArgs 0 SeqNil).
claim L: TupArgs 0 SeqNil = 0.
{ apply Empty_eq. let z. assume Hz: z :e TupArgs 0 SeqNil.
  apply lamE 0 (fun j => SeqAt SeqNil j) z Hz.
  let x. assume Hx: x :e 0 /\ exists y :e SeqAt SeqNil x, z = setsum x y.
  exact EmptyE x (andEL (x :e 0) (exists y :e SeqAt SeqNil x, z = setsum x y) Hx). }
rewrite L. rewrite setsum_0_0. exact setsum_0_0.
Qed.

(** The only position below 1 is 0. **)
Theorem In_1_eq_0 : forall x :e 1, x = 0.
let x. assume Hx: x :e 1.
apply ordsuccE 0 x Hx.
- assume H: x :e 0. prove False. exact EmptyE x H.
- assume H: x = 0. exact H.
Qed.

(** A successor node is the pair of its tag 1 with its argument tuple. **)
Theorem Lean_Nat_succ_node_pair : forall x, Lean_Nat_succ_node x = setsum 1 (TupArgs 1 (SeqCons x SeqNil)).
let x.
prove setsum (setsum 1 (SeqAt (SeqCons 0 (SeqCons 0 SeqNil)) 1)) (TupArgs 1 (SeqCons x SeqNil)) = setsum 1 (TupArgs 1 (SeqCons x SeqNil)).
rewrite Lean_Nat_O1 (TupArgs 1 (SeqCons x SeqNil)).
rewrite setsum_1_0_1.
reflexivity.
Qed.

(** The one-field tuple of x has the members setsum 0 y for y :e x. **)
Theorem TupArgs_1_E : forall x z, z :e TupArgs 1 (SeqCons x SeqNil) -> exists y :e x, z = setsum 0 y.
let x z. assume Hz: z :e TupArgs 1 (SeqCons x SeqNil).
apply lamE 1 (fun j => SeqAt (SeqCons x SeqNil) j) z Hz.
let j. assume Hj: j :e 1 /\ exists y :e SeqAt (SeqCons x SeqNil) j, z = setsum j y.
apply Hj. assume Hj1: j :e 1. assume Hj2: exists y :e SeqAt (SeqCons x SeqNil) j, z = setsum j y.
claim L0: j = 0.
{ exact In_1_eq_0 j Hj1. }
apply Hj2. let y. assume Hy: y :e SeqAt (SeqCons x SeqNil) j /\ z = setsum j y.
apply Hy. assume Hy1: y :e SeqAt (SeqCons x SeqNil) j. assume Hy2: z = setsum j y.
witness y. apply andI.
- prove y :e x.
  exact In_eq_r y (SeqAt (SeqCons x SeqNil) 0) x (SeqAt_0 x SeqNil)
    (In_fam_eq (fun i => SeqAt (SeqCons x SeqNil) i) j 0 L0 y Hy1).
- prove z = setsum 0 y.
  rewrite <- L0. exact Hy2.
Qed.

Theorem TupArgs_1_I : forall x y, y :e x -> setsum 0 y :e TupArgs 1 (SeqCons x SeqNil).
let x y. assume Hy: y :e x.
claim L: y :e SeqAt (SeqCons x SeqNil) 0.
{ rewrite SeqAt_0. exact Hy. }
exact lamI 1 (fun j => SeqAt (SeqCons x SeqNil) j) 0 In_0_1 y L.
Qed.

Theorem LeanNum_1_ord : LeanNum 1 = 1.
rewrite LeanNum_S 0 nat_0. rewrite LeanNum_0_ord. rewrite Lean_Nat_succ_node_pair.
claim L: TupArgs 1 (SeqCons 0 SeqNil) = 0.
{ apply Empty_eq. let z. assume Hz: z :e TupArgs 1 (SeqCons 0 SeqNil).
  apply TupArgs_1_E 0 z Hz. let y. assume Hy: y :e 0 /\ z = setsum 0 y.
  exact EmptyE y (andEL (y :e 0) (z = setsum 0 y) Hy). }
rewrite L. exact setsum_1_0_1.
Qed.

Theorem LeanNum_2_ord : LeanNum 2 = 2.
rewrite LeanNum_S 1 nat_1. rewrite LeanNum_1_ord. rewrite Lean_Nat_succ_node_pair.
claim L: TupArgs 1 (SeqCons 1 SeqNil) = 1.
{ apply set_ext.
  - let z. assume Hz: z :e TupArgs 1 (SeqCons 1 SeqNil).
    apply TupArgs_1_E 1 z Hz. let y. assume Hy: y :e 1 /\ z = setsum 0 y.
    apply Hy. assume Hy1: y :e 1. assume Hy2: z = setsum 0 y.
    rewrite Hy2. rewrite In_1_eq_0 y Hy1. rewrite setsum_0_0. exact In_0_1.
  - let z. assume Hz: z :e 1.
    rewrite In_1_eq_0 z Hz.
    exact In_eq_l (setsum 0 0) 0 (TupArgs 1 (SeqCons 1 SeqNil)) setsum_0_0 (TupArgs_1_I 1 0 In_0_1). }
rewrite L. exact setsum_1_1_2.
Qed.

(** Negative example: from 3 on the readings differ.  3 is the pair of 1
    with 2, so LeanNum 3 = 3 would make the tuple of LeanNum 2 equal to 2,
    whose member 1 contains 0; no member setsum 0 y of a tuple does. **)
Theorem LeanNum_3_not_3 : LeanNum 3 <> 3.
assume H: LeanNum 3 = 3.
claim L3: LeanNum 3 = setsum 1 (TupArgs 1 (SeqCons 2 SeqNil)).
{ rewrite LeanNum_S 2 nat_2. rewrite LeanNum_2_ord. exact Lean_Nat_succ_node_pair 2. }
claim Lp: setsum 1 (TupArgs 1 (SeqCons 2 SeqNil)) = setsum 1 2.
{ rewrite <- L3. rewrite H. exact eq_sym_i (setsum 1 2) 3 (nat_pair1_ordsucc 2 nat_2). }
claim La: TupArgs 1 (SeqCons 2 SeqNil) = 2.
{ exact andER (1 = 1) (TupArgs 1 (SeqCons 2 SeqNil) = 2) (pair_inj 1 (TupArgs 1 (SeqCons 2 SeqNil)) 1 2 Lp). }
claim L1: 1 :e TupArgs 1 (SeqCons 2 SeqNil).
{ rewrite La. exact In_1_2. }
apply TupArgs_1_E 2 1 L1. let y. assume Hy: y :e 2 /\ 1 = setsum 0 y.
claim L0: 0 :e Inj0 y.
{ rewrite <- Inj0_setsum_0L y. rewrite <- andER (y :e 2) (1 = setsum 0 y) Hy. exact In_0_1. }
apply Inj0E y 0 L0. let t. assume Ht: t :e y /\ 0 = Inj1 t.
exact Inj1NE1 t (eq_sym_i 0 (Inj1 t) (andER (t :e y) (0 = Inj1 t) Ht)).
Qed.

(** Lean writes the pattern zero as the literal 0 in some equation
    theorems, as for multiplication by zero; there it is read as the
    constructor, at that position only. **)
Theorem LeanNum_0_at : forall F:set -> set, forall G, F Lean_Nat_zero_node = G -> F (LeanNum 0) = G.
let F G. assume H: F Lean_Nat_zero_node = G.
rewrite LeanNum_0. exact H.
Qed.

(** Booleans coincide the same way: false and true are the sets 0 and 1,
    the truth values of LeanProp. **)
Theorem TupArgs_0_eq : forall s, TupArgs 0 s = 0.
let s. apply Empty_eq. let z. assume Hz: z :e TupArgs 0 s.
apply lamE 0 (fun j => SeqAt s j) z Hz.
let x. assume Hx: x :e 0 /\ exists y :e SeqAt s x, z = setsum x y.
exact EmptyE x (andEL (x :e 0) (exists y :e SeqAt s x, z = setsum x y) Hx).
Qed.

Theorem Lean_Bool_false_ord : Lean_Bool_false_node = 0.
prove setsum (setsum 0 (SeqAt (SeqCons 0 (SeqCons 0 SeqNil)) 0)) (TupArgs 0 SeqNil) = 0.
rewrite Lean_Bool_O0 (TupArgs 0 SeqNil).
rewrite TupArgs_0_eq SeqNil. rewrite setsum_0_0. exact setsum_0_0.
Qed.

Theorem Lean_Bool_true_ord : Lean_Bool_true_node = 1.
prove setsum (setsum 1 (SeqAt (SeqCons 0 (SeqCons 0 SeqNil)) 1)) (TupArgs 0 SeqNil) = 1.
rewrite Lean_Bool_O1 (TupArgs 0 SeqNil).
rewrite TupArgs_0_eq SeqNil. rewrite setsum_1_0_1. exact setsum_1_0_1.
Qed.
