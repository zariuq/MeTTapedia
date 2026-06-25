(* ============================================================================
   Program Verification / CoqPLF — Hoare logic over Imp
   (MeTTaKernel curriculum, 4th pillar; self-contained vanilla Rocq/Coq 9.1.)
   Big-step Imp + Hoare triples {P} c {Q}, the skip/assign/seq/consequence
   rules proved sound against the operational semantics, and a worked triple.
   Spine after Software Foundations PLF (Hoare).  NEGATIVE inline via `Fail`.
   ========================================================================== *)

(* ---- Imp core (states, expressions, commands, big-step semantics) ---------- *)
Definition state := nat -> nat.
Definition empty : state := fun _ => 0.
Definition update (st : state) (x v : nat) : state :=
  fun y => if Nat.eqb x y then v else st y.

Inductive aexp : Type :=
| ANum (n : nat) | AVar (x : nat)
| APlus (a1 a2 : aexp) | AMinus (a1 a2 : aexp) | AMult (a1 a2 : aexp).

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n | AVar x => st x
  | APlus a1 a2 => aeval st a1 + aeval st a2
  | AMinus a1 a2 => aeval st a1 - aeval st a2
  | AMult a1 a2 => aeval st a1 * aeval st a2
  end.

Inductive bexp : Type :=
| BTrue | BFalse | BEq (a1 a2 : aexp) | BLe (a1 a2 : aexp)
| BNot (b : bexp) | BAnd (b1 b2 : bexp).

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true | BFalse => false
  | BEq a1 a2 => Nat.eqb (aeval st a1) (aeval st a2)
  | BLe a1 a2 => Nat.leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1) | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Inductive com : Type :=
| CSkip | CAsgn (x : nat) (a : aexp) | CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com) | CWhile (b : bexp) (c : com).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st, ceval CSkip st st
| E_Asgn : forall st x a, ceval (CAsgn x a) st (update st x (aeval st a))
| E_Seq  : forall c1 c2 st st' st'', ceval c1 st st' -> ceval c2 st' st'' -> ceval (CSeq c1 c2) st st''
| E_IfTrue : forall b c1 c2 st st', beval st b = true  -> ceval c1 st st' -> ceval (CIf b c1 c2) st st'
| E_IfFalse: forall b c1 c2 st st', beval st b = false -> ceval c2 st st' -> ceval (CIf b c1 c2) st st'
| E_WhileFalse : forall b c st, beval st b = false -> ceval (CWhile b c) st st
| E_WhileTrue  : forall b c st st' st'', beval st b = true -> ceval c st st' ->
    ceval (CWhile b c) st' st'' -> ceval (CWhile b c) st st''.

(* read-after-write on the store *)
Lemma eqb_refl' : forall x, Nat.eqb x x = true.
Proof. induction x as [| x IH]; simpl. - reflexivity. - exact IH. Qed.
Lemma update_eq : forall st x v, update st x v x = v.
Proof. intros st x v. unfold update. rewrite eqb_refl'. reflexivity. Qed.

(* ---- Hoare triples : partial-correctness assertions ------------------------ *)
Definition assertion := state -> Prop.
Definition hoare (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall st st', ceval c st st' -> P st -> Q st'.

(* the structural rules, proved SOUND against the operational semantics *)
Theorem hoare_skip : forall P, hoare P CSkip P.
Proof. intros P st st' Hc HP. inversion Hc; subst. exact HP. Qed.

Theorem hoare_asgn : forall Q x a,
  hoare (fun st => Q (update st x (aeval st a))) (CAsgn x a) Q.
Proof. intros Q x a st st' Hc HP. inversion Hc; subst. exact HP. Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  hoare P c1 Q -> hoare Q c2 R -> hoare P (CSeq c1 c2) R.
Proof.
  intros P Q R c1 c2 H1 H2 st st' Hc HP. inversion Hc; subst.
  eapply H2; [ eassumption | eapply H1; [ eassumption | exact HP ] ].
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : assertion) c,
  (forall st, P' st -> P st) -> hoare P c Q -> hoare P' c Q.
Proof. intros P P' Q c Himp H st st' Hc HP'. apply (H st st' Hc). apply Himp. exact HP'. Qed.

(* ---- A worked triple : {X+1 = 3}  Y := X+1  {Y = 3}   (X=0, Y=1) ----------- *)
Example hoare_asgn_example :
  hoare (fun st => st 0 + 1 = 3) (CAsgn 1 (APlus (AVar 0) (ANum 1))) (fun st => st 1 = 3).
Proof.
  eapply hoare_consequence_pre; [ | apply hoare_asgn ].
  intros st HP. simpl. exact HP.
Qed.

(* ---- NEGATIVE : a command sequence needs two commands ---------------------- *)
Fail Definition bad_seq : com := CSeq CSkip.
