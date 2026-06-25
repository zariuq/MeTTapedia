(* ============================================================================
   Program Verification / CoqPLF — Imp: a toy imperative language + its
   big-step operational semantics, with concrete evaluations.
   (MeTTaKernel curriculum, 4th pillar; self-contained vanilla Rocq/Coq 9.1.)
   Spine after Software Foundations (PLF/LF Imp), but self-contained so it
   `coqc`-checks without the SF build system.  NEGATIVES inline via `Fail`.
   ========================================================================== *)

(* ---- States: variables are nat ids, a state maps them to nat values -------- *)
Definition state := nat -> nat.
Definition empty : state := fun _ => 0.
Definition update (st : state) (x v : nat) : state :=
  fun y => if Nat.eqb x y then v else st y.

(* ---- Arithmetic expressions + their evaluator ------------------------------ *)
Inductive aexp : Type :=
| ANum (n : nat)
| AVar (x : nat)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AVar x => st x
  | APlus a1 a2 => aeval st a1 + aeval st a2
  | AMinus a1 a2 => aeval st a1 - aeval st a2
  | AMult a1 a2 => aeval st a1 * aeval st a2
  end.

(* ---- Boolean expressions + their evaluator --------------------------------- *)
Inductive bexp : Type :=
| BTrue | BFalse
| BEq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (aeval st a1) (aeval st a2)
  | BLe a1 a2 => Nat.leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

(* ---- Commands -------------------------------------------------------------- *)
Inductive com : Type :=
| CSkip
| CAsgn (x : nat) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

(* ---- Big-step operational semantics (an inductive evaluation relation) ----- *)
Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st, ceval CSkip st st
| E_Asgn : forall st x a, ceval (CAsgn x a) st (update st x (aeval st a))
| E_Seq : forall c1 c2 st st' st'',
    ceval c1 st st' -> ceval c2 st' st'' -> ceval (CSeq c1 c2) st st''
| E_IfTrue : forall b c1 c2 st st',
    beval st b = true -> ceval c1 st st' -> ceval (CIf b c1 c2) st st'
| E_IfFalse : forall b c1 c2 st st',
    beval st b = false -> ceval c2 st st' -> ceval (CIf b c1 c2) st st'
| E_WhileFalse : forall b c st,
    beval st b = false -> ceval (CWhile b c) st st
| E_WhileTrue : forall b c st st' st'',
    beval st b = true -> ceval c st st' -> ceval (CWhile b c) st' st'' ->
    ceval (CWhile b c) st st''.

(* ---- A concrete program runs to a concrete state --------------------------- *)
(* X := 2 ;; Y := X + 1     (X = var 0, Y = var 1) *)
Definition prog : com :=
  CSeq (CAsgn 0 (ANum 2))
       (CAsgn 1 (APlus (AVar 0) (ANum 1))).

Example prog_eval : ceval prog empty (update (update empty 0 2) 1 3).
Proof.
  unfold prog.
  apply E_Seq with (st' := update empty 0 2).
  - apply E_Asgn.
  - apply E_Asgn.
Qed.

(* a conditional that takes the true branch *)
Example if_eval :
  ceval (CIf (BLe (AVar 0) (ANum 5)) (CAsgn 1 (ANum 1)) (CAsgn 1 (ANum 0)))
        (update empty 0 2)
        (update (update empty 0 2) 1 1).
Proof.
  apply E_IfTrue.
  - reflexivity.
  - apply E_Asgn.
Qed.

(* ---- NEGATIVES : the checker rejects ill-formed programs -------------------- *)
(* a variable slot must be a nat id, not an aexp *)
Fail Definition bad_asgn : com := CAsgn (ANum 0) (ANum 1).
(* APlus is binary — under-application is rejected *)
Fail Definition bad_aexp : aexp := APlus (ANum 1).
