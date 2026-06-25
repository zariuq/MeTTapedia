(* ============================================================================
   ICL Ch.10-11 — COMPLETENESS of CLASSICAL natural deduction (Kalmar's theorem)
   (MeTTaKernel curriculum, DTT ladder, Coq).  The implicational-falsum fragment
   {->, _|_} with a classical calculus (ND + reductio ad absurdum), proved
   COMPLETE for the boolean semantics: every tautology is derivable.
   (Intuitionistic ND is NOT classically complete -- a /\ ~a etc. -- so the
   calculus here adds `nd_raa`.  This file builds the structural lemmas; Kalmar's
   lemma + completeness are added on top.)
   ========================================================================== *)

From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.

Inductive form : Type := Var (n : nat) | Bot | Imp (a b : form).
Definition Neg (a : form) : form := Imp a Bot.

(* ---- Classical natural deduction (reductio is the classical rule) ---------- *)
Inductive nd : list form -> form -> Prop :=
| nd_ax   : forall G a, In a G -> nd G a
| nd_impI : forall G a b, nd (a :: G) b -> nd G (Imp a b)
| nd_impE : forall G a b, nd G (Imp a b) -> nd G a -> nd G b
| nd_raa  : forall G a, nd (Neg a :: G) Bot -> nd G a.

(* ---- Weakening (context inclusion) ----------------------------------------- *)
Lemma nd_mono : forall G a, nd G a -> forall G', incl G G' -> nd G' a.
Proof.
  intros G a D.
  induction D as [G p Hin | G p q D IH | G p q D1 IH1 D2 IH2 | G p D IH];
    intros G' Hs.
  - apply nd_ax. apply Hs. exact Hin.
  - apply nd_impI. apply IH. intros x [Hx | Hx]. + left; exact Hx. + right; apply Hs; exact Hx.
  - apply nd_impE with p. + apply IH1; exact Hs. + apply IH2; exact Hs.
  - apply nd_raa. apply IH. intros x [Hx | Hx]. + left; exact Hx. + right; apply Hs; exact Hx.
Qed.

Lemma nd_weak : forall G a p, nd G a -> nd (p :: G) a.
Proof. intros G a p D. apply nd_mono with G. exact D. intros x Hx. right. exact Hx. Qed.

(* ex falso is derivable from reductio *)
Lemma nd_botE : forall G a, nd G Bot -> nd G a.
Proof. intros G a D. apply nd_raa. apply nd_weak. exact D. Qed.

(* ---- The classical CASE SPLIT : the heart of Kalmar's argument ------------- *)
Lemma nd_cases : forall G p a, nd (p :: G) a -> nd (Neg p :: G) a -> nd G a.
Proof.
  intros G p a H1 H2. apply nd_raa.
  assert (Dnp : nd (Neg a :: G) (Neg p)).
  { apply nd_impI. apply nd_impE with a.
    - apply nd_ax. right; left; reflexivity.
    - apply nd_mono with (p :: G). exact H1.
      intros x [Hx | Hx]. left; exact Hx. right; right; exact Hx. }
  assert (Dnnp : nd (Neg a :: G) (Neg (Neg p))).
  { apply nd_impI. apply nd_impE with a.
    - apply nd_ax. right; left; reflexivity.
    - apply nd_mono with (Neg p :: G). exact H2.
      intros x [Hx | Hx]. left; exact Hx. right; right; exact Hx. }
  apply nd_impE with (Neg p). exact Dnnp. exact Dnp.
Qed.

(* ---- Boolean semantics + signed contexts (Kalmar) -------------------------- *)
Fixpoint eval (v : nat -> bool) (f : form) : bool :=
  match f with
  | Var n   => v n
  | Bot     => false
  | Imp a b => implb (eval v a) (eval v b)
  end.

Definition signLit (v : nat -> bool) (n : nat) : form := if v n then Var n else Neg (Var n).
Definition signF   (v : nat -> bool) (a : form) : form := if eval v a then a else Neg a.

Fixpoint vars (a : form) : list nat :=
  match a with Var n => [n] | Bot => [] | Imp a b => vars a ++ vars b end.

(* Kalmar's lemma: the signed atoms of `a` derive the signed `a`, under any v *)
Lemma kalmar : forall a v, nd (map (signLit v) (vars a)) (signF v a).
Proof.
  induction a as [n | | a IHa b IHb]; intros v.
  - (* Var n *) unfold signF, signLit; simpl. destruct (v n); apply nd_ax; left; reflexivity.
  - (* Bot *) unfold signF; simpl. apply nd_impI. apply nd_ax. left. reflexivity.
  - (* Imp a b *)
    simpl. rewrite map_app.
    assert (Wa : nd (map (signLit v) (vars a) ++ map (signLit v) (vars b)) (signF v a)).
    { apply nd_mono with (map (signLit v) (vars a)). exact (IHa v). apply incl_appl. apply incl_refl. }
    assert (Wb : nd (map (signLit v) (vars a) ++ map (signLit v) (vars b)) (signF v b)).
    { apply nd_mono with (map (signLit v) (vars b)). exact (IHb v). apply incl_appr. apply incl_refl. }
    unfold signF in *. simpl in *.
    destruct (eval v a) eqn:Ea; destruct (eval v b) eqn:Eb; simpl in *.
    + (* T,T : signF(a->b) = a->b *) apply nd_impI. apply nd_weak. exact Wb.
    + (* T,F : signF = Neg(a->b) *)
      apply nd_impI. apply nd_impE with b.
      * apply nd_weak. exact Wb.
      * apply nd_impE with a. apply nd_ax; left; reflexivity. apply nd_weak. exact Wa.
    + (* F,T *) apply nd_impI. apply nd_weak. exact Wb.
    + (* F,F : signF = a->b, from Neg a *)
      apply nd_impI. apply nd_botE. apply nd_impE with a.
      apply nd_weak. exact Wa. apply nd_ax; left; reflexivity.
Qed.

(* ---- eliminate the signed atoms one at a time (classical case split) ------- *)
Definition setv (v : nat -> bool) (n : nat) (b : bool) : nat -> bool :=
  fun m => if Nat.eqb n m then b else v m.

Lemma signLit_setv_true : forall v n, signLit (setv v n true) n = Var n.
Proof. intros. unfold signLit, setv. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma signLit_setv_false : forall v n, signLit (setv v n false) n = Neg (Var n).
Proof. intros. unfold signLit, setv. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma map_signLit_setv : forall L v n b, ~ In n L ->
  map (signLit (setv v n b)) L = map (signLit v) L.
Proof.
  induction L as [| m L IH]; intros v n b Hn; simpl.
  - reflexivity.
  - f_equal.
    + unfold signLit, setv. destruct (Nat.eqb n m) eqn:E.
      * apply Nat.eqb_eq in E. subst. exfalso. apply Hn. left. reflexivity.
      * reflexivity.
    + apply IH. intro H. apply Hn. right. exact H.
Qed.

Lemma remove_atoms : forall L a, NoDup L ->
  (forall v, nd (map (signLit v) L) a) -> nd [] a.
Proof.
  induction L as [| n L IH]; intros a Hnd H.
  - exact (H (fun _ => true)).
  - assert (Hn : ~ In n L) by (inversion Hnd; assumption).
    apply IH.
    + inversion Hnd; assumption.
    + intro v. apply nd_cases with (Var n).
      * specialize (H (setv v n true)). simpl in H.
        rewrite signLit_setv_true in H. rewrite (map_signLit_setv L v n true Hn) in H. exact H.
      * specialize (H (setv v n false)). simpl in H.
        rewrite signLit_setv_false in H. rewrite (map_signLit_setv L v n false Hn) in H. exact H.
Qed.

(* ---- COMPLETENESS : every boolean tautology is derivable ------------------- *)
Theorem nd_complete : forall a, (forall v, eval v a = true) -> nd [] a.
Proof.
  intros a Hvalid.
  apply (remove_atoms (nodup Nat.eq_dec (vars a)) a).
  - apply NoDup_nodup.
  - intro v.
    assert (Hk := kalmar a v). unfold signF in Hk. rewrite (Hvalid v) in Hk. simpl in Hk.
    apply nd_mono with (map (signLit v) (vars a)). exact Hk.
    intros x Hx. apply in_map_iff in Hx. destruct Hx as [m [Hm Hmin]].
    apply in_map_iff. exists m. split. exact Hm. apply nodup_In. exact Hmin.
Qed.

(* NEGATIVE: Bot is never true under any valuation *)
Fail Example neg_bot_true : eval (fun _ => true) Bot = true := eq_refl.
