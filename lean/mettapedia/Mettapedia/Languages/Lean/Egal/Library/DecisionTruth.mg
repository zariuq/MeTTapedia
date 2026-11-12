(** A decision is determined by the truth of its proposition.

    A proposition's proofs are a subset of the singleton, so it holds or it
    does not; the element of Decidable p is then isTrue or isFalse, whatever
    the instance.  A conditional is its first branch where the proposition
    holds and its second where it does not: a branch is observed only under
    its guard. **)

Theorem Lean_Decidable_truth : forall p :e LeanProp, forall d :e Lean_Decidable p,
  forall C : set -> prop,
  (0 :e p -> C (Lean_Decidable_isTrue_node p 0)) ->
  (0 /:e p -> C (Lean_Decidable_isFalse_node p 0)) -> C d.
let p. assume Hp: p :e LeanProp. let d. assume Hd: d :e Lean_Decidable p.
let C. assume Htrue: 0 :e p -> C (Lean_Decidable_isTrue_node p 0).
assume Hfalse: 0 /:e p -> C (Lean_Decidable_isFalse_node p 0).
rewrite Lean_Decidable_unique p Hp d Hd.
apply xm (0 :e p).
- assume H: 0 :e p. rewrite Lean_DecCanon_true p H. exact Htrue H.
- assume H: 0 /:e p. rewrite Lean_DecCanon_false p H. exact Hfalse H.
Qed.

Theorem Lean_ite_truth : forall T, forall p :e LeanProp, forall d :e Lean_Decidable p, forall a b,
  forall C : set -> prop, (0 :e p -> C a) -> (0 /:e p -> C b) -> C (Lean_ite T p d a b).
let T p. assume Hp: p :e LeanProp. let d. assume Hd: d :e Lean_Decidable p. let a b C.
assume Ha: 0 :e p -> C a. assume Hb: 0 /:e p -> C b.
apply Lean_Decidable_truth p Hp d Hd (fun e => C (Lean_ite T p e a b)).
- assume H: 0 :e p.
  prove C (Lean_ite T p (Lean_Decidable_isTrue_node p 0) a b).
  rewrite Lean_ite_true_ap T p H a b. exact Ha H.
- assume H: 0 /:e p.
  prove C (Lean_ite T p (Lean_Decidable_isFalse_node p 0) a b).
  rewrite Lean_ite_false_ap T p Hp H a b. exact Hb H.
Qed.

Theorem Lean_dite_truth : forall T, forall p :e LeanProp, forall d :e Lean_Decidable p,
  forall F G : set -> set, forall C : set -> prop,
  (0 :e p -> C (F 0)) -> (0 /:e p -> C (G 0)) ->
  C (Lean_dite T p d (fun h :e p => F h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G h)).
let T p. assume Hp: p :e LeanProp. let d. assume Hd: d :e Lean_Decidable p. let F G C.
assume HF: 0 :e p -> C (F 0). assume HG: 0 /:e p -> C (G 0).
apply Lean_Decidable_truth p Hp d Hd
  (fun e => C (Lean_dite T p e (fun h :e p => F h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G h))).
- assume H: 0 :e p.
  prove C (Lean_dite T p (Lean_Decidable_isTrue_node p 0) (fun h :e p => F h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G h)).
  rewrite Lean_dite_true_ap T p H F G. exact HF H.
- assume H: 0 /:e p.
  prove C (Lean_dite T p (Lean_Decidable_isFalse_node p 0) (fun h :e p => F h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G h)).
  rewrite Lean_dite_false_ap T p Hp H F G. exact HG H.
Qed.

(** Two conditionals on one decision are equal when their branches are,
    each under its guard. **)
Theorem Lean_ite_guarded : forall T, forall p :e LeanProp, forall d :e Lean_Decidable p, forall a b a2 b2,
  (0 :e p -> a = a2) -> (0 /:e p -> b = b2) -> Lean_ite T p d a b = Lean_ite T p d a2 b2.
let T p. assume Hp: p :e LeanProp. let d. assume Hd: d :e Lean_Decidable p. let a b a2 b2.
assume Ha: 0 :e p -> a = a2. assume Hb: 0 /:e p -> b = b2.
apply Lean_Decidable_truth p Hp d Hd (fun e => Lean_ite T p e a b = Lean_ite T p e a2 b2).
- assume H: 0 :e p.
  prove Lean_ite T p (Lean_Decidable_isTrue_node p 0) a b = Lean_ite T p (Lean_Decidable_isTrue_node p 0) a2 b2.
  rewrite Lean_ite_true_ap T p H a b. rewrite Lean_ite_true_ap T p H a2 b2. exact Ha H.
- assume H: 0 /:e p.
  prove Lean_ite T p (Lean_Decidable_isFalse_node p 0) a b = Lean_ite T p (Lean_Decidable_isFalse_node p 0) a2 b2.
  rewrite Lean_ite_false_ap T p Hp H a b. rewrite Lean_ite_false_ap T p Hp H a2 b2. exact Hb H.
Qed.

Theorem Lean_dite_guarded : forall T, forall p :e LeanProp, forall d :e Lean_Decidable p,
  forall F G F2 G2 : set -> set,
  (0 :e p -> F 0 = F2 0) -> (0 /:e p -> G 0 = G2 0) ->
  Lean_dite T p d (fun h :e p => F h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G h)
    = Lean_dite T p d (fun h :e p => F2 h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G2 h).
let T p. assume Hp: p :e LeanProp. let d. assume Hd: d :e Lean_Decidable p. let F G F2 G2.
assume HF: 0 :e p -> F 0 = F2 0. assume HG: 0 /:e p -> G 0 = G2 0.
apply Lean_Decidable_truth p Hp d Hd
  (fun e => Lean_dite T p e (fun h :e p => F h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G h)
    = Lean_dite T p e (fun h :e p => F2 h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G2 h)).
- assume H: 0 :e p.
  prove Lean_dite T p (Lean_Decidable_isTrue_node p 0) (fun h :e p => F h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G h)
    = Lean_dite T p (Lean_Decidable_isTrue_node p 0) (fun h :e p => F2 h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G2 h).
  rewrite Lean_dite_true_ap T p H F G. rewrite Lean_dite_true_ap T p H F2 G2. exact HF H.
- assume H: 0 /:e p.
  prove Lean_dite T p (Lean_Decidable_isFalse_node p 0) (fun h :e p => F h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G h)
    = Lean_dite T p (Lean_Decidable_isFalse_node p 0) (fun h :e p => F2 h) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => G2 h).
  rewrite Lean_dite_false_ap T p Hp H F G. rewrite Lean_dite_false_ap T p Hp H F2 G2. exact HG H.
Qed.

(** A conditional whose branches ignore the proof is the plain conditional. **)
Theorem Lean_dite_plain : forall T p d a b,
  Lean_dite T p d (fun h :e p => a) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => b) = Lean_ite T p d a b.
let T p d a b.
rewrite Lean_dite_unfold T p d (fun h :e p => a) (fun h :e (Pi_ ux :e p, Lean_False_Prop) => b).
rewrite Lean_ite_unfold T p d a b.
reflexivity.
Qed.

(** Positive and negative examples: a true guard hides the second branch, and
    does not hide the first. **)
Theorem Lean_ite_guarded_ex : forall d :e Lean_Decidable (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)),
  Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) d (LeanNum 1) (LeanNum 2)
    = Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) d (LeanNum 1) (LeanNum 3).
let d. assume Hd: d :e Lean_Decidable (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)).
apply Lean_ite_guarded Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0))
  (Lean_Eq_Prop_prop Lean_Nat (LeanNum 0) (LeanNum 0)) d Hd (LeanNum 1) (LeanNum 2) (LeanNum 1) (LeanNum 3).
- assume H: 0 :e Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0). reflexivity.
- assume H: 0 /:e Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0).
  exact FalseE (H (Lean_Eq_num_refl 0)) (LeanNum 2 = LeanNum 3).
Qed.

Theorem Lean_ite_guarded_ex_not : forall d :e Lean_Decidable (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)),
  Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) d (LeanNum 1) (LeanNum 2)
    <> Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) d (LeanNum 3) (LeanNum 2).
let d. assume Hd: d :e Lean_Decidable (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)).
apply Lean_Decidable_truth (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0))
  (Lean_Eq_Prop_prop Lean_Nat (LeanNum 0) (LeanNum 0)) d Hd
  (fun e => Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) e (LeanNum 1) (LeanNum 2)
    <> Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) e (LeanNum 3) (LeanNum 2)).
- assume H: 0 :e Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0).
  prove Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) (Lean_Decidable_isTrue_node (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) 0) (LeanNum 1) (LeanNum 2)
    <> Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) (Lean_Decidable_isTrue_node (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) 0) (LeanNum 3) (LeanNum 2).
  rewrite Lean_ite_true_ap Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) H (LeanNum 1) (LeanNum 2).
  rewrite Lean_ite_true_ap Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) H (LeanNum 3) (LeanNum 2).
  assume Heq: LeanNum 1 = LeanNum 3.
  exact neq_0_2 (ordsucc_inj 0 2 (LeanNum_inj 1 nat_1 3 nat_3 Heq)).
- assume H: 0 /:e Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0).
  exact FalseE (H (Lean_Eq_num_refl 0))
    (Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) (Lean_Decidable_isFalse_node (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) 0) (LeanNum 1) (LeanNum 2)
      <> Lean_ite Lean_Nat (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) (Lean_Decidable_isFalse_node (Lean_Eq_Prop Lean_Nat (LeanNum 0) (LeanNum 0)) 0) (LeanNum 3) (LeanNum 2)).
Qed.
