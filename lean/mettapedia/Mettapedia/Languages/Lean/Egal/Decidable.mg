(** Decidable propositions and canonical readouts.

   In the set model a proof is 0 and a proposition is a truth value, so
   Decidable p has one element for each truth value p: isTrue p 0 when p
   holds, isFalse p 0 otherwise (Lean_DecCanon). A decision procedure is
   interpreted from its definition; its checked typing theorem then identifies
   its result with that canonical element.
   Decisions about the naturals are proved here for numerals: Nat.le by
   its constructors and, negatively, by induction through its recursor; Eq
   by reflexivity and by the injectivity of numerals. **)

Definition Lean_DecCanon : set -> set :=
  fun p => if 0 :e p then Lean_Decidable_isTrue_node p 0 else Lean_Decidable_isFalse_node p 0.

Theorem Lean_DecCanon_true : forall p, 0 :e p -> Lean_DecCanon p = Lean_Decidable_isTrue_node p 0.
let p. assume H: 0 :e p.
exact If_i_1 (0 :e p) (Lean_Decidable_isTrue_node p 0) (Lean_Decidable_isFalse_node p 0) H.
Qed.

Theorem Lean_DecCanon_false : forall p, 0 /:e p -> Lean_DecCanon p = Lean_Decidable_isFalse_node p 0.
let p. assume H: 0 /:e p.
exact If_i_0 (0 :e p) (Lean_Decidable_isTrue_node p 0) (Lean_Decidable_isFalse_node p 0) H.
Qed.

(** A false proposition has the empty function as its refutation. **)
Theorem Lean_refute_0 : forall p :e LeanProp, 0 /:e p -> 0 :e (Pi_ ux :e p, Lean_False_Prop).
let p. assume Hp: p :e LeanProp. assume H0: 0 /:e p.
claim Lp: forall x :e p, False.
{ let x. assume Hx: x :e p. apply H0.
  claim Lx: x = 0.
  { exact In_1_eq_0 x (PowerE 1 p Hp x Hx). }
  rewrite <- Lx. exact Hx. }
prove 0 :e {f :e Power (Sigma_ x :e p, Union Lean_False_Prop) | forall x :e p, f x :e Lean_False_Prop}.
apply SepI (Power (Sigma_ x :e p, Union Lean_False_Prop)) (fun f => forall x :e p, f x :e Lean_False_Prop) 0
  (Empty_In_Power (Sigma_ x :e p, Union Lean_False_Prop)).
let x. assume Hx: x :e p. apply FalseE. exact Lp x Hx.
Qed.

Theorem Lean_DecCanon_In : forall p :e LeanProp, Lean_DecCanon p :e Lean_Decidable p.
let p. assume Hp: p :e LeanProp.
apply xm (0 :e p).
- assume H0: 0 :e p. rewrite Lean_DecCanon_true p H0. exact Lean_Decidable_isTrue_typed p 0 H0.
- assume H0: 0 /:e p. rewrite Lean_DecCanon_false p H0.
  exact Lean_Decidable_isFalse_typed p 0 (Lean_refute_0 p Hp H0).
Qed.

(** The reading principle: Decidable p has exactly one element.  Proved by
    Decidable's own recursor into a proposition, as Lean proves that
    Decidable p is a subsingleton by cases: a proof of p is 0, so isTrue
    carries 0 and p holds; a refutation of p maps every proof of p into
    False, which has none, so p is empty and the refutation is the empty
    function. **)
Theorem Lean_False_Prop_empty : forall x, x /:e Lean_False_Prop.
let x. assume Hx: x :e Lean_False_Prop.
apply SepE2 1 (fun x => exists w, w :e Lean_False) x Hx.
let w. assume Hw: w :e Lean_False.
exact Lean_False_empty w Hw.
Qed.

Theorem Lean_refutation_0 : forall p :e LeanProp, forall h :e (Pi_ ux :e p, Lean_False_Prop),
  0 /:e p /\ h = 0.
let p. assume Hp: p :e LeanProp. let h. assume Hh: h :e (Pi_ ux :e p, Lean_False_Prop).
claim Lx: forall x :e p, x = 0.
{ let x. assume Hx: x :e p. exact In_1_eq_0 x (PowerE 1 p Hp x Hx). }
claim L0: 0 /:e p.
{ assume H0: 0 :e p.
  exact Lean_False_Prop_empty (h 0) (ap_Pi p (fun ux => Lean_False_Prop) h 0 Hh H0). }
claim Lp: forall x, x /:e p.
{ let x. assume Hx: x :e p. apply L0. rewrite <- Lx x Hx. exact Hx. }
claim Lz: (fun u :e p => h u) = 0.
{ apply Empty_eq. let z. assume Hz: z :e (fun u :e p => h u).
  apply lamE p (fun u => h u) z Hz.
  let u. assume Hu.
  apply Hu. assume Hu1: u :e p. assume Hu2.
  exact Lp u Hu1. }
apply andI.
- exact L0.
- rewrite <- Pi_eta p (fun ux => Lean_False_Prop) h Hh. exact Lz.
Qed.

(** A proof of a proposition is 0, so a proposition with a proof has 0. **)
Theorem Lean_prop_0_of : forall p :e LeanProp, forall h :e p, 0 :e p.
let p. assume Hp: p :e LeanProp. let h. assume Hh: h :e p.
claim Lh: h = 0.
{ exact In_1_eq_0 h (PowerE 1 p Hp h Hh). }
rewrite <- Lh. exact Hh.
Qed.

(** A proposition is refuted when it implies a refuted one. **)
Theorem Lean_refute_by : forall c :e LeanProp, forall h :e (Pi_ ux :e c, Lean_False_Prop),
  forall p :e LeanProp, (0 :e p -> 0 :e c) -> 0 :e (Pi_ ux :e p, Lean_False_Prop).
let c. assume Hc: c :e LeanProp. let h. assume Hh: h :e (Pi_ ux :e c, Lean_False_Prop).
let p. assume Hp: p :e LeanProp. assume Himp: 0 :e p -> 0 :e c.
apply Lean_refute_0 p Hp.
assume H0: 0 :e p.
apply andEL (0 /:e c) (h = 0) (Lean_refutation_0 c Hc h Hh).
exact Himp H0.
Qed.

Theorem Lean_Decidable_unique : forall p :e LeanProp, forall d :e Lean_Decidable p,
  d = Lean_DecCanon p.
let p. assume Hp: p :e LeanProp. let d. assume Hd: d :e Lean_Decidable p.
claim H0: (fun x0 :e (Pi_ ux :e p, Lean_False_Prop) => 0)
  :e (Pi_ x0 :e (Pi_ ux :e p, Lean_False_Prop), {z :e 1 | Lean_Decidable_isFalse_node p x0 = Lean_DecCanon p}).
{ apply lam_Pi (Pi_ ux :e p, Lean_False_Prop)
    (fun x0 => {z :e 1 | Lean_Decidable_isFalse_node p x0 = Lean_DecCanon p}) (fun x0 => 0).
  let x0. assume Hx0: x0 :e (Pi_ ux :e p, Lean_False_Prop).
  apply Lean_refutation_0 p Hp x0 Hx0. assume Hn: 0 /:e p. assume Hz: x0 = 0.
  apply SepI 1 (fun z => Lean_Decidable_isFalse_node p x0 = Lean_DecCanon p) 0 In_0_1.
  rewrite Lean_DecCanon_false p Hn. rewrite Hz. reflexivity. }
claim H1: (fun x0 :e p => 0) :e (Pi_ x0 :e p, {z :e 1 | Lean_Decidable_isTrue_node p x0 = Lean_DecCanon p}).
{ apply lam_Pi p (fun x0 => {z :e 1 | Lean_Decidable_isTrue_node p x0 = Lean_DecCanon p}) (fun x0 => 0).
  let x0. assume Hx0: x0 :e p.
  claim Lx: x0 = 0.
  { exact In_1_eq_0 x0 (PowerE 1 p Hp x0 Hx0). }
  claim L0: 0 :e p.
  { rewrite <- Lx. exact Hx0. }
  apply SepI 1 (fun z => Lean_Decidable_isTrue_node p x0 = Lean_DecCanon p) 0 In_0_1.
  rewrite Lean_DecCanon_true p L0. rewrite Lx. reflexivity. }
claim LR: Lean_Decidable_rec p (fun x0 :e (Pi_ ux :e p, Lean_False_Prop) => 0) (fun x0 :e p => 0) d
  :e {z :e 1 | d = Lean_DecCanon p}.
{ exact Lean_Decidable_rec_type p (fun t => {z :e 1 | t = Lean_DecCanon p})
    (fun x0 :e (Pi_ ux :e p, Lean_False_Prop) => 0) H0 (fun x0 :e p => 0) H1 d Hd. }
exact SepE2 1 (fun z => d = Lean_DecCanon p)
  (Lean_Decidable_rec p (fun x0 :e (Pi_ ux :e p, Lean_False_Prop) => 0) (fun x0 :e p => 0) d) LR.
Qed.

(** Case analysis on the canonical element: the minor for isTrue at the
    proof 0 when p holds, the minor for isFalse at the refutation 0 when it
    does not. **)
Theorem Lean_DecCanon_rec_true : forall p, 0 :e p -> forall h0 h1, Lean_Decidable_rec p h0 h1 (Lean_DecCanon p) = h1 0.
let p. assume H: 0 :e p. let h0 h1.
rewrite Lean_DecCanon_true p H.
exact Lean_Decidable_iota1 p h0 h1 0 H.
Qed.

Theorem Lean_DecCanon_rec_false : forall p :e LeanProp, 0 /:e p -> forall h0 h1,
  Lean_Decidable_rec p h0 h1 (Lean_DecCanon p) = h0 0.
let p. assume Hp: p :e LeanProp. assume H: 0 /:e p. let h0 h1.
rewrite Lean_DecCanon_false p H.
exact Lean_Decidable_iota0 p h0 h1 0 (Lean_refute_0 p Hp H).
Qed.
