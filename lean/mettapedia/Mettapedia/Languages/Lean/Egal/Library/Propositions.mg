(** Logical operations on the generated proof-irrelevant proposition families. **)

Theorem LeanIff_forward : forall p q :e LeanProp, forall h :e Lean_Iff_Prop p q,
  0 :e p -> 0 :e q.
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
let h. assume Hh: h :e Lean_Iff_Prop p q. assume H0: 0 :e p.
claim HM: (fun f :e (Pi_ x :e p, q) => fun g :e (Pi_ x :e q, p) => f 0)
  :e (Pi_ f :e (Pi_ x :e p, q), (Pi_ g :e (Pi_ x :e q, p), q)).
{ exact lam_Pi (Pi_ x :e p, q) (fun _ => Pi_ g :e (Pi_ x :e q, p), q)
    (fun f => fun g :e (Pi_ x :e q, p) => f 0)
    (fun f Hf => lam_Pi (Pi_ x :e q, p) (fun _ => q) (fun _ => f 0)
      (fun g Hg => ap_Pi p (fun _ => q) f 0 Hf H0)). }
claim L: Lean_Iff_prec p q
  (fun f :e (Pi_ x :e p, q) => fun g :e (Pi_ x :e q, p) => f 0) h :e q.
{ exact Lean_Iff_prec_type p q (fun _ => q)
    (fun f :e (Pi_ x :e p, q) => fun g :e (Pi_ x :e q, p) => f 0) HM h Hh. }
exact Lean_prop_0_of q Hq
  (Lean_Iff_prec p q (fun f :e (Pi_ x :e p, q) => fun g :e (Pi_ x :e q, p) => f 0) h) L.
Qed.

Theorem LeanIff_backward : forall p q :e LeanProp, forall h :e Lean_Iff_Prop p q,
  0 :e q -> 0 :e p.
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
let h. assume Hh: h :e Lean_Iff_Prop p q. assume H0: 0 :e q.
claim HM: (fun f :e (Pi_ x :e p, q) => fun g :e (Pi_ x :e q, p) => g 0)
  :e (Pi_ f :e (Pi_ x :e p, q), (Pi_ g :e (Pi_ x :e q, p), p)).
{ exact lam_Pi (Pi_ x :e p, q) (fun _ => Pi_ g :e (Pi_ x :e q, p), p)
    (fun f => fun g :e (Pi_ x :e q, p) => g 0)
    (fun f Hf => lam_Pi (Pi_ x :e q, p) (fun _ => p) (fun g => g 0)
      (fun g Hg => ap_Pi q (fun _ => p) g 0 Hg H0)). }
claim L: Lean_Iff_prec p q
  (fun f :e (Pi_ x :e p, q) => fun g :e (Pi_ x :e q, p) => g 0) h :e p.
{ exact Lean_Iff_prec_type p q (fun _ => p)
    (fun f :e (Pi_ x :e p, q) => fun g :e (Pi_ x :e q, p) => g 0) HM h Hh. }
exact Lean_prop_0_of p Hp
  (Lean_Iff_prec p q (fun f :e (Pi_ x :e p, q) => fun g :e (Pi_ x :e q, p) => g 0) h) L.
Qed.

Theorem LeanIff_intro : forall p q :e LeanProp,
  (0 :e p -> 0 :e q) -> (0 :e q -> 0 :e p) -> 0 :e Lean_Iff_Prop p q.
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
assume Hforward: 0 :e p -> 0 :e q. assume Hbackward: 0 :e q -> 0 :e p.
exact Lean_Iff_intro_proof_ok p q 0
  (Pi_0_In p (fun _ => q) (fun x Hx => Hforward (Lean_prop_0_of p Hp x Hx)))
  0 (Pi_0_In q (fun _ => p) (fun x Hx => Hbackward (Lean_prop_0_of q Hq x Hx))).
Qed.

Theorem LeanIff_symm : forall p q :e LeanProp, forall h :e Lean_Iff_Prop p q,
  0 :e Lean_Iff_Prop q p.
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
let h. assume Hh: h :e Lean_Iff_Prop p q.
exact LeanIff_intro q Hq p Hp (LeanIff_backward p Hp q Hq h Hh) (LeanIff_forward p Hp q Hq h Hh).
Qed.

Theorem LeanAnd_left : forall p q :e LeanProp, forall h :e Lean_And_Prop p q, 0 :e p.
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
let h. assume Hh: h :e Lean_And_Prop p q.
claim HM: (fun x :e p => fun y :e q => x) :e (Pi_ x :e p, (Pi_ y :e q, p)).
{ exact lam_Pi p (fun _ => Pi_ y :e q, p) (fun x => fun y :e q => x)
    (fun x Hx => lam_Pi q (fun _ => p) (fun _ => x) (fun y Hy => Hx)). }
claim L: Lean_And_prec p q (fun x :e p => fun y :e q => x) h :e p.
{ exact Lean_And_prec_type p q (fun _ => p) (fun x :e p => fun y :e q => x) HM h Hh. }
exact Lean_prop_0_of p Hp (Lean_And_prec p q (fun x :e p => fun y :e q => x) h) L.
Qed.

Theorem LeanAnd_right : forall p q :e LeanProp, forall h :e Lean_And_Prop p q, 0 :e q.
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
let h. assume Hh: h :e Lean_And_Prop p q.
claim HM: (fun x :e p => fun y :e q => y) :e (Pi_ x :e p, (Pi_ y :e q, q)).
{ exact lam_Pi p (fun _ => Pi_ y :e q, q) (fun x => fun y :e q => y)
    (fun x Hx => lam_Pi q (fun _ => q) (fun y => y) (fun y Hy => Hy)). }
claim L: Lean_And_prec p q (fun x :e p => fun y :e q => y) h :e q.
{ exact Lean_And_prec_type p q (fun _ => q) (fun x :e p => fun y :e q => y) HM h Hh. }
exact Lean_prop_0_of q Hq (Lean_And_prec p q (fun x :e p => fun y :e q => y) h) L.
Qed.

Theorem LeanAnd_refute_left : forall p q :e LeanProp,
  forall h :e (Pi_ x :e p, Lean_False_Prop), 0 :e (Pi_ x :e Lean_And_Prop p q, Lean_False_Prop).
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
let h. assume Hh: h :e (Pi_ x :e p, Lean_False_Prop).
exact Lean_refute_by p Hp h Hh (Lean_And_Prop p q) (Lean_And_Prop_prop p q)
  (fun H => LeanAnd_left p Hp q Hq 0 H).
Qed.

Theorem LeanAnd_refute_right : forall p q :e LeanProp,
  forall h :e (Pi_ x :e q, Lean_False_Prop), 0 :e (Pi_ x :e Lean_And_Prop p q, Lean_False_Prop).
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp.
let h. assume Hh: h :e (Pi_ x :e q, Lean_False_Prop).
exact Lean_refute_by q Hq h Hh (Lean_And_Prop p q) (Lean_And_Prop_prop p q)
  (fun H => LeanAnd_right p Hp q Hq 0 H).
Qed.

Theorem LeanNot_double : forall p :e LeanProp, 0 :e p ->
  0 :e (Pi_ h :e (Pi_ x :e p, Lean_False_Prop), Lean_False_Prop).
let p. assume Hp: p :e LeanProp. assume H0: 0 :e p.
exact Lean_refute_0 (Pi_ x :e p, Lean_False_Prop)
  (LeanPi_prop p (fun _ => Lean_False_Prop) (fun x Hx => Lean_False_Prop_prop))
  (fun Hn => Lean_False_Prop_empty (0 0) (ap_Pi p (fun _ => Lean_False_Prop) 0 0 Hn H0)).
Qed.

Theorem LeanExists_intro : forall A p, forall x :e A, 0 :e p x -> 0 :e Lean_Exists_Prop A p.
let A p x. assume Hx: x :e A. assume Hp: 0 :e p x.
exact Lean_Exists_intro_proof_ok A p x Hx 0 (Lean_ProofField_intro (p x) Hp).
Qed.

Theorem LeanExists_elim : forall A p, forall Q:prop,
  (forall x :e A, 0 :e p x -> Q) -> 0 :e Lean_Exists_Prop A p -> Q.
let A p Q. assume H: forall x :e A, 0 :e p x -> Q. assume Hex: 0 :e Lean_Exists_Prop A p.
claim HM: 0 :e (Pi_ x :e A, (Pi_ h :e Lean_ProofField (p x), {z :e 1 | Q})).
{ apply Pi_0_In. let x. assume Hx: x :e A.
  prove 0 :e (Pi_ h :e Lean_ProofField (p x), {z :e 1 | Q}).
  apply Pi_0_In. let h. assume Hh: h :e Lean_ProofField (p x).
  prove 0 :e {z :e 1 | Q}.
  apply SepI 1 (fun z => Q) 0 In_0_1.
  exact H x Hx (Lean_ProofField_sound (p x) 0
    (Lean_prop_0_of (Lean_ProofField (p x)) (Lean_ProofField_prop (p x)) h Hh)). }
exact SepE2 1 (fun z => Q) (Lean_Exists_prec A p 0 0)
  (Lean_Exists_prec_type A p (fun _ => {z :e 1 | Q})
    (fun _ => Lean_sep1_prop Q) 0 HM 0 Hex).
Qed.

(** Propositional extensionality on truth values: equivalent propositions
    are the same subset of 1. **)
Theorem Lean_propext_value : forall p q :e LeanProp, 0 :e Lean_Iff_Prop p q -> p = q.
let p. assume Hp: p :e LeanProp. let q. assume Hq: q :e LeanProp. assume H: 0 :e Lean_Iff_Prop p q.
claim Hpq: 0 :e p -> 0 :e q. { exact LeanIff_forward p Hp q Hq 0 H. }
claim Hqp: 0 :e q -> 0 :e p. { exact LeanIff_backward p Hp q Hq 0 H. }
apply set_ext.
- let x. assume Hx: x :e p.
  claim Hx1: x :e 1. { exact PowerE 1 p Hp x Hx. }
  exact cases_1 x Hx1 (fun z => z :e p -> z :e q) Hpq Hx.
- let x. assume Hx: x :e q.
  claim Hx1: x :e 1. { exact PowerE 1 q Hq x Hx. }
  exact cases_1 x Hx1 (fun z => z :e q -> z :e p) Hqp Hx.
Qed.
