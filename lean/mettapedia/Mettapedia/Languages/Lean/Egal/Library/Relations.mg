(** Reflexive-transitive closure, for any carrier A and relation r: a set function
    from A to A to LeanProp, read from Lean's Relation.ReflTransGen.  The lemmas
    Lean's library proves about it (single, tail, head, trans) and two facts of
    deterministic relations (head inversion and uniqueness of final states),
    proved once through the family's induction principle. **)

Theorem Lean_RTG_refl : forall A r a, 0 :e Lean_Relation_ReflTransGen_Prop A r a a.
let A r a. exact Lean_Relation_ReflTransGen_refl_proof_ok A r a.
Qed.

(** A proof of a proposition is 0. **)
Theorem Lean_guard_of : forall p:set, 0 :e p -> 0 :e {z :e 1 | z :e p}.
let p. assume H: 0 :e p. exact SepI 1 (fun z => z :e p) 0 In_0_1 H.
Qed.
Theorem Lean_of_guard : forall p:set, forall x :e {z :e 1 | z :e p}, 0 :e p.
let p x. assume Hx: x :e {z :e 1 | z :e p}.
claim L: x = 0. { exact In_1_eq_0 x (SepE1 1 (fun z => z :e p) x Hx). }
rewrite <- L. exact SepE2 1 (fun z => z :e p) x Hx.
Qed.

Theorem Lean_RTG_tail : forall A r a, forall b :e A, forall c :e A,
  0 :e Lean_Relation_ReflTransGen_Prop A r a b -> 0 :e r b c -> 0 :e Lean_Relation_ReflTransGen_Prop A r a c.
let A r a b. assume Hb: b :e A. let c. assume Hc: c :e A.
assume Hab: 0 :e Lean_Relation_ReflTransGen_Prop A r a b. assume Hr: 0 :e r b c.
apply SepE2 1 (fun x => exists w, w :e Lean_Relation_ReflTransGen A r a b) 0 Hab.
let w. assume Hw: w :e Lean_Relation_ReflTransGen A r a b.
exact Lean_Relation_ReflTransGen_tail_proof_ok A r a b Hb c Hc w Hw 0 (Lean_guard_of (r b c) Hr).
Qed.

Theorem Lean_RTG_single : forall A r, forall a :e A, forall b :e A, 0 :e r a b -> 0 :e Lean_Relation_ReflTransGen_Prop A r a b.
let A r a. assume Ha: a :e A. let b. assume Hb: b :e A. assume Hr: 0 :e r a b.
exact Lean_RTG_tail A r a a Ha b Hb (Lean_RTG_refl A r a) Hr.
Qed.

(** A proposition of the form {z :e 1 | P} lies in LeanProp. **)

Theorem Lean_RTG_trans : forall A r a b c,
  0 :e Lean_Relation_ReflTransGen_Prop A r a b -> 0 :e Lean_Relation_ReflTransGen_Prop A r b c ->
  0 :e Lean_Relation_ReflTransGen_Prop A r a c.
let A r a b c. assume Hab: 0 :e Lean_Relation_ReflTransGen_Prop A r a b.
assume Hbc: 0 :e Lean_Relation_ReflTransGen_Prop A r b c.
claim HC: forall i t, {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a i} :e LeanProp.
{ let i t. exact Lean_sep1_prop (0 :e Lean_Relation_ReflTransGen_Prop A r a i). }
claim H0: 0 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a b}.
{ exact SepI 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r a b) 0 In_0_1 Hab. }
claim H1: 0 :e (Pi_ x0 :e A, (Pi_ x1 :e A, (Pi_ x2 :e (Lean_Relation_ReflTransGen A r b x0),
  (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)}, (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x0},
  {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x1}))))).
{ apply Pi_0_In. let x0. assume Hx0: x0 :e A.
  prove 0 :e (Pi_ x1 :e A, (Pi_ x2 :e (Lean_Relation_ReflTransGen A r b x0),
    (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)}, (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x0},
    {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x1})))).
  apply Pi_0_In. let x1. assume Hx1: x1 :e A.
  prove 0 :e (Pi_ x2 :e (Lean_Relation_ReflTransGen A r b x0),
    (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)}, (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x0},
    {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x1}))).
  apply Pi_0_In. let x2. assume Hx2.
  prove 0 :e (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)}, (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x0},
    {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x1})).
  apply Pi_0_In. let x3. assume Hx3: x3 :e {z :e 1 | z :e ((r x0) x1)}.
  prove 0 :e (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x0}, {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x1}).
  apply Pi_0_In. let y2. assume Hy2: y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x0}.
  prove 0 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a x1}.
  apply SepI 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r a x1) 0 In_0_1.
  exact Lean_RTG_tail A r a x0 Hx0 x1 Hx1 (SepE2 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r a x0) y2 Hy2)
    (Lean_of_guard (r x0 x1) x3 Hx3). }
claim L: Lean_Relation_ReflTransGen_prec A r b 0 0 c 0 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a c}.
{ exact Lean_Relation_ReflTransGen_prec_type A r b (fun i t => {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a i}) HC
    0 H0 0 H1 c 0 Hbc. }
exact SepE2 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r a c) (Lean_Relation_ReflTransGen_prec A r b 0 0 c 0) L.
Qed.

Theorem Lean_RTG_head : forall A r, forall a :e A, forall b :e A, forall c,
  0 :e r a b -> 0 :e Lean_Relation_ReflTransGen_Prop A r b c -> 0 :e Lean_Relation_ReflTransGen_Prop A r a c.
let A r a. assume Ha: a :e A. let b. assume Hb: b :e A. let c. assume Hr: 0 :e r a b.
assume Hbc: 0 :e Lean_Relation_ReflTransGen_Prop A r b c.
exact Lean_RTG_trans A r a b c (Lean_RTG_single A r a Ha b Hb Hr) Hbc.
Qed.

(** Every path from a is empty, or begins with a step from a. **)
Theorem Lean_RTG_head_inv : forall A r a, forall c,
  0 :e Lean_Relation_ReflTransGen_Prop A r a c ->
  a = c \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x c.
let A r a c. assume Hac: 0 :e Lean_Relation_ReflTransGen_Prop A r a c.
claim HC: forall i t, {z :e 1 | a = i \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x i} :e LeanProp.
{ let i t. exact Lean_sep1_prop (a = i \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x i). }
claim H0: 0 :e {z :e 1 | a = a \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x a}.
{ apply SepI 1 (fun z => a = a \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x a) 0 In_0_1.
  apply orIL. reflexivity. }
claim H1: 0 :e (Pi_ x0 :e A, (Pi_ x1 :e A, (Pi_ x2 :e (Lean_Relation_ReflTransGen A r a x0),
  (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
  (Pi_ y2 :e {z :e 1 | a = x0 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0},
  {z :e 1 | a = x1 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x1}))))).
{ apply Pi_0_In. let x0. assume Hx0: x0 :e A.
  prove 0 :e (Pi_ x1 :e A, (Pi_ x2 :e (Lean_Relation_ReflTransGen A r a x0), (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | a = x0 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0},
    {z :e 1 | a = x1 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x1})))).
  apply Pi_0_In. let x1. assume Hx1: x1 :e A.
  prove 0 :e (Pi_ x2 :e (Lean_Relation_ReflTransGen A r a x0), (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | a = x0 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0},
    {z :e 1 | a = x1 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x1}))).
  apply Pi_0_In. let x2. assume Hx2.
  prove 0 :e (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | a = x0 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0},
    {z :e 1 | a = x1 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x1})).
  apply Pi_0_In. let x3. assume Hx3: x3 :e {z :e 1 | z :e ((r x0) x1)}.
  prove 0 :e (Pi_ y2 :e {z :e 1 | a = x0 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0},
    {z :e 1 | a = x1 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x1}).
  apply Pi_0_In. let y2. assume Hy2: y2 :e {z :e 1 | a = x0 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0}.
  prove 0 :e {z :e 1 | a = x1 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x1}.
  apply SepI 1 (fun z => a = x1 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x1) 0 In_0_1.
  claim Lr: 0 :e r x0 x1. { exact Lean_of_guard (r x0 x1) x3 Hx3. }
  apply SepE2 1 (fun z => a = x0 \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0) y2 Hy2.
  - assume Ha0: a = x0. apply orIR. witness x1. apply andI.
    + exact Hx1.
    + apply andI.
      * rewrite Ha0. exact Lr.
      * exact Lean_RTG_refl A r x1.
  - assume Hex: exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0.
    apply Hex. let x. assume Hx: x :e A /\ (0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x x0).
    apply Hx. assume HxA: x :e A. assume Hxr.
    apply Hxr. assume Hrax: 0 :e r a x. assume Hxx0: 0 :e Lean_Relation_ReflTransGen_Prop A r x x0.
    apply orIR. witness x. apply andI.
    + exact HxA.
    + apply andI.
      * exact Hrax.
      * exact Lean_RTG_tail A r x x0 Hx0 x1 Hx1 Hxx0 Lr. }
claim L: Lean_Relation_ReflTransGen_prec A r a 0 0 c 0
  :e {z :e 1 | a = c \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x c}.
{ exact Lean_Relation_ReflTransGen_prec_type A r a
    (fun i t => {z :e 1 | a = i \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x i}) HC
    0 H0 0 H1 c 0 Hac. }
exact SepE2 1 (fun z => a = c \/ exists x :e A, 0 :e r a x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x c)
  (Lean_Relation_ReflTransGen_prec A r a 0 0 c 0) L.
Qed.

(** A deterministic relation reaches at most one final state from any start. **)
Theorem Lean_RTG_final_unique : forall A r,
  (forall x :e A, forall y :e A, forall z :e A, 0 :e r x y -> 0 :e r x z -> y = z) ->
  forall s :e A, forall f1 :e A, forall f2 :e A,
  0 :e Lean_Relation_ReflTransGen_Prop A r s f1 -> 0 :e Lean_Relation_ReflTransGen_Prop A r s f2 ->
  (forall y :e A, 0 /:e r f1 y) -> (forall y :e A, 0 /:e r f2 y) -> f1 = f2.
let A r. assume Hdet: forall x :e A, forall y :e A, forall z :e A, 0 :e r x y -> 0 :e r x z -> y = z.
let s. assume Hs: s :e A. let f1. assume Hf1: f1 :e A. let f2. assume Hf2: f2 :e A.
assume H1: 0 :e Lean_Relation_ReflTransGen_Prop A r s f1. assume H2: 0 :e Lean_Relation_ReflTransGen_Prop A r s f2.
assume Hfin1: forall y :e A, 0 /:e r f1 y. assume Hfin2: forall y :e A, 0 /:e r f2 y.
claim HC: forall i t, {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r i f1} :e LeanProp.
{ let i t. exact Lean_sep1_prop (0 :e Lean_Relation_ReflTransGen_Prop A r i f1). }
claim H0: 0 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r s f1}.
{ exact SepI 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r s f1) 0 In_0_1 H1. }
claim HS: 0 :e (Pi_ x0 :e A, (Pi_ x1 :e A, (Pi_ x2 :e (Lean_Relation_ReflTransGen A r s x0),
  (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)}, (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 f1},
  {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 f1}))))).
{ apply Pi_0_In. let x0. assume Hx0: x0 :e A.
  prove 0 :e (Pi_ x1 :e A, (Pi_ x2 :e (Lean_Relation_ReflTransGen A r s x0), (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 f1}, {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 f1})))).
  apply Pi_0_In. let x1. assume Hx1: x1 :e A.
  prove 0 :e (Pi_ x2 :e (Lean_Relation_ReflTransGen A r s x0), (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 f1}, {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 f1}))).
  apply Pi_0_In. let x2. assume Hx2.
  prove 0 :e (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 f1}, {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 f1})).
  apply Pi_0_In. let x3. assume Hx3: x3 :e {z :e 1 | z :e ((r x0) x1)}.
  prove 0 :e (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 f1}, {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 f1}).
  apply Pi_0_In. let y2. assume Hy2: y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 f1}.
  prove 0 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 f1}.
  apply SepI 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r x1 f1) 0 In_0_1.
  claim Lr: 0 :e r x0 x1. { exact Lean_of_guard (r x0 x1) x3 Hx3. }
  apply Lean_RTG_head_inv A r x0 f1 (SepE2 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r x0 f1) y2 Hy2).
  - assume He: x0 = f1. apply FalseE. apply Hfin1 x1 Hx1. rewrite <- He. exact Lr.
  - assume Hex: exists x :e A, 0 :e r x0 x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x f1.
    apply Hex. let x. assume Hx: x :e A /\ (0 :e r x0 x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x f1).
    apply Hx. assume HxA: x :e A. assume Hxr.
    apply Hxr. assume Hrx: 0 :e r x0 x. assume Hxf: 0 :e Lean_Relation_ReflTransGen_Prop A r x f1.
    claim Le: x1 = x. { exact Hdet x0 Hx0 x1 Hx1 x HxA Lr Hrx. }
    rewrite Le. exact Hxf. }
claim L: Lean_Relation_ReflTransGen_prec A r s 0 0 f2 0 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r f2 f1}.
{ exact Lean_Relation_ReflTransGen_prec_type A r s (fun i t => {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r i f1}) HC
    0 H0 0 HS f2 0 H2. }
claim L21: 0 :e Lean_Relation_ReflTransGen_Prop A r f2 f1.
{ exact SepE2 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r f2 f1) (Lean_Relation_ReflTransGen_prec A r s 0 0 f2 0) L. }
apply Lean_RTG_head_inv A r f2 f1 L21.
- assume He: f2 = f1. exact eq_sym_i f2 f1 He.
- assume Hex: exists x :e A, 0 :e r f2 x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x f1.
  apply Hex. let x. assume Hx: x :e A /\ (0 :e r f2 x /\ 0 :e Lean_Relation_ReflTransGen_Prop A r x f1).
  apply Hx. assume HxA: x :e A. assume Hxr.
  apply Hxr. assume Hrx: 0 :e r f2 x. assume Hxf.
  apply FalseE. exact Hfin2 x HxA Hrx.
Qed.

(** Head induction: a property that holds at b, and passes from y to x along
    a step x -> y whenever y reaches b, holds at every x that reaches b.  By
    induction on the run from a, generalized over its end. **)
Theorem Lean_RTG_head_ind : forall A r b, forall P:set -> prop,
  P b ->
  (forall x :e A, forall y :e A, 0 :e r x y -> 0 :e Lean_Relation_ReflTransGen_Prop A r y b -> P y -> P x) ->
  forall a :e A, 0 :e Lean_Relation_ReflTransGen_Prop A r a b -> P a.
let A r b P. assume Pb. assume Step. let a. assume Ha: a :e A.
assume Hab: 0 :e Lean_Relation_ReflTransGen_Prop A r a b.
claim HC: forall i t, {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r i b -> P i -> P a} :e LeanProp.
{ let i t. exact Lean_sep1_prop (0 :e Lean_Relation_ReflTransGen_Prop A r i b -> P i -> P a). }
claim H0: 0 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r a b -> P a -> P a}.
{ apply SepI 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r a b -> P a -> P a) 0 In_0_1.
  assume H1. assume H2. exact H2. }
claim H1: 0 :e (Pi_ x0 :e A, (Pi_ x1 :e A, (Pi_ x2 :e (Lean_Relation_ReflTransGen A r a x0),
  (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
  (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 b -> P x0 -> P a},
  {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 b -> P x1 -> P a}))))).
{ apply Pi_0_In. let x0. assume Hx0: x0 :e A.
  prove 0 :e (Pi_ x1 :e A, (Pi_ x2 :e (Lean_Relation_ReflTransGen A r a x0),
    (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 b -> P x0 -> P a},
    {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 b -> P x1 -> P a})))).
  apply Pi_0_In. let x1. assume Hx1: x1 :e A.
  prove 0 :e (Pi_ x2 :e (Lean_Relation_ReflTransGen A r a x0),
    (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 b -> P x0 -> P a},
    {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 b -> P x1 -> P a}))).
  apply Pi_0_In. let x2. assume Hx2.
  prove 0 :e (Pi_ x3 :e {z :e 1 | z :e ((r x0) x1)},
    (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 b -> P x0 -> P a},
    {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 b -> P x1 -> P a})).
  apply Pi_0_In. let x3. assume Hx3: x3 :e {z :e 1 | z :e ((r x0) x1)}.
  prove 0 :e (Pi_ y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 b -> P x0 -> P a},
    {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 b -> P x1 -> P a}).
  apply Pi_0_In. let y2. assume Hy2: y2 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x0 b -> P x0 -> P a}.
  prove 0 :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r x1 b -> P x1 -> P a}.
  apply SepI 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r x1 b -> P x1 -> P a) 0 In_0_1.
  assume H1b: 0 :e Lean_Relation_ReflTransGen_Prop A r x1 b. assume P1: P x1.
  claim Rx: 0 :e r x0 x1.
  { exact Lean_of_guard (r x0 x1) x3 Hx3. }
  claim IH: 0 :e Lean_Relation_ReflTransGen_Prop A r x0 b -> P x0 -> P a.
  { exact SepE2 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r x0 b -> P x0 -> P a) y2 Hy2. }
  apply IH.
  - exact Lean_RTG_head A r x0 Hx0 x1 Hx1 b Rx H1b.
  - exact Step x0 Hx0 x1 Hx1 Rx H1b P1. }
claim L: Lean_Relation_ReflTransGen_prec A r a 0 0 b 0
  :e {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r b b -> P b -> P a}.
{ exact Lean_Relation_ReflTransGen_prec_type A r a
    (fun i t => {z :e 1 | 0 :e Lean_Relation_ReflTransGen_Prop A r i b -> P i -> P a}) HC 0 H0 0 H1 b 0 Hab. }
exact SepE2 1 (fun z => 0 :e Lean_Relation_ReflTransGen_Prop A r b b -> P b -> P a)
  (Lean_Relation_ReflTransGen_prec A r a 0 0 b 0) L (Lean_RTG_refl A r b) Pb.
Qed.
