(** Membership and pairwise relations of Lean lists, and their invariance
    under permutation.

    List.Mem and List.Pairwise are the generated readings of Lean's inductive
    propositions.  Their truth values are restated as Egal propositions, with
    the introduction and inversion laws of the constructors, and a pairwise
    symmetric relation is shown to hold of every permutation of a list it
    holds of.  For the relation "different" that is List.Perm.nodup_iff. **)

Definition LeanListMem : set -> set -> set -> prop :=
  fun A a xs => 0 :e Lean_List_Mem_Prop A a xs.

Theorem LeanListMem_intro : forall A a xs w, w :e Lean_List_Mem A a xs -> LeanListMem A a xs.
let A a xs w. assume Hw: w :e Lean_List_Mem A a xs.
exact SepI 1 (fun _ => exists w, w :e Lean_List_Mem A a xs) 0 In_0_1 (fun P H => H w Hw).
Qed.

Theorem LeanListMem_elim : forall A a xs, LeanListMem A a xs ->
  forall p:prop, (forall w, w :e Lean_List_Mem A a xs -> p) -> p.
let A a xs. assume H: LeanListMem A a xs.
exact SepE2 1 (fun _ => exists w, w :e Lean_List_Mem A a xs) 0 H.
Qed.

Theorem LeanListMem_head : forall A a, forall xs :e Lean_List A,
  LeanListMem A a (Lean_List_cons_node A a xs).
let A a xs. assume Hxs: xs :e Lean_List A.
exact LeanListMem_intro A a (Lean_List_cons_node A a xs) (Lean_List_Mem_head_node A a xs)
  (Lean_List_Mem_head_typed A a xs Hxs).
Qed.

Theorem LeanListMem_tail : forall A a, forall b :e A, forall xs :e Lean_List A,
  LeanListMem A a xs -> LeanListMem A a (Lean_List_cons_node A b xs).
let A a b. assume Hb: b :e A. let xs. assume Hxs: xs :e Lean_List A. assume H: LeanListMem A a xs.
apply LeanListMem_elim A a xs H.
let w. assume Hw: w :e Lean_List_Mem A a xs.
exact LeanListMem_intro A a (Lean_List_cons_node A b xs) (Lean_List_Mem_tail_node A a b xs w)
  (Lean_List_Mem_tail_typed A a b Hb xs Hxs w Hw).
Qed.

Theorem LeanListMem_cons_inv : forall A a b xs, LeanListMem A a (Lean_List_cons_node A b xs) ->
  a = b \/ LeanListMem A a xs.
let A a b xs. assume H: LeanListMem A a (Lean_List_cons_node A b xs).
apply LeanListMem_elim A a (Lean_List_cons_node A b xs) H.
let w. assume Hw: w :e Lean_List_Mem A a (Lean_List_cons_node A b xs).
claim Hhead: forall x0 :e Lean_List A, forall c ys,
  Lean_List_cons_node A a x0 = Lean_List_cons_node A c ys -> a = c \/ LeanListMem A a ys.
{ let x0. assume Hx0: x0 :e Lean_List A. let c ys.
  assume Heq: Lean_List_cons_node A a x0 = Lean_List_cons_node A c ys.
  apply orIL. exact Lean_List_cons_inj0 A a x0 c ys Heq. }
claim Htail: forall x0 :e A, forall x1 :e Lean_List A, forall x2 :e Lean_List_Mem A a x1,
  (forall c ys, x1 = Lean_List_cons_node A c ys -> a = c \/ LeanListMem A a ys) ->
  forall c ys, Lean_List_cons_node A x0 x1 = Lean_List_cons_node A c ys -> a = c \/ LeanListMem A a ys.
{ let x0. assume Hx0: x0 :e A. let x1. assume Hx1: x1 :e Lean_List A.
  let x2. assume Hx2: x2 :e Lean_List_Mem A a x1.
  assume IH: forall c ys, x1 = Lean_List_cons_node A c ys -> a = c \/ LeanListMem A a ys.
  let c ys. assume Heq: Lean_List_cons_node A x0 x1 = Lean_List_cons_node A c ys.
  apply orIR. rewrite <- Lean_List_cons_inj1 A x0 x1 c ys Heq.
  exact LeanListMem_intro A a x1 x2 Hx2. }
exact Lean_List_Mem_ind A a
  (fun i t => forall c ys, i = Lean_List_cons_node A c ys -> a = c \/ LeanListMem A a ys)
  Hhead Htail (Lean_List_cons_node A b xs) w Hw b xs (Lean_eq_refl (Lean_List_cons_node A b xs)).
Qed.

Theorem LeanListMem_nil : forall A a, ~ LeanListMem A a (Lean_List_nil_node A).
let A a. assume H: LeanListMem A a (Lean_List_nil_node A).
apply LeanListMem_elim A a (Lean_List_nil_node A) H.
let w. assume Hw: w :e Lean_List_Mem A a (Lean_List_nil_node A).
claim Hhead: forall x0 :e Lean_List A, Lean_List_cons_node A a x0 <> Lean_List_nil_node A.
{ let x0. assume Hx0: x0 :e Lean_List A. assume Heq: Lean_List_cons_node A a x0 = Lean_List_nil_node A.
  exact Lean_List_noconf0_1 A a x0 (eq_sym_i (Lean_List_cons_node A a x0) (Lean_List_nil_node A) Heq). }
claim Htail: forall x0 :e A, forall x1 :e Lean_List A, forall x2 :e Lean_List_Mem A a x1,
  x1 <> Lean_List_nil_node A -> Lean_List_cons_node A x0 x1 <> Lean_List_nil_node A.
{ let x0. assume Hx0: x0 :e A. let x1. assume Hx1: x1 :e Lean_List A.
  let x2. assume Hx2: x2 :e Lean_List_Mem A a x1. assume IH: x1 <> Lean_List_nil_node A.
  assume Heq: Lean_List_cons_node A x0 x1 = Lean_List_nil_node A.
  exact Lean_List_noconf0_1 A x0 x1 (eq_sym_i (Lean_List_cons_node A x0 x1) (Lean_List_nil_node A) Heq). }
exact Lean_List_Mem_ind A a (fun i t => i <> Lean_List_nil_node A) Hhead Htail
  (Lean_List_nil_node A) w Hw (Lean_eq_refl (Lean_List_nil_node A)).
Qed.

Definition LeanListPairwise : set -> set -> set -> prop :=
  fun A R xs => 0 :e Lean_List_Pairwise_Prop A R xs.

Theorem LeanListPairwise_intro : forall A R xs w, w :e Lean_List_Pairwise A R xs -> LeanListPairwise A R xs.
let A R xs w. assume Hw: w :e Lean_List_Pairwise A R xs.
exact SepI 1 (fun _ => exists w, w :e Lean_List_Pairwise A R xs) 0 In_0_1 (fun P H => H w Hw).
Qed.

Theorem LeanListPairwise_elim : forall A R xs, LeanListPairwise A R xs ->
  forall p:prop, (forall w, w :e Lean_List_Pairwise A R xs -> p) -> p.
let A R xs. assume H: LeanListPairwise A R xs.
exact SepE2 1 (fun _ => exists w, w :e Lean_List_Pairwise A R xs) 0 H.
Qed.

Theorem LeanListPairwise_nil : forall A R, LeanListPairwise A R (Lean_List_nil_node A).
let A R.
exact LeanListPairwise_intro A R (Lean_List_nil_node A) (Lean_List_Pairwise_nil_node A R)
  (Lean_List_Pairwise_nil_typed A R).
Qed.

Theorem LeanListPairwise_cons : forall A R, forall x :e A, forall xs :e Lean_List A,
  (forall b :e A, LeanListMem A b xs -> 0 :e R x b) -> LeanListPairwise A R xs ->
  LeanListPairwise A R (Lean_List_cons_node A x xs).
let A R x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
assume Hall: forall b :e A, LeanListMem A b xs -> 0 :e R x b.
assume Hpw: LeanListPairwise A R xs.
apply LeanListPairwise_elim A R xs Hpw.
let w. assume Hw: w :e Lean_List_Pairwise A R xs.
claim Hproduct: 0 :e (Pi_ q0 :e A, (Pi_ q1 :e (Lean_List_Mem_Prop A q0 xs), (R x q0))).
{ exact Pi_0_In A (fun q0 => Pi_ q1 :e (Lean_List_Mem_Prop A q0 xs), R x q0)
    (fun q0 Hq0 => Pi_0_In (Lean_List_Mem_Prop A q0 xs) (fun _ => R x q0)
      (fun q1 Hq1 => Hall q0 Hq0
        (Lean_prop_0_of (Lean_List_Mem_Prop A q0 xs) (Lean_List_Mem_Prop_prop A q0 xs) q1 Hq1))). }
claim Hguard: 0 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e (Lean_List_Mem_Prop A q0 xs), (R x q0)))}.
{ exact SepI 1 (fun z => z :e (Pi_ q0 :e A, (Pi_ q1 :e (Lean_List_Mem_Prop A q0 xs), (R x q0)))) 0 In_0_1 Hproduct. }
exact LeanListPairwise_intro A R (Lean_List_cons_node A x xs) (Lean_List_Pairwise_cons_node A R x xs 0 w)
  (Lean_List_Pairwise_cons_typed A R x Hx xs Hxs 0 Hguard w Hw).
Qed.

Theorem LeanListPairwise_cons_inv : forall A, forall R :e (Pi_ a :e A, Pi_ b :e A, LeanProp),
  forall x :e A, forall xs, LeanListPairwise A R (Lean_List_cons_node A x xs) ->
  (forall b :e A, LeanListMem A b xs -> 0 :e R x b) /\ LeanListPairwise A R xs.
let A R. assume HR: R :e (Pi_ a :e A, Pi_ b :e A, LeanProp).
claim HRprop: forall a :e A, forall b :e A, R a b :e LeanProp.
{ let a. assume Ha: a :e A. let b. assume Hb: b :e A.
  exact ap_Pi A (fun _ => LeanProp) (R a) b (ap_Pi A (fun a => Pi_ b :e A, LeanProp) R a HR Ha) Hb. }
claim Hnil: forall c :e A, forall ys, Lean_List_nil_node A = Lean_List_cons_node A c ys ->
  (forall b :e A, LeanListMem A b ys -> 0 :e R c b) /\ LeanListPairwise A R ys.
{ let c. assume Hc: c :e A. let ys. assume Heq: Lean_List_nil_node A = Lean_List_cons_node A c ys.
  exact FalseE (Lean_List_noconf0_1 A c ys Heq)
    ((forall b :e A, LeanListMem A b ys -> 0 :e R c b) /\ LeanListPairwise A R ys). }
claim Hcons: forall x0 :e A, forall x1 :e Lean_List A,
  forall x2 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e (Lean_List_Mem_Prop A q0 x1), (R x0 q0)))},
  forall x3 :e Lean_List_Pairwise A R x1,
  (forall c :e A, forall ys, x1 = Lean_List_cons_node A c ys ->
    (forall b :e A, LeanListMem A b ys -> 0 :e R c b) /\ LeanListPairwise A R ys) ->
  forall c :e A, forall ys, Lean_List_cons_node A x0 x1 = Lean_List_cons_node A c ys ->
    (forall b :e A, LeanListMem A b ys -> 0 :e R c b) /\ LeanListPairwise A R ys.
{ let x0. assume Hx0: x0 :e A. let x1. assume Hx1: x1 :e Lean_List A.
  let x2. assume Hx2: x2 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e (Lean_List_Mem_Prop A q0 x1), (R x0 q0)))}.
  let x3. assume Hx3: x3 :e Lean_List_Pairwise A R x1.
  assume IH: forall c :e A, forall ys, x1 = Lean_List_cons_node A c ys ->
    (forall b :e A, LeanListMem A b ys -> 0 :e R c b) /\ LeanListPairwise A R ys.
  let c. assume Hc: c :e A. let ys. assume Heq: Lean_List_cons_node A x0 x1 = Lean_List_cons_node A c ys.
  rewrite <- Lean_List_cons_inj0 A x0 x1 c ys Heq. rewrite <- Lean_List_cons_inj1 A x0 x1 c ys Heq.
  apply andI.
  - let b. assume Hb: b :e A. assume Hmem: LeanListMem A b x1.
    claim Hx2p: x2 :e (Pi_ q0 :e A, (Pi_ q1 :e (Lean_List_Mem_Prop A q0 x1), (R x0 q0))).
    { exact SepE2 1 (fun z => z :e (Pi_ q0 :e A, (Pi_ q1 :e (Lean_List_Mem_Prop A q0 x1), (R x0 q0)))) x2 Hx2. }
    claim Hx2b: x2 b :e (Pi_ q1 :e (Lean_List_Mem_Prop A b x1), (R x0 b)).
    { exact ap_Pi A (fun q0 => Pi_ q1 :e (Lean_List_Mem_Prop A q0 x1), (R x0 q0)) x2 b Hx2p Hb. }
    claim Hx2b0: (x2 b) 0 :e R x0 b.
    { exact ap_Pi (Lean_List_Mem_Prop A b x1) (fun _ => R x0 b) (x2 b) 0 Hx2b Hmem. }
    exact Lean_prop_0_of (R x0 b) (HRprop x0 Hx0 b Hb) ((x2 b) 0) Hx2b0.
  - exact LeanListPairwise_intro A R x1 x3 Hx3. }
let x. assume Hx: x :e A. let xs. assume H: LeanListPairwise A R (Lean_List_cons_node A x xs).
apply LeanListPairwise_elim A R (Lean_List_cons_node A x xs) H.
let w. assume Hw: w :e Lean_List_Pairwise A R (Lean_List_cons_node A x xs).
exact Lean_List_Pairwise_ind A R
  (fun i t => forall c :e A, forall ys, i = Lean_List_cons_node A c ys ->
    (forall b :e A, LeanListMem A b ys -> 0 :e R c b) /\ LeanListPairwise A R ys)
  Hnil Hcons (Lean_List_cons_node A x xs) w Hw x Hx xs (Lean_eq_refl (Lean_List_cons_node A x xs)).
Qed.

(** Permuted lists have the same members. **)
Theorem LeanListPerm_mem : forall A xs ys, LeanListPerm A xs ys ->
  forall b, LeanListMem A b xs -> LeanListMem A b ys.
let A.
claim Hnil: forall b, LeanListMem A b (Lean_List_nil_node A) -> LeanListMem A b (Lean_List_nil_node A).
{ let b. assume H: LeanListMem A b (Lean_List_nil_node A). exact H. }
claim Hcons: forall x :e A, forall xs ys :e Lean_List A,
  (forall b, LeanListMem A b xs -> LeanListMem A b ys) ->
  forall b, LeanListMem A b (Lean_List_cons_node A x xs) -> LeanListMem A b (Lean_List_cons_node A x ys).
{ let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
  assume IH: forall b, LeanListMem A b xs -> LeanListMem A b ys.
  let b. assume H: LeanListMem A b (Lean_List_cons_node A x xs).
  apply LeanListMem_cons_inv A b x xs H.
  - assume Hbx: b = x. rewrite Hbx. exact LeanListMem_head A x ys Hys.
  - assume Hm: LeanListMem A b xs. exact LeanListMem_tail A b x Hx ys Hys (IH b Hm). }
claim Hswap: forall x y :e A, forall xs :e Lean_List A,
  forall b, LeanListMem A b (Lean_List_cons_node A y (Lean_List_cons_node A x xs)) ->
    LeanListMem A b (Lean_List_cons_node A x (Lean_List_cons_node A y xs)).
{ let x. assume Hx: x :e A. let y. assume Hy: y :e A. let xs. assume Hxs: xs :e Lean_List A.
  claim Hyxs: Lean_List_cons_node A y xs :e Lean_List A. { exact Lean_List_cons_typed A y Hy xs Hxs. }
  let b. assume H: LeanListMem A b (Lean_List_cons_node A y (Lean_List_cons_node A x xs)).
  apply LeanListMem_cons_inv A b y (Lean_List_cons_node A x xs) H.
  - assume Hby: b = y. rewrite Hby.
    exact LeanListMem_tail A y x Hx (Lean_List_cons_node A y xs) Hyxs (LeanListMem_head A y xs Hxs).
  - assume Hm: LeanListMem A b (Lean_List_cons_node A x xs).
    apply LeanListMem_cons_inv A b x xs Hm.
    + assume Hbx: b = x. rewrite Hbx. exact LeanListMem_head A x (Lean_List_cons_node A y xs) Hyxs.
    + assume Hm2: LeanListMem A b xs.
      exact LeanListMem_tail A b x Hx (Lean_List_cons_node A y xs) Hyxs (LeanListMem_tail A b y Hy xs Hxs Hm2). }
claim Htrans: forall xs ys zs :e Lean_List A,
  (forall b, LeanListMem A b xs -> LeanListMem A b ys) ->
  (forall b, LeanListMem A b ys -> LeanListMem A b zs) ->
  forall b, LeanListMem A b xs -> LeanListMem A b zs.
{ let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A. let zs. assume Hzs: zs :e Lean_List A.
  assume H1: forall b, LeanListMem A b xs -> LeanListMem A b ys.
  assume H2: forall b, LeanListMem A b ys -> LeanListMem A b zs.
  let b. assume H: LeanListMem A b xs. exact H2 b (H1 b H). }
exact LeanListPerm_ind A (fun xs ys => forall b, LeanListMem A b xs -> LeanListMem A b ys)
  Hnil Hcons Hswap Htrans.
Qed.

(** A symmetric relation that holds pairwise of a list holds pairwise of its
    permutations. **)
Theorem LeanListPerm_pairwise : forall A, forall R :e (Pi_ a :e A, Pi_ b :e A, LeanProp),
  (forall a b :e A, 0 :e R a b -> 0 :e R b a) ->
  forall xs ys, LeanListPerm A xs ys -> LeanListPairwise A R xs -> LeanListPairwise A R ys.
let A R. assume HR: R :e (Pi_ a :e A, Pi_ b :e A, LeanProp).
assume Hsym: forall a b :e A, 0 :e R a b -> 0 :e R b a.
claim Hnil: LeanListPerm A (Lean_List_nil_node A) (Lean_List_nil_node A) /\
  (LeanListPairwise A R (Lean_List_nil_node A) -> LeanListPairwise A R (Lean_List_nil_node A)).
{ apply andI.
  - exact LeanListPerm_nil A.
  - assume H: LeanListPairwise A R (Lean_List_nil_node A). exact H. }
claim Hcons: forall x :e A, forall xs ys :e Lean_List A,
  LeanListPerm A ys xs /\ (LeanListPairwise A R xs -> LeanListPairwise A R ys) ->
  LeanListPerm A (Lean_List_cons_node A x ys) (Lean_List_cons_node A x xs) /\
  (LeanListPairwise A R (Lean_List_cons_node A x xs) -> LeanListPairwise A R (Lean_List_cons_node A x ys)).
{ let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
  assume IH: LeanListPerm A ys xs /\ (LeanListPairwise A R xs -> LeanListPairwise A R ys).
  apply IH. assume Hperm: LeanListPerm A ys xs.
  assume Himp: LeanListPairwise A R xs -> LeanListPairwise A R ys.
  apply andI.
  - exact LeanListPerm_cons A x Hx ys Hys xs Hxs Hperm.
  - assume Hpw: LeanListPairwise A R (Lean_List_cons_node A x xs).
    apply LeanListPairwise_cons_inv A R HR x Hx xs Hpw.
    assume Hall: forall b :e A, LeanListMem A b xs -> 0 :e R x b.
    assume Hrest: LeanListPairwise A R xs.
    exact LeanListPairwise_cons A R x Hx ys Hys
      (fun b Hb Hmem => Hall b Hb (LeanListPerm_mem A ys xs Hperm b Hmem)) (Himp Hrest). }
claim Hswap: forall x y :e A, forall xs :e Lean_List A,
  LeanListPerm A (Lean_List_cons_node A x (Lean_List_cons_node A y xs))
    (Lean_List_cons_node A y (Lean_List_cons_node A x xs)) /\
  (LeanListPairwise A R (Lean_List_cons_node A y (Lean_List_cons_node A x xs)) ->
   LeanListPairwise A R (Lean_List_cons_node A x (Lean_List_cons_node A y xs))).
{ let x. assume Hx: x :e A. let y. assume Hy: y :e A. let xs. assume Hxs: xs :e Lean_List A.
  claim Hxxs: Lean_List_cons_node A x xs :e Lean_List A. { exact Lean_List_cons_typed A x Hx xs Hxs. }
  claim Hyxs: Lean_List_cons_node A y xs :e Lean_List A. { exact Lean_List_cons_typed A y Hy xs Hxs. }
  apply andI.
  - exact LeanListPerm_swap A y Hy x Hx xs Hxs.
  - assume Hpw: LeanListPairwise A R (Lean_List_cons_node A y (Lean_List_cons_node A x xs)).
    apply LeanListPairwise_cons_inv A R HR y Hy (Lean_List_cons_node A x xs) Hpw.
    assume Hall1: forall b :e A, LeanListMem A b (Lean_List_cons_node A x xs) -> 0 :e R y b.
    assume Hrest1: LeanListPairwise A R (Lean_List_cons_node A x xs).
    apply LeanListPairwise_cons_inv A R HR x Hx xs Hrest1.
    assume Hall2: forall b :e A, LeanListMem A b xs -> 0 :e R x b.
    assume Hrest2: LeanListPairwise A R xs.
    claim Hxall: forall b :e A, LeanListMem A b (Lean_List_cons_node A y xs) -> 0 :e R x b.
    { let b. assume Hb: b :e A. assume Hm: LeanListMem A b (Lean_List_cons_node A y xs).
      apply LeanListMem_cons_inv A b y xs Hm.
      - assume Hby: b = y. rewrite Hby.
        exact Hsym y Hy x Hx (Hall1 x Hx (LeanListMem_head A x xs Hxs)).
      - assume Hm2: LeanListMem A b xs. exact Hall2 b Hb Hm2. }
    exact LeanListPairwise_cons A R x Hx (Lean_List_cons_node A y xs) Hyxs Hxall
      (LeanListPairwise_cons A R y Hy xs Hxs
        (fun b Hb Hm => Hall1 b Hb (LeanListMem_tail A b x Hx xs Hxs Hm)) Hrest2). }
claim Htrans: forall xs ys zs :e Lean_List A,
  LeanListPerm A ys xs /\ (LeanListPairwise A R xs -> LeanListPairwise A R ys) ->
  LeanListPerm A zs ys /\ (LeanListPairwise A R ys -> LeanListPairwise A R zs) ->
  LeanListPerm A zs xs /\ (LeanListPairwise A R xs -> LeanListPairwise A R zs).
{ let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A. let zs. assume Hzs: zs :e Lean_List A.
  assume IH1: LeanListPerm A ys xs /\ (LeanListPairwise A R xs -> LeanListPairwise A R ys).
  assume IH2: LeanListPerm A zs ys /\ (LeanListPairwise A R ys -> LeanListPairwise A R zs).
  apply IH1. assume Hp1: LeanListPerm A ys xs. assume Hi1: LeanListPairwise A R xs -> LeanListPairwise A R ys.
  apply IH2. assume Hp2: LeanListPerm A zs ys. assume Hi2: LeanListPairwise A R ys -> LeanListPairwise A R zs.
  apply andI.
  - exact LeanListPerm_trans A zs Hzs ys Hys xs Hxs Hp2 Hp1.
  - assume H: LeanListPairwise A R xs. exact Hi2 (Hi1 H). }
let xs ys. assume Hperm: LeanListPerm A xs ys.
apply LeanListPerm_ind A
  (fun xs ys => LeanListPerm A ys xs /\ (LeanListPairwise A R xs -> LeanListPairwise A R ys))
  Hnil Hcons Hswap Htrans xs ys Hperm.
assume Hback: LeanListPerm A ys xs.
assume Himp: LeanListPairwise A R xs -> LeanListPairwise A R ys.
exact Himp.
Qed.

(** The relation "different", as Lean writes it in List.Nodup. **)
Definition LeanListNe : set -> set :=
  fun A => (fun x1 :e A => (fun x2 :e A => (Pi_ ux :e (Lean_Eq_Prop A x1 x2), Lean_False_Prop))).

Theorem LeanListNe_typed : forall A, LeanListNe A :e (Pi_ a :e A, Pi_ b :e A, LeanProp).
let A.
exact lam_Pi A (fun a => Pi_ b :e A, LeanProp)
  (fun x1 => (fun x2 :e A => (Pi_ ux :e (Lean_Eq_Prop A x1 x2), Lean_False_Prop)))
  (fun x1 Hx1 => lam_Pi A (fun _ => LeanProp) (fun x2 => (Pi_ ux :e (Lean_Eq_Prop A x1 x2), Lean_False_Prop))
    (fun x2 Hx2 => LeanPi_prop (Lean_Eq_Prop A x1 x2) (fun _ => Lean_False_Prop)
      (fun u Hu => Lean_False_Prop_prop))).
Qed.

Theorem LeanListNe_ap : forall A, forall x y :e A,
  (LeanListNe A) x y = (Pi_ ux :e (Lean_Eq_Prop A x y), Lean_False_Prop).
let A x. assume Hx: x :e A. let y. assume Hy: y :e A.
prove (fun x1 :e A => (fun x2 :e A => (Pi_ ux :e (Lean_Eq_Prop A x1 x2), Lean_False_Prop))) x y =
  (Pi_ ux :e (Lean_Eq_Prop A x y), Lean_False_Prop).
rewrite beta A (fun x1 => (fun x2 :e A => (Pi_ ux :e (Lean_Eq_Prop A x1 x2), Lean_False_Prop))) x Hx.
exact beta A (fun x2 => (Pi_ ux :e (Lean_Eq_Prop A x x2), Lean_False_Prop)) y Hy.
Qed.

Theorem LeanListNe_intro : forall A, forall x y :e A, x <> y -> 0 :e (LeanListNe A) x y.
let A x. assume Hx: x :e A. let y. assume Hy: y :e A. assume Hne: x <> y.
rewrite LeanListNe_ap A x Hx y Hy.
apply Lean_refute_0 (Lean_Eq_Prop A x y) (Lean_Eq_Prop_prop A x y).
assume H: 0 :e Lean_Eq_Prop A x y.
exact Hne (LeanEq_sound A x y 0 H).
Qed.

Theorem LeanListNe_elim : forall A, forall x y :e A, 0 :e (LeanListNe A) x y -> x <> y.
let A x. assume Hx: x :e A. let y. assume Hy: y :e A. assume H: 0 :e (LeanListNe A) x y.
assume Heq: x = y.
claim H1: 0 :e (Pi_ ux :e (Lean_Eq_Prop A x y), Lean_False_Prop).
{ exact In_eq_r 0 ((LeanListNe A) x y) (Pi_ ux :e (Lean_Eq_Prop A x y), Lean_False_Prop)
    (LeanListNe_ap A x Hx y Hy) H. }
exact Lean_False_Prop_false (0 0)
  (ap_Pi (Lean_Eq_Prop A x y) (fun _ => Lean_False_Prop) 0 0 H1 (Lean_Eq_proof_of A x y Heq)).
Qed.

Theorem LeanListNe_sym : forall A, forall x y :e A, 0 :e (LeanListNe A) x y -> 0 :e (LeanListNe A) y x.
let A x. assume Hx: x :e A. let y. assume Hy: y :e A. assume H: 0 :e (LeanListNe A) x y.
apply LeanListNe_intro A y Hy x Hx.
assume Heq: y = x.
exact LeanListNe_elim A x Hx y Hy H (eq_sym_i y x Heq).
Qed.

(** List.Perm.nodup_iff, on the truth values. **)
Theorem LeanListPerm_nodup : forall A xs ys, LeanListPerm A xs ys ->
  LeanListPairwise A (LeanListNe A) xs -> LeanListPairwise A (LeanListNe A) ys.
let A.
exact LeanListPerm_pairwise A (LeanListNe A) (LeanListNe_typed A) (LeanListNe_sym A).
Qed.
