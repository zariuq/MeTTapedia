(** Lean's type theory interpreted in Egal (Megalodon's HOTG), part H1.

   The admitted fragment is Lean4Lean's typing judgment (VExpr) for sorts,
   dependent products, abstractions, applications, constants and let, with
   Prop impredicative and proof irrelevance, and inductive families whose
   constructors have finitely many fields, each a recursive occurrence of the
   family at some index or a set given by the earlier fields.  Universe
   levels are instantiated: a declaration is interpreted at each level it is
   used at, Prop at level 0.  The universes are those of Egal's UnivOf.

   The interpretation, with Egal's set functions (fun x :e X => F x is the
   set of the pairs (x, y) with y :e F x, and f x reads that set back):

     Sort 0 = Prop       LeanProp = Power 1   (truth values: 0 false, 1 true)
     Sort (u+1)          LeanUniv u, the u-th Grothendieck universe above omega
     (x : A) -> B x      Pi_ x :e [A], [B x]
     fun x : A => t      fun x :e [A] => [t]
     f a                 [f] [a]
     an inductive        one general construction (section IndFamily): a
       family T i        constructor k at fields a is the value
                         ((tag k, index), a); T i is the fiber at i of the
                         least set closed under the constructors
     its constructors    IndNode k, curried over the fields
     its recursor        IndRec, the least relation closed under the methods
     an inductive        the truth value of its fiber being inhabited.  It
       proposition       eliminates into data only where Lean allows that,
                         for syntactic subsingletons such as Eq, whose fiber
                         has at most one member: the recursor runs IndRec on
                         that member.  Others eliminate only into Prop.

   Instances are generated from Lean's own declarations (generate.sh, into
   generated/LeanFamilies.mg): for each admitted family its signature as
   finite sequences, its types, constructors with their Pi types, recursor
   with iota equations and dependent typing, no-confusion, and for indexed
   families one index per value.  An inductive proposition is the truth
   value of its fiber being inhabited (E_Prop), its proofs are 0, and its
   recursor runs on the fiber's chosen member, with the motive at the proof.

   Soundness, rule by rule: a well-typed term lies in its type.  A proof of
   a proposition is its only element 0, so proofs are irrelevant; a product
   into Prop is a truth value again, so Prop is impredicative, with no case
   apart: a function whose values are all 0 is the empty set of pairs.  These
   are the choices of the set model of the tower interpretation in
   Mettapedia (TowerInterpretation/SetModel.lean and the inductive carriers
   of ZFSetInductive): Aczel traces for functions, truth values for
   propositions, constructor values built from a tag and the tuple of the
   fields, carriers as the union over omega of the iterates of one step.  The
   closure facts (that pairs, functions and products stay inside a universe)
   are proved here and in Library/Typing.mg, because Egal's preamble states
   them only for its own operations.  Library/Conversion.mg (membership
   along equations) is read before this file, Library/Typing.mg after it. **)

(** ---- closure of a transitive ZF-closed set ---- **)

Theorem ZF_Empty_In : forall U, TransSet U -> ZF_closed U -> forall X :e U, 0 :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. let X. assume HX: X :e U.
claim LP: Power X :e U.
{ exact ZF_Power_closed U Hz X HX. }
exact Ht (Power X) LP 0 (Empty_In_Power X).
Qed.

Theorem ZF_Subq_In : forall U, TransSet U -> ZF_closed U -> forall T :e U, forall S, S c= T -> S :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. let T. assume HT: T :e U.
let S. assume HS: S c= T.
claim LP: Power T :e U.
{ exact ZF_Power_closed U Hz T HT. }
exact Ht (Power T) LP S (PowerI T S HS).
Qed.

Theorem ZF_Inj1_In : forall U, TransSet U -> ZF_closed U -> forall X :e U, Inj1 X :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U.
claim L: forall X, X :e U -> Inj1 X :e U.
{ apply In_ind (fun X => X :e U -> Inj1 X :e U).
  let X. assume IH: forall x :e X, x :e U -> Inj1 x :e U. assume HX: X :e U.
  rewrite Inj1_eq X.
  apply ZF_binunion_closed U Hz.
  - apply ZF_Sing_closed U Hz. exact ZF_Empty_In U Ht Hz X HX.
  - apply ZF_Repl_closed U Hz X HX Inj1.
    let x. assume Hx: x :e X.
    exact IH x Hx (Ht X HX x Hx).
}
exact L.
Qed.

Theorem ZF_Inj0_In : forall U, TransSet U -> ZF_closed U -> forall X :e U, Inj0 X :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. let X. assume HX: X :e U.
prove {Inj1 x|x :e X} :e U.
apply ZF_Repl_closed U Hz X HX Inj1.
let x. assume Hx: x :e X.
exact ZF_Inj1_In U Ht Hz x (Ht X HX x Hx).
Qed.

Theorem ZF_pair_In : forall U, TransSet U -> ZF_closed U -> forall x y :e U, setsum x y :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U.
let x. assume Hx: x :e U. let y. assume Hy: y :e U.
prove {Inj0 u|u :e x} :\/: {Inj1 v|v :e y} :e U.
apply ZF_binunion_closed U Hz.
- apply ZF_Repl_closed U Hz x Hx Inj0.
  let u. assume Hu: u :e x.
  exact ZF_Inj0_In U Ht Hz u (Ht x Hx u Hu).
- apply ZF_Repl_closed U Hz y Hy Inj1.
  let v. assume Hv: v :e y.
  exact ZF_Inj1_In U Ht Hz v (Ht y Hy v Hv).
Qed.

Theorem ZF_lam_In : forall U, TransSet U -> ZF_closed U -> forall X :e U, forall F:set -> set,
  (forall x :e X, F x :e U) -> (fun x :e X => F x) :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. let X. assume HX: X :e U.
let F. assume HF: forall x :e X, F x :e U.
claim LG: forall x :e X, {setsum x y|y :e F x} :e U.
{ let x. assume Hx: x :e X.
  exact ZF_Repl_closed U Hz (F x) (HF x Hx) (setsum x)
    (fun y Hy => ZF_pair_In U Ht Hz x (Ht X HX x Hx) y (Ht (F x) (HF x Hx) y Hy)).
}
claim LR: {{setsum x y|y :e F x}|x :e X} :e U.
{ exact ZF_Repl_closed U Hz X HX (fun x => {setsum x y|y :e F x}) LG. }
claim LU: Union {{setsum x y|y :e F x}|x :e X} :e U.
{ exact ZF_Union_closed U Hz {{setsum x y|y :e F x}|x :e X} LR. }
apply ZF_Subq_In U Ht Hz (Union {{setsum x y|y :e F x}|x :e X}) LU.
let z. assume Hz2: z :e \/_ x :e X, {setsum x y|y :e F x}.
apply famunionE_impred X (fun x => {setsum x y|y :e F x}) z Hz2.
let x. assume Hx: x :e X. assume Hzx: z :e {setsum x y|y :e F x}.
exact UnionI {{setsum x y|y :e F x}|x :e X} z {setsum x y|y :e F x} Hzx
  (ReplI X (fun x => {setsum x y|y :e F x}) x Hx).
Qed.

Theorem ZF_Pi_In : forall U, TransSet U -> ZF_closed U -> forall X :e U, forall Y:set -> set,
  (forall x :e X, Y x :e U) -> (Pi_ x :e X, Y x) :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. let X. assume HX: X :e U.
let Y. assume HY: forall x :e X, Y x :e U.
claim LS: (Sigma_ x :e X, Union (Y x)) :e U.
{ apply ZF_lam_In U Ht Hz X HX (fun x => Union (Y x)).
  let x. assume Hx: x :e X.
  exact ZF_Union_closed U Hz (Y x) (HY x Hx).
}
claim LP: Power (Sigma_ x :e X, Union (Y x)) :e U.
{ exact ZF_Power_closed U Hz (Sigma_ x :e X, Union (Y x)) LS. }
apply ZF_Subq_In U Ht Hz (Power (Sigma_ x :e X, Union (Y x))) LP.
exact Sep_Subq (Power (Sigma_ x :e X, Union (Y x))) (fun f => forall x :e X, f x :e Y x).
Qed.

(** ---- universes: Sort (u+1) is LeanUniv u ---- **)

Definition LeanUniv : set -> set := nat_primrec (UnivOf omega) (fun k U => UnivOf U).

Theorem LeanUniv_0 : LeanUniv 0 = UnivOf omega.
exact nat_primrec_0 (UnivOf omega) (fun k U => UnivOf U).
Qed.

Theorem LeanUniv_S : forall n, nat_p n -> LeanUniv (ordsucc n) = UnivOf (LeanUniv n).
let n. assume Hn: nat_p n.
exact nat_primrec_S (UnivOf omega) (fun k U => UnivOf U) n Hn.
Qed.

Theorem LeanUniv_UnivOf : forall n, nat_p n -> exists N, LeanUniv n = UnivOf N.
apply nat_ind.
- witness omega. exact LeanUniv_0.
- let n. assume Hn: nat_p n. assume IH: exists N, LeanUniv n = UnivOf N.
  witness LeanUniv n. exact LeanUniv_S n Hn.
Qed.

Theorem LeanUniv_TransSet : forall n, nat_p n -> TransSet (LeanUniv n).
let n. assume Hn: nat_p n.
apply LeanUniv_UnivOf n Hn.
let N. assume HN: LeanUniv n = UnivOf N.
rewrite HN. exact UnivOf_TransSet N.
Qed.

Theorem LeanUniv_ZF_closed : forall n, nat_p n -> ZF_closed (LeanUniv n).
let n. assume Hn: nat_p n.
apply LeanUniv_UnivOf n Hn.
let N. assume HN: LeanUniv n = UnivOf N.
rewrite HN. exact UnivOf_ZF_closed N.
Qed.

Theorem LeanUniv_In_S : forall n, nat_p n -> LeanUniv n :e LeanUniv (ordsucc n).
let n. assume Hn: nat_p n.
rewrite LeanUniv_S n Hn. exact UnivOf_In (LeanUniv n).
Qed.

Theorem omega_In_LeanUniv : forall n, nat_p n -> omega :e LeanUniv n.
apply nat_ind.
- rewrite LeanUniv_0. exact UnivOf_In omega.
- let n. assume Hn: nat_p n. assume IH: omega :e LeanUniv n.
  exact LeanUniv_TransSet (ordsucc n) (nat_ordsucc n Hn) (LeanUniv n) (LeanUniv_In_S n Hn) omega IH.
Qed.

Theorem LeanUniv_cumulative : forall n, nat_p n -> forall m :e n, LeanUniv m :e LeanUniv n.
apply nat_ind.
- let m. assume Hm: m :e 0. prove False. exact EmptyE m Hm.
- let n. assume Hn: nat_p n. assume IH: forall m :e n, LeanUniv m :e LeanUniv n.
  let m. assume Hm: m :e ordsucc n.
  apply ordsuccE n m Hm.
  + assume H1: m :e n.
    exact LeanUniv_TransSet (ordsucc n) (nat_ordsucc n Hn) (LeanUniv n) (LeanUniv_In_S n Hn) (LeanUniv m) (IH m H1).
  + assume H1: m = n. rewrite H1. exact LeanUniv_In_S n Hn.
Qed.

(** ---- Prop: Sort 0 is the set of truth values ---- **)

Definition LeanProp : set := Power 1.

Theorem LeanProp_In_LeanUniv : forall n, nat_p n -> LeanProp :e LeanUniv n.
let n. assume Hn: nat_p n.
claim L1: 1 :e LeanUniv n.
{ exact LeanUniv_TransSet n Hn omega (omega_In_LeanUniv n Hn) 1 (nat_p_omega 1 nat_1). }
exact ZF_Power_closed (LeanUniv n) (LeanUniv_ZF_closed n Hn) 1 L1.
Qed.

Theorem LeanProp_true : 1 :e LeanProp.
exact PowerI 1 1 (Subq_ref 1).
Qed.

Theorem LeanProp_false : 0 :e LeanProp.
exact Empty_In_Power 1.
Qed.

Theorem LeanProp_not_two : 2 /:e LeanProp.
assume H: 2 :e Power 1.
exact In_irref 1 (PowerE 1 2 H 1 In_1_2).
Qed.

Theorem LeanProp_proof_irrelevant : forall P :e LeanProp, forall p q :e P, p = q.
let P. assume HP: P :e Power 1. let p. assume Hp: p :e P. let q. assume Hq: q :e P.
claim Lp: p = 0.
{ exact SingE 0 p (Subq_1_Sing0 p (PowerE 1 P HP p Hp)). }
claim Lq: q = 0.
{ exact SingE 0 q (Subq_1_Sing0 q (PowerE 1 P HP q Hq)). }
rewrite Lp. rewrite Lq. reflexivity.
Qed.

(** Sort u: Prop at 0, the universe LeanUniv k at k + 1. **)
Definition LeanSort : set -> set := fun u => nat_primrec LeanProp (fun k _ => LeanUniv k) u.

Theorem LeanSort_0 : LeanSort 0 = LeanProp.
exact nat_primrec_0 LeanProp (fun k _ => LeanUniv k).
Qed.

Theorem LeanSort_S : forall k, nat_p k -> LeanSort (ordsucc k) = LeanUniv k.
let k. assume Hk: nat_p k.
exact nat_primrec_S LeanProp (fun k _ => LeanUniv k) k Hk.
Qed.

(** A truth value lies in every universe. **)
Theorem LeanProp_sub_In : forall u, nat_p u -> forall p :e LeanProp, p :e LeanUniv u.
let u. assume Hu: nat_p u. let p. assume Hp: p :e LeanProp.
exact LeanUniv_TransSet u Hu LeanProp (LeanProp_In_LeanUniv u Hu) p Hp.
Qed.

(** ---- inductive families: one construction for every declaration ---- **)

(** The general construction follows the set model of the tower
    interpretation (ZFSetInductive, SetInductive): a constructor's value is
    built from its tag and the tuple of its arguments, and the carrier is the
    union over omega of the iterates of one step from the empty set.  For an
    indexed family the value also records the index it lies at, so that the
    index of an argument is read from the argument itself:

      IndNode k a = ((T k, O k a), a)

    A signature: constructors K; tag T k; number of fields N k (a natural);
    R k j when field j of k is recursive, at index Ix k j a; otherwise the
    field ranges over F k j a, inside the bound B; O k a the index of the
    value.  An inductive type without indices is the case O k a = 0. **)

Theorem In_eq_rs : forall x y z, y = z -> x :e z -> x :e y.
let x y z. assume H: y = z. assume Hx: x :e z.
rewrite H. exact Hx.
Qed.

Theorem ZF_famunion_In : forall U, TransSet U -> ZF_closed U -> forall X :e U, forall G:set -> set,
  (forall x :e X, G x :e U) -> (\/_ x :e X, G x) :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. let X. assume HX: X :e U.
let G. assume HG: forall x :e X, G x :e U.
claim LU: Union {G x|x :e X} :e U.
{ exact ZF_Union_closed U Hz {G x|x :e X} (ZF_Repl_closed U Hz X HX G HG). }
apply ZF_Subq_In U Ht Hz (Union {G x|x :e X}) LU.
let z. assume Hz2: z :e \/_ x :e X, G x.
apply famunionE_impred X G z Hz2.
let x. assume Hx: x :e X. assume Hzx: z :e G x.
exact UnionI {G x|x :e X} z (G x) Hzx (ReplI X G x Hx).
Qed.

Theorem binunion_mono_r : forall A X Y, X c= Y -> A :\/: X c= A :\/: Y.
let A X Y. assume H: X c= Y.
apply binunion_Subq_min A X (A :\/: Y).
- exact binunion_Subq_1 A Y.
- exact Subq_tra X Y (A :\/: Y) H (binunion_Subq_2 A Y).
Qed.

Theorem nat_max_cases : forall m n, nat_p m -> nat_p n ->
  forall p:prop, ((m :e n \/ m = n) -> p) -> (n :e m -> p) -> p.
let m n. assume Hm: nat_p m. assume Hn: nat_p n. let p.
assume H1: (m :e n \/ m = n) -> p. assume H2: n :e m -> p.
apply ordinal_trichotomy_or m n (nat_p_ordinal m Hm) (nat_p_ordinal n Hn).
- assume H: m :e n \/ m = n. exact H1 H.
- assume H: n :e m. exact H2 H.
Qed.

Section IndFamily.

Variable K : set.
Variable T : set -> set.
Variable N : set -> set.
Variable R : set -> set -> prop.
Variable F : set -> set -> set -> set.
Variable Ix : set -> set -> set -> set.
Variable O : set -> set -> set.
Variable B : set.

Definition IndNode : set -> set -> set := fun k a => setsum (setsum (T k) (O k a)) a.

Definition IndIdx : set -> set := fun x => proj1 (proj0 x).

Definition IndFits : set -> set -> set -> prop := fun X k a =>
  forall j :e N k, (R k j -> a j :e X /\ IndIdx (a j) = Ix k j a) /\ (~ R k j -> a j :e F k j a).

Definition IndArgs : set -> set -> set := fun X k =>
  {a :e Pi_ j :e N k, B :\/: X | IndFits X k a}.

Definition IndStep : set -> set := fun X => \/_ k :e K, {IndNode k a | a :e IndArgs X k}.

Definition IndIter : set -> set := nat_primrec 0 (fun n X => IndStep X).

Definition IndCarrier : set := \/_ n :e omega, IndIter n.

Definition IndFiber : set -> set := fun i => {x :e IndCarrier | IndIdx x = i}.

Theorem IndIdx_Node : forall k a, IndIdx (IndNode k a) = O k a.
let k a.
prove proj1 (proj0 (setsum (setsum (T k) (O k a)) a)) = O k a.
rewrite proj0_pair_eq (setsum (T k) (O k a)) a.
exact proj1_pair_eq (T k) (O k a).
Qed.

Theorem IndNode_fields : forall k a j, (proj1 (IndNode k a)) j = a j.
let k a j.
prove (proj1 (setsum (setsum (T k) (O k a)) a)) j = a j.
rewrite proj1_pair_eq (setsum (T k) (O k a)) a. reflexivity.
Qed.

Theorem IndFits_mono : forall X Y, X c= Y -> forall k a, IndFits X k a -> IndFits Y k a.
let X Y. assume HXY: X c= Y. let k a. assume H: IndFits X k a.
let j. assume Hj: j :e N k.
apply H j Hj.
assume H1: R k j -> a j :e X /\ IndIdx (a j) = Ix k j a.
assume H2: ~ R k j -> a j :e F k j a.
apply andI.
- assume Hr: R k j.
  apply H1 Hr. assume Ha1: a j :e X. assume Ha2: IndIdx (a j) = Ix k j a.
  exact andI (a j :e Y) (IndIdx (a j) = Ix k j a) (HXY (a j) Ha1) Ha2.
- exact H2.
Qed.

Theorem IndArgs_mono : forall X Y, X c= Y -> forall k, IndArgs X k c= IndArgs Y k.
let X Y. assume HXY: X c= Y. let k a. assume Ha: a :e IndArgs X k.
claim LPi: a :e Pi_ j :e N k, B :\/: X.
{ exact SepE1 (Pi_ j :e N k, B :\/: X) (fun a => IndFits X k a) a Ha. }
claim LFits: IndFits X k a.
{ exact SepE2 (Pi_ j :e N k, B :\/: X) (fun a => IndFits X k a) a Ha. }
prove a :e {a :e Pi_ j :e N k, B :\/: Y | IndFits Y k a}.
apply SepI (Pi_ j :e N k, B :\/: Y) (fun a => IndFits Y k a) a.
- exact Pi_cod_mon (N k) (fun j => B :\/: X) (fun j => B :\/: Y)
    (fun j Hj => binunion_mono_r B X Y HXY) a LPi.
- exact IndFits_mono X Y HXY k a LFits.
Qed.

Theorem IndStep_mono : forall X Y, X c= Y -> IndStep X c= IndStep Y.
let X Y. assume HXY: X c= Y. let z. assume Hz: z :e \/_ k :e K, {IndNode k a | a :e IndArgs X k}.
apply famunionE_impred K (fun k => {IndNode k a | a :e IndArgs X k}) z Hz.
let k. assume Hk: k :e K. assume Hzk: z :e {IndNode k a | a :e IndArgs X k}.
apply ReplE_impred (IndArgs X k) (IndNode k) z Hzk.
let a. assume Ha: a :e IndArgs X k. assume Hza: z = IndNode k a.
rewrite Hza.
exact famunionI K (fun k => {IndNode k a | a :e IndArgs Y k}) k (IndNode k a) Hk
  (ReplI (IndArgs Y k) (IndNode k) a (IndArgs_mono X Y HXY k a Ha)).
Qed.

Theorem IndIter_0 : IndIter 0 = 0.
exact nat_primrec_0 0 (fun n X => IndStep X).
Qed.

Theorem IndIter_S : forall n, nat_p n -> IndIter (ordsucc n) = IndStep (IndIter n).
let n. assume Hn: nat_p n.
exact nat_primrec_S 0 (fun n X => IndStep X) n Hn.
Qed.

Theorem IndIter_sub_S : forall n, nat_p n -> IndIter n c= IndIter (ordsucc n).
apply nat_ind.
- let z. assume Hz: z :e IndIter 0.
  prove False. exact EmptyE z (In_eq_r z (IndIter 0) 0 IndIter_0 Hz).
- let n. assume Hn: nat_p n. assume IH: IndIter n c= IndIter (ordsucc n).
  let z. assume Hz: z :e IndIter (ordsucc n).
  claim L1: z :e IndStep (IndIter n).
  { exact In_eq_r z (IndIter (ordsucc n)) (IndStep (IndIter n)) (IndIter_S n Hn) Hz. }
  claim L2: z :e IndStep (IndIter (ordsucc n)).
  { exact IndStep_mono (IndIter n) (IndIter (ordsucc n)) IH z L1. }
  exact In_eq_rs z (IndIter (ordsucc (ordsucc n))) (IndStep (IndIter (ordsucc n)))
    (IndIter_S (ordsucc n) (nat_ordsucc n Hn)) L2.
Qed.

Theorem IndIter_mono : forall n, nat_p n -> forall m :e n, IndIter m c= IndIter n.
apply nat_ind.
- let m. assume Hm: m :e 0. prove False. exact EmptyE m Hm.
- let n. assume Hn: nat_p n. assume IH: forall m :e n, IndIter m c= IndIter n.
  let m. assume Hm: m :e ordsucc n.
  apply ordsuccE n m Hm.
  + assume H1: m :e n.
    exact Subq_tra (IndIter m) (IndIter n) (IndIter (ordsucc n)) (IH m H1) (IndIter_sub_S n Hn).
  + assume H1: m = n. rewrite H1. exact IndIter_sub_S n Hn.
Qed.

Theorem IndIter_le : forall m n, nat_p n -> (m :e n \/ m = n) -> IndIter m c= IndIter n.
let m n. assume Hn: nat_p n. assume H: m :e n \/ m = n.
apply H.
- assume H1: m :e n. exact IndIter_mono n Hn m H1.
- assume H1: m = n. rewrite H1. exact Subq_ref (IndIter n).
Qed.

Theorem IndIter_cover : forall n, nat_p n -> forall P:set -> prop, forall Z:set -> set,
  (forall j :e n, P j -> exists m, nat_p m /\ Z j :e IndIter m) ->
  exists m, nat_p m /\ forall j :e n, P j -> Z j :e IndIter m.
apply nat_ind.
- let P Z. assume H. witness 0. apply andI.
  + exact nat_0.
  + let j. assume Hj: j :e 0. prove False. exact EmptyE j Hj.
- let n. assume Hn: nat_p n.
  assume IH: forall P:set -> prop, forall Z:set -> set,
    (forall j :e n, P j -> exists m, nat_p m /\ Z j :e IndIter m) ->
    exists m, nat_p m /\ forall j :e n, P j -> Z j :e IndIter m.
  let P Z. assume H: forall j :e ordsucc n, P j -> exists m, nat_p m /\ Z j :e IndIter m.
  apply IH P Z (fun j Hj => H j (ordsuccI1 n j Hj)).
  let m1. assume Hm1: nat_p m1 /\ forall j :e n, P j -> Z j :e IndIter m1.
  apply Hm1. assume Hm1n: nat_p m1. assume Hm1c: forall j :e n, P j -> Z j :e IndIter m1.
  apply xm (P n).
  + assume HPn: P n.
    apply H n (ordsuccI2 n) HPn.
    let m2. assume Hm2: nat_p m2 /\ Z n :e IndIter m2.
    apply Hm2. assume Hm2n: nat_p m2. assume Hm2c: Z n :e IndIter m2.
    apply nat_max_cases m1 m2 Hm1n Hm2n.
    * assume H12: m1 :e m2 \/ m1 = m2.
      witness m2. apply andI.
      { exact Hm2n. }
      { let j. assume Hj: j :e ordsucc n. assume HPj: P j.
        apply ordsuccE n j Hj.
        - assume Hjn: j :e n. exact IndIter_le m1 m2 Hm2n H12 (Z j) (Hm1c j Hjn HPj).
        - assume Hjeq: j = n. rewrite Hjeq. exact Hm2c.
      }
    * assume H21: m2 :e m1.
      witness m1. apply andI.
      { exact Hm1n. }
      { let j. assume Hj: j :e ordsucc n. assume HPj: P j.
        apply ordsuccE n j Hj.
        - assume Hjn: j :e n. exact Hm1c j Hjn HPj.
        - assume Hjeq: j = n. rewrite Hjeq. exact IndIter_mono m1 Hm1n m2 H21 (Z n) Hm2c.
      }
  + assume HnPn: ~ P n.
    witness m1. apply andI.
    * exact Hm1n.
    * let j. assume Hj: j :e ordsucc n. assume HPj: P j.
      apply ordsuccE n j Hj.
      { assume Hjn: j :e n. exact Hm1c j Hjn HPj. }
      { assume Hjeq: j = n.
        claim LPn: P n.
        { rewrite <- Hjeq. exact HPj. }
        exact FalseE (HnPn LPn) (Z j :e IndIter m1).
      }
Qed.

Definition IndBounded : prop := forall k :e K, forall a, forall j :e N k, ~ R k j -> F k j a c= B.

Theorem IndIter_Carrier : forall n, nat_p n -> IndIter n c= IndCarrier.
let n. assume Hn: nat_p n. let x. assume Hx: x :e IndIter n.
exact famunionI omega IndIter n x (nat_p_omega n Hn) Hx.
Qed.

Theorem IndCarrier_E : forall x :e IndCarrier, exists n, nat_p n /\ x :e IndIter n.
let x. assume Hx: x :e \/_ n :e omega, IndIter n.
apply famunionE_impred omega IndIter x Hx.
let n. assume Hn: n :e omega. assume Hxn: x :e IndIter n.
witness n. exact andI (nat_p n) (x :e IndIter n) (omega_nat_p n Hn) Hxn.
Qed.

Theorem IndArgs_Pi : forall X k, forall a :e IndArgs X k, a :e Pi_ j :e N k, B :\/: X.
let X k a. assume Ha: a :e IndArgs X k.
exact SepE1 (Pi_ j :e N k, B :\/: X) (fun a => IndFits X k a) a Ha.
Qed.

Theorem IndArgs_Fits : forall X k, forall a :e IndArgs X k, IndFits X k a.
let X k a. assume Ha: a :e IndArgs X k.
exact SepE2 (Pi_ j :e N k, B :\/: X) (fun a => IndFits X k a) a Ha.
Qed.

(** Closure: a constructor at arguments in the carrier gives a member.  Its
    finitely many recursive arguments lie in one iterate. **)
Theorem IndNode_In : IndBounded -> forall k :e K, nat_p (N k) ->
  forall a :e IndArgs IndCarrier k, IndNode k a :e IndCarrier.
assume HB: IndBounded. let k. assume Hk: k :e K. assume HN: nat_p (N k).
let a. assume Ha: a :e IndArgs IndCarrier k.
claim LPi: a :e Pi_ j :e N k, B :\/: IndCarrier.
{ exact IndArgs_Pi IndCarrier k a Ha. }
claim LFits: IndFits IndCarrier k a.
{ exact IndArgs_Fits IndCarrier k a Ha. }
claim Lcov: exists m, nat_p m /\ forall j :e N k, R k j -> a j :e IndIter m.
{ apply IndIter_cover (N k) HN (fun j => R k j) (fun j => a j).
  let j. assume Hj: j :e N k. assume Hr: R k j.
  apply LFits j Hj. assume H1: R k j -> a j :e IndCarrier /\ IndIdx (a j) = Ix k j a.
  assume H2: ~ R k j -> a j :e F k j a.
  apply H1 Hr. assume Haj: a j :e IndCarrier. assume H3: IndIdx (a j) = Ix k j a.
  exact IndCarrier_E (a j) Haj.
}
apply Lcov.
let m. assume Hm: nat_p m /\ forall j :e N k, R k j -> a j :e IndIter m.
apply Hm. assume Hmn: nat_p m. assume Hmc: forall j :e N k, R k j -> a j :e IndIter m.
claim LArgs: a :e IndArgs (IndIter m) k.
{ prove a :e {a :e Pi_ j :e N k, B :\/: IndIter m | IndFits (IndIter m) k a}.
  apply SepI (Pi_ j :e N k, B :\/: IndIter m) (fun a => IndFits (IndIter m) k a) a.
  - apply PiE (N k) (fun j => B :\/: IndCarrier) a LPi.
    assume Hpairs: forall u :e a, pair_p u /\ u 0 :e N k.
    assume Hvals: forall j :e N k, a j :e B :\/: IndCarrier.
    apply PiI (N k) (fun j => B :\/: IndIter m) a Hpairs.
    let j. assume Hj: j :e N k.
    apply xm (R k j).
    + assume Hr: R k j. exact binunionI2 B (IndIter m) (a j) (Hmc j Hj Hr).
    + assume Hnr: ~ R k j.
      apply LFits j Hj. assume H1: R k j -> a j :e IndCarrier /\ IndIdx (a j) = Ix k j a.
      assume H2: ~ R k j -> a j :e F k j a.
      exact binunionI1 B (IndIter m) (a j) (HB k Hk a j Hj Hnr (a j) (H2 Hnr)).
  - let j. assume Hj: j :e N k.
    apply LFits j Hj. assume H1: R k j -> a j :e IndCarrier /\ IndIdx (a j) = Ix k j a.
    assume H2: ~ R k j -> a j :e F k j a.
    apply andI.
    + assume Hr: R k j. apply H1 Hr. assume H3: a j :e IndCarrier. assume Hidx: IndIdx (a j) = Ix k j a.
      exact andI (a j :e IndIter m) (IndIdx (a j) = Ix k j a) (Hmc j Hj Hr) Hidx.
    + exact H2.
}
claim LStep: IndNode k a :e IndStep (IndIter m).
{ exact famunionI K (fun k => {IndNode k a | a :e IndArgs (IndIter m) k}) k (IndNode k a) Hk
    (ReplI (IndArgs (IndIter m) k) (IndNode k) a LArgs). }
exact IndIter_Carrier (ordsucc m) (nat_ordsucc m Hmn) (IndNode k a)
  (In_eq_rs (IndNode k a) (IndIter (ordsucc m)) (IndStep (IndIter m)) (IndIter_S m Hmn) LStep).
Qed.

(** Inversion: every member is a constructor at arguments in the carrier. **)
Theorem IndCarrier_inv : forall x :e IndCarrier,
  exists k :e K, exists a :e IndArgs IndCarrier k, x = IndNode k a.
claim L: forall n, nat_p n -> forall x :e IndIter n,
  exists k :e K, exists a :e IndArgs IndCarrier k, x = IndNode k a.
{ apply nat_ind.
  - let x. assume Hx: x :e IndIter 0.
    prove False. exact EmptyE x (In_eq_r x (IndIter 0) 0 IndIter_0 Hx).
  - let n. assume Hn: nat_p n.
    assume IH: forall x :e IndIter n, exists k :e K, exists a :e IndArgs IndCarrier k, x = IndNode k a.
    let x. assume Hx: x :e IndIter (ordsucc n).
    claim L1: x :e IndStep (IndIter n).
    { exact In_eq_r x (IndIter (ordsucc n)) (IndStep (IndIter n)) (IndIter_S n Hn) Hx. }
    apply famunionE_impred K (fun k => {IndNode k a | a :e IndArgs (IndIter n) k}) x L1.
    let k. assume Hk: k :e K. assume Hxk: x :e {IndNode k a | a :e IndArgs (IndIter n) k}.
    apply ReplE_impred (IndArgs (IndIter n) k) (IndNode k) x Hxk.
    let a. assume Ha: a :e IndArgs (IndIter n) k. assume Hxa: x = IndNode k a.
    witness k. apply andI.
    + exact Hk.
    + witness a. apply andI.
      * exact IndArgs_mono (IndIter n) IndCarrier (IndIter_Carrier n Hn) k a Ha.
      * exact Hxa.
}
let x. assume Hx: x :e IndCarrier.
apply IndCarrier_E x Hx.
let n. assume Hn: nat_p n /\ x :e IndIter n.
apply Hn. assume Hnn: nat_p n. assume Hxn: x :e IndIter n.
exact L n Hnn x Hxn.
Qed.

(** Induction over the carrier. **)
Theorem IndCarrier_ind : forall Q:set -> prop,
  (forall k :e K, forall a :e IndArgs IndCarrier k, (forall j :e N k, R k j -> Q (a j)) -> Q (IndNode k a)) ->
  forall x :e IndCarrier, Q x.
let Q.
assume HQ: forall k :e K, forall a :e IndArgs IndCarrier k, (forall j :e N k, R k j -> Q (a j)) -> Q (IndNode k a).
claim L: forall n, nat_p n -> forall x :e IndIter n, Q x.
{ apply nat_ind.
  - let x. assume Hx: x :e IndIter 0.
    prove False. exact EmptyE x (In_eq_r x (IndIter 0) 0 IndIter_0 Hx).
  - let n. assume Hn: nat_p n. assume IH: forall x :e IndIter n, Q x.
    let x. assume Hx: x :e IndIter (ordsucc n).
    claim L1: x :e IndStep (IndIter n).
    { exact In_eq_r x (IndIter (ordsucc n)) (IndStep (IndIter n)) (IndIter_S n Hn) Hx. }
    apply famunionE_impred K (fun k => {IndNode k a | a :e IndArgs (IndIter n) k}) x L1.
    let k. assume Hk: k :e K. assume Hxk: x :e {IndNode k a | a :e IndArgs (IndIter n) k}.
    apply ReplE_impred (IndArgs (IndIter n) k) (IndNode k) x Hxk.
    let a. assume Ha: a :e IndArgs (IndIter n) k. assume Hxa: x = IndNode k a.
    rewrite Hxa.
    apply HQ k Hk a (IndArgs_mono (IndIter n) IndCarrier (IndIter_Carrier n Hn) k a Ha).
    let j. assume Hj: j :e N k. assume Hr: R k j.
    apply IndArgs_Fits (IndIter n) k a Ha j Hj.
    assume H1: R k j -> a j :e IndIter n /\ IndIdx (a j) = Ix k j a.
    assume H2: ~ R k j -> a j :e F k j a.
    apply H1 Hr. assume Haj: a j :e IndIter n. assume H3: IndIdx (a j) = Ix k j a.
    exact IH (a j) Haj.
}
let x. assume Hx: x :e IndCarrier.
apply IndCarrier_E x Hx.
let n. assume Hn: nat_p n /\ x :e IndIter n.
apply Hn. assume Hnn: nat_p n. assume Hxn: x :e IndIter n.
exact L n Hnn x Hxn.
Qed.

(** The carrier lies in every universe that holds the signature's data. **)
Theorem IndCarrier_In : forall U, TransSet U -> ZF_closed U -> omega :e U -> K :e U -> B :e U ->
  (forall k :e K, nat_p (N k)) -> (forall k :e K, T k :e U) ->
  (forall k :e K, forall V :e U, forall a :e (Pi_ j :e N k, V), O k a :e U) ->
  IndCarrier :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. assume Hom: omega :e U.
assume HK: K :e U. assume HB: B :e U.
assume HN: forall k :e K, nat_p (N k). assume HT: forall k :e K, T k :e U.
assume HO: forall k :e K, forall V :e U, forall a :e (Pi_ j :e N k, V), O k a :e U.
claim LStep: forall X :e U, IndStep X :e U.
{ let X. assume HX: X :e U.
  prove (\/_ k :e K, {IndNode k a | a :e IndArgs X k}) :e U.
  apply ZF_famunion_In U Ht Hz K HK (fun k => {IndNode k a | a :e IndArgs X k}).
  let k. assume Hk: k :e K.
  claim LV: B :\/: X :e U.
  { exact ZF_binunion_closed U Hz B HB X HX. }
  claim LNk: N k :e U.
  { exact Ht omega Hom (N k) (nat_p_omega (N k) (HN k Hk)). }
  claim LPi: (Pi_ j :e N k, B :\/: X) :e U.
  { exact ZF_Pi_In U Ht Hz (N k) LNk (fun j => B :\/: X) (fun j Hj => LV). }
  claim LArgs: IndArgs X k :e U.
  { exact ZF_Subq_In U Ht Hz (Pi_ j :e N k, B :\/: X) LPi (IndArgs X k)
      (Sep_Subq (Pi_ j :e N k, B :\/: X) (fun a => IndFits X k a)). }
  prove {IndNode k a | a :e IndArgs X k} :e U.
  apply ZF_Repl_closed U Hz (IndArgs X k) LArgs (IndNode k).
  let a. assume Ha: a :e IndArgs X k.
  claim LaPi: a :e Pi_ j :e N k, B :\/: X.
  { exact IndArgs_Pi X k a Ha. }
  prove setsum (setsum (T k) (O k a)) a :e U.
  apply ZF_pair_In U Ht Hz.
  - apply ZF_pair_In U Ht Hz.
    + exact HT k Hk.
    + exact HO k Hk (B :\/: X) LV a LaPi.
  - exact Ht (Pi_ j :e N k, B :\/: X) LPi a LaPi.
}
claim LIter: forall n, nat_p n -> IndIter n :e U.
{ apply nat_ind.
  - rewrite IndIter_0. exact ZF_Empty_In U Ht Hz omega Hom.
  - let n. assume Hn: nat_p n. assume IH: IndIter n :e U.
    rewrite IndIter_S n Hn. exact LStep (IndIter n) IH.
}
exact ZF_famunion_In U Ht Hz omega Hom IndIter (fun n Hn => LIter n (omega_nat_p n Hn)).
Qed.

Theorem IndFiber_In : forall U, TransSet U -> ZF_closed U -> IndCarrier :e U -> forall i, IndFiber i :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. assume HC: IndCarrier :e U. let i.
exact ZF_Subq_In U Ht Hz IndCarrier HC (IndFiber i) (Sep_Subq IndCarrier (fun x => IndIdx x = i)).
Qed.

(** A constructor's value lies in the fiber of its index. **)
Theorem IndNode_Fiber : IndBounded -> forall k :e K, nat_p (N k) ->
  forall a :e IndArgs IndCarrier k, IndNode k a :e IndFiber (O k a).
assume HB: IndBounded. let k. assume Hk: k :e K. assume HN: nat_p (N k).
let a. assume Ha: a :e IndArgs IndCarrier k.
prove IndNode k a :e {x :e IndCarrier | IndIdx x = O k a}.
apply SepI IndCarrier (fun x => IndIdx x = O k a) (IndNode k a).
- exact IndNode_In HB k Hk HN a Ha.
- exact IndIdx_Node k a.
Qed.

(** ---- the recursor ---- **)

(** The tuple of a constructor's recursive results, 0 at its other fields. **)
Definition IndRes : set -> (set -> set) -> set := fun k r => fun j :e N k => if R k j then r j else 0.

Definition IndDistinct : prop := forall k k' :e K, T k = T k' -> k = k'.

Definition IndRecClosed : (set -> set -> set -> set) -> (set -> set -> prop) -> prop := fun M Q =>
  forall k :e K, forall a :e IndArgs IndCarrier k, forall r:set -> set,
    (forall j :e N k, R k j -> Q (a j) (r j)) -> Q (IndNode k a) (M k a (IndRes k r)).

(** The least relation closed under the methods M. **)
Definition IndRecRel : (set -> set -> set -> set) -> set -> set -> prop := fun M x y =>
  forall Q:set -> set -> prop, IndRecClosed M Q -> Q x y.

Definition IndRec : (set -> set -> set -> set) -> set -> set := fun M x => Eps_i (IndRecRel M x).

Theorem IndRes_ext : forall k, forall r r':set -> set, (forall j :e N k, R k j -> r j = r' j) ->
  IndRes k r = IndRes k r'.
let k r r'. assume H: forall j :e N k, R k j -> r j = r' j.
prove (fun j :e N k => if R k j then r j else 0) = (fun j :e N k => if R k j then r' j else 0).
apply lam_ext (N k) (fun j => if R k j then r j else 0) (fun j => if R k j then r' j else 0).
let j. assume Hj: j :e N k.
prove (if R k j then r j else 0) = (if R k j then r' j else 0).
apply xm (R k j).
- assume Hr: R k j.
  rewrite If_i_1 (R k j) (r j) 0 Hr. rewrite If_i_1 (R k j) (r' j) 0 Hr. exact H j Hj Hr.
- assume Hnr: ~ R k j.
  rewrite If_i_0 (R k j) (r j) 0 Hnr. rewrite If_i_0 (R k j) (r' j) 0 Hnr. reflexivity.
Qed.

Theorem IndNode_inj : IndDistinct -> forall k k' :e K, forall a a', IndNode k a = IndNode k' a' -> k = k' /\ a = a'.
assume HD: IndDistinct. let k. assume Hk: k :e K. let k'. assume Hk': k' :e K.
let a a'. assume H: IndNode k a = IndNode k' a'.
apply pair_inj (setsum (T k) (O k a)) a (setsum (T k') (O k' a')) a' H.
assume H1: setsum (T k) (O k a) = setsum (T k') (O k' a'). assume H2: a = a'.
apply pair_inj (T k) (O k a) (T k') (O k' a') H1.
assume H3: T k = T k'. assume H4: O k a = O k' a'.
exact andI (k = k') (a = a') (HD k Hk k' Hk' H3) H2.
Qed.

Theorem IndRecRel_closed : forall M:set -> set -> set -> set, IndRecClosed M (IndRecRel M).
let M. let k. assume Hk: k :e K. let a. assume Ha: a :e IndArgs IndCarrier k. let r.
assume Hr: forall j :e N k, R k j -> IndRecRel M (a j) (r j).
let Q. assume HQ: IndRecClosed M Q.
exact HQ k Hk a Ha r (fun j Hj Hrj => Hr j Hj Hrj Q HQ).
Qed.

(** Inversion of the relation at a constructor. **)
Theorem IndRecRel_inv : IndDistinct -> forall M:set -> set -> set -> set, forall x y, IndRecRel M x y ->
  forall k :e K, forall a, x = IndNode k a ->
  exists r:set -> set, (forall j :e N k, R k j -> IndRecRel M (a j) (r j)) /\ y = M k a (IndRes k r).
assume HD: IndDistinct. let M x y. assume Hxy: IndRecRel M x y.
claim LQ: IndRecClosed M (fun x y => IndRecRel M x y /\ forall k :e K, forall a, x = IndNode k a ->
  exists r:set -> set, (forall j :e N k, R k j -> IndRecRel M (a j) (r j)) /\ y = M k a (IndRes k r)).
{ let k'. assume Hk': k' :e K. let a'. assume Ha': a' :e IndArgs IndCarrier k'. let r'.
  assume Hr': forall j :e N k', R k' j -> (IndRecRel M (a' j) (r' j) /\ forall k :e K, forall a, a' j = IndNode k a ->
    exists r:set -> set, (forall i :e N k, R k i -> IndRecRel M (a i) (r i)) /\ r' j = M k a (IndRes k r)).
  apply andI.
  - exact IndRecRel_closed M k' Hk' a' Ha' r' (fun j Hj Hrj => andEL (IndRecRel M (a' j) (r' j)) (forall k :e K, forall a, a' j = IndNode k a ->
      exists r:set -> set, (forall i :e N k, R k i -> IndRecRel M (a i) (r i)) /\ r' j = M k a (IndRes k r)) (Hr' j Hj Hrj)).
  - let k. assume Hk: k :e K. let a. assume Heq: IndNode k' a' = IndNode k a.
    apply IndNode_inj HD k' Hk' k Hk a' a Heq.
    assume Hkk: k' = k. assume Haa: a' = a.
    witness r'. apply andI.
    + rewrite <- Hkk. rewrite <- Haa.
      let j. assume Hj: j :e N k'. assume Hrj: R k' j.
      exact andEL (IndRecRel M (a' j) (r' j)) (forall k :e K, forall a, a' j = IndNode k a ->
        exists r:set -> set, (forall i :e N k, R k i -> IndRecRel M (a i) (r i)) /\ r' j = M k a (IndRes k r)) (Hr' j Hj Hrj).
    + rewrite <- Hkk. rewrite <- Haa. reflexivity.
}
claim L2: IndRecRel M x y /\ forall k :e K, forall a, x = IndNode k a ->
  exists r:set -> set, (forall j :e N k, R k j -> IndRecRel M (a j) (r j)) /\ y = M k a (IndRes k r).
{ exact Hxy (fun x y => IndRecRel M x y /\ forall k :e K, forall a, x = IndNode k a ->
  exists r:set -> set, (forall j :e N k, R k j -> IndRecRel M (a j) (r j)) /\ y = M k a (IndRes k r)) LQ. }
exact andER (IndRecRel M x y) (forall k :e K, forall a, x = IndNode k a ->
  exists r:set -> set, (forall j :e N k, R k j -> IndRecRel M (a j) (r j)) /\ y = M k a (IndRes k r)) L2.
Qed.

Theorem IndRecRel_ex : forall M:set -> set -> set -> set, forall x :e IndCarrier, exists y, IndRecRel M x y.
let M.
claim Lstep: forall k :e K, forall a :e IndArgs IndCarrier k,
  (forall j :e N k, R k j -> exists y, IndRecRel M (a j) y) -> exists y, IndRecRel M (IndNode k a) y.
{ let k. assume Hk: k :e K. let a. assume Ha: a :e IndArgs IndCarrier k.
  assume IH: forall j :e N k, R k j -> exists y, IndRecRel M (a j) y.
  witness M k a (IndRes k (fun j => Eps_i (IndRecRel M (a j)))).
  exact IndRecRel_closed M k Hk a Ha (fun j => Eps_i (IndRecRel M (a j)))
    (fun j Hj Hrj => Eps_i_ex (IndRecRel M (a j)) (IH j Hj Hrj)).
}
exact IndCarrier_ind (fun x => exists y, IndRecRel M x y) Lstep.
Qed.

Theorem IndRecRel_fun : IndDistinct -> forall M:set -> set -> set -> set, forall x :e IndCarrier,
  forall y y', IndRecRel M x y -> IndRecRel M x y' -> y = y'.
assume HD: IndDistinct. let M.
claim Lstep: forall k :e K, forall a :e IndArgs IndCarrier k,
  (forall j :e N k, R k j -> forall y y', IndRecRel M (a j) y -> IndRecRel M (a j) y' -> y = y') ->
  forall y y', IndRecRel M (IndNode k a) y -> IndRecRel M (IndNode k a) y' -> y = y'.
{ let k. assume Hk: k :e K. let a. assume Ha: a :e IndArgs IndCarrier k.
  assume IH: forall j :e N k, R k j -> forall y y', IndRecRel M (a j) y -> IndRecRel M (a j) y' -> y = y'.
  let y y'. assume Hy: IndRecRel M (IndNode k a) y. assume Hy': IndRecRel M (IndNode k a) y'.
  claim Lrefl: IndNode k a = IndNode k a.
  { reflexivity. }
  apply IndRecRel_inv HD M (IndNode k a) y Hy k Hk a Lrefl.
  let r. assume Hr: (forall j :e N k, R k j -> IndRecRel M (a j) (r j)) /\ y = M k a (IndRes k r).
  apply Hr. assume Hr1: forall j :e N k, R k j -> IndRecRel M (a j) (r j). assume Hr2: y = M k a (IndRes k r).
  apply IndRecRel_inv HD M (IndNode k a) y' Hy' k Hk a Lrefl.
  let r'. assume Hr': (forall j :e N k, R k j -> IndRecRel M (a j) (r' j)) /\ y' = M k a (IndRes k r').
  apply Hr'. assume Hr1': forall j :e N k, R k j -> IndRecRel M (a j) (r' j). assume Hr2': y' = M k a (IndRes k r').
  rewrite Hr2. rewrite Hr2'.
  rewrite IndRes_ext k r r' (fun j Hj Hrj => IH j Hj Hrj (r j) (r' j) (Hr1 j Hj Hrj) (Hr1' j Hj Hrj)).
  reflexivity.
}
exact IndCarrier_ind (fun x => forall y y', IndRecRel M x y -> IndRecRel M x y' -> y = y') Lstep.
Qed.

Theorem IndRec_rel : forall M:set -> set -> set -> set, forall x :e IndCarrier, IndRecRel M x (IndRec M x).
let M x. assume Hx: x :e IndCarrier.
exact Eps_i_ex (IndRecRel M x) (IndRecRel_ex M x Hx).
Qed.

(** The iota equation: at a constructor, the recursor is its method at the
    fields and the recursor's values at the recursive fields. **)
Theorem IndRec_iota : IndDistinct -> IndBounded -> (forall k :e K, nat_p (N k)) ->
  forall M:set -> set -> set -> set, forall k :e K, forall a :e IndArgs IndCarrier k,
  IndRec M (IndNode k a) = M k a (IndRes k (fun j => IndRec M (a j))).
assume HD: IndDistinct. assume HB: IndBounded. assume HN: forall k :e K, nat_p (N k).
let M k. assume Hk: k :e K. let a. assume Ha: a :e IndArgs IndCarrier k.
claim LC: IndNode k a :e IndCarrier.
{ exact IndNode_In HB k Hk (HN k Hk) a Ha. }
claim L1: IndRecRel M (IndNode k a) (IndRec M (IndNode k a)).
{ exact IndRec_rel M (IndNode k a) LC. }
claim L2: IndRecRel M (IndNode k a) (M k a (IndRes k (fun j => IndRec M (a j)))).
{ exact IndRecRel_closed M k Hk a Ha (fun j => IndRec M (a j))
    (fun j Hj Hrj => IndRec_rel M (a j)
       (andEL (a j :e IndCarrier) (IndIdx (a j) = Ix k j a)
          (andEL (R k j -> a j :e IndCarrier /\ IndIdx (a j) = Ix k j a) (~ R k j -> a j :e F k j a)
             (IndArgs_Fits IndCarrier k a Ha j Hj) Hrj))). }
exact IndRecRel_fun HD M (IndNode k a) LC (IndRec M (IndNode k a))
  (M k a (IndRes k (fun j => IndRec M (a j)))) L1 L2.
Qed.

(** Uniqueness: a function satisfying the constructor equations on the
    carrier is the recursor there.  Its graph is closed under the methods, so
    it contains the least such relation. **)
Theorem IndRec_unique : forall M:set -> set -> set -> set, forall f:set -> set,
  (forall k :e K, forall a :e IndArgs IndCarrier k, f (IndNode k a) = M k a (IndRes k (fun j => f (a j)))) ->
  forall x :e IndCarrier, f x = IndRec M x.
let M f.
assume Hf: forall k :e K, forall a :e IndArgs IndCarrier k, f (IndNode k a) = M k a (IndRes k (fun j => f (a j))).
let x. assume Hx: x :e IndCarrier.
claim LQ: IndRecClosed M (fun x y => f x = y).
{ let k. assume Hk: k :e K. let a. assume Ha: a :e IndArgs IndCarrier k. let r.
  assume Hr: forall j :e N k, R k j -> f (a j) = r j.
  prove f (IndNode k a) = M k a (IndRes k r).
  rewrite Hf k Hk a Ha.
  rewrite IndRes_ext k (fun j => f (a j)) r Hr.
  reflexivity. }
exact IndRec_rel M x Hx (fun x y => f x = y) LQ.
Qed.

(** Its dependent typing: the recursor lies in the motive at every member. **)
Theorem IndRec_type : IndDistinct -> IndBounded -> (forall k :e K, nat_p (N k)) ->
  forall M:set -> set -> set -> set, forall C:set -> set,
  (forall k :e K, forall a :e IndArgs IndCarrier k, forall r:set -> set,
     (forall j :e N k, R k j -> r j :e C (a j)) -> M k a (IndRes k r) :e C (IndNode k a)) ->
  forall x :e IndCarrier, IndRec M x :e C x.
assume HD: IndDistinct. assume HB: IndBounded. assume HN: forall k :e K, nat_p (N k).
let M C.
assume HM: forall k :e K, forall a :e IndArgs IndCarrier k, forall r:set -> set,
  (forall j :e N k, R k j -> r j :e C (a j)) -> M k a (IndRes k r) :e C (IndNode k a).
claim Lstep: forall k :e K, forall a :e IndArgs IndCarrier k,
  (forall j :e N k, R k j -> IndRec M (a j) :e C (a j)) -> IndRec M (IndNode k a) :e C (IndNode k a).
{ let k. assume Hk: k :e K. let a. assume Ha: a :e IndArgs IndCarrier k.
  assume IH: forall j :e N k, R k j -> IndRec M (a j) :e C (a j).
  rewrite IndRec_iota HD HB HN M k Hk a Ha.
  exact HM k Hk a Ha (fun j => IndRec M (a j)) IH.
}
exact IndCarrier_ind (fun x => IndRec M x :e C x) Lstep.
Qed.

Theorem IndRes_at : forall k, forall r:set -> set, forall j :e N k, R k j -> IndRes k r j = r j.
let k r j. assume Hj: j :e N k. assume Hr: R k j.
prove (fun j :e N k => if R k j then r j else 0) j = r j.
rewrite beta (N k) (fun j => if R k j then r j else 0) j Hj.
exact If_i_1 (R k j) (r j) 0 Hr.
Qed.

End IndFamily.

(** ---- finite sequences: one dispatch for every signature ---- **)

(** A signature's finite data (arities, recursive flags, data sorts, index
    values, argument tuples, recursor methods) is a sequence read by
    position.  The two projection laws below are all a generated instance
    uses to read it. **)

Definition SeqNil : set := 0.

Definition SeqCons : set -> set -> set := fun x s => setsum x s.

Definition SeqDrop : set -> set -> set := fun s i => nat_primrec s (fun k r => proj1 r) i.

Definition SeqAt : set -> set -> set := fun s i => proj0 (SeqDrop s i).

Theorem SeqDrop_0 : forall s, SeqDrop s 0 = s.
let s. exact nat_primrec_0 s (fun k r => proj1 r).
Qed.

Theorem SeqDrop_S : forall s, forall i, nat_p i -> SeqDrop s (ordsucc i) = proj1 (SeqDrop s i).
let s i. assume Hi: nat_p i.
exact nat_primrec_S s (fun k r => proj1 r) i Hi.
Qed.

Theorem SeqDrop_shift : forall i, nat_p i -> forall s, SeqDrop s (ordsucc i) = SeqDrop (proj1 s) i.
apply nat_ind.
- let s.
  prove SeqDrop s (ordsucc 0) = SeqDrop (proj1 s) 0.
  rewrite SeqDrop_0 (proj1 s). rewrite SeqDrop_S s 0 nat_0. rewrite SeqDrop_0 s. reflexivity.
- let i. assume Hi: nat_p i. assume IH: forall s, SeqDrop s (ordsucc i) = SeqDrop (proj1 s) i.
  let s.
  rewrite SeqDrop_S s (ordsucc i) (nat_ordsucc i Hi).
  rewrite IH s.
  rewrite SeqDrop_S (proj1 s) i Hi.
  reflexivity.
Qed.

Theorem SeqAt_0 : forall x s, SeqAt (SeqCons x s) 0 = x.
let x s.
prove proj0 (SeqDrop (setsum x s) 0) = x.
rewrite SeqDrop_0 (setsum x s).
exact proj0_pair_eq x s.
Qed.

Theorem SeqAt_S : forall x s i, nat_p i -> SeqAt (SeqCons x s) (ordsucc i) = SeqAt s i.
let x s i. assume Hi: nat_p i.
prove proj0 (SeqDrop (setsum x s) (ordsucc i)) = proj0 (SeqDrop s i).
rewrite SeqDrop_shift i Hi (setsum x s).
rewrite proj1_pair_eq x s.
reflexivity.
Qed.

(** Properties of every position below a natural, from each position. **)
Theorem Below_0 : forall P:set -> prop, forall j :e 0, P j.
let P j. assume Hj: j :e 0. prove P j. exact EmptyE j Hj (P j).
Qed.

Theorem Below_S : forall m, forall P:set -> prop, (forall j :e m, P j) -> P m -> forall j :e ordsucc m, P j.
let m P. assume Hbelow: forall j :e m, P j. assume Hm: P m.
let j. assume Hj: j :e ordsucc m.
apply ordsuccE m j Hj.
- assume H: j :e m. exact Hbelow j H.
- assume H: j = m. rewrite H. exact Hm.
Qed.

(** An argument tuple of m fields, read from a sequence. **)
Definition TupArgs : set -> set -> set := fun m s => fun j :e m => SeqAt s j.

Theorem TupArgs_at : forall m s, forall j :e m, TupArgs m s j = SeqAt s j.
let m s j. assume Hj: j :e m.
exact beta m (fun j => SeqAt s j) j Hj.
Qed.

(** Equal nodes of one constructor have equal fields: the argument
    tuples are equal (IndNode_inj), and so is each position below m. **)
Theorem IndNode_args_inj : forall K, forall T N:set -> set, forall R:set -> set -> prop, forall F Ix:set -> set -> set -> set,
  forall O:set -> set -> set, forall B,
  IndDistinct K T N R F Ix O B -> forall k :e K, forall m s t,
  IndNode K T N R F Ix O B k (TupArgs m s) = IndNode K T N R F Ix O B k (TupArgs m t) ->
  forall j :e m, SeqAt s j = SeqAt t j.
let K T N R F Ix O B. assume HD. let k. assume Hk: k :e K. let m s t.
assume H: IndNode K T N R F Ix O B k (TupArgs m s) = IndNode K T N R F Ix O B k (TupArgs m t).
let j. assume Hj: j :e m.
claim La: TupArgs m s = TupArgs m t.
{ exact andER (k = k) (TupArgs m s = TupArgs m t)
    (IndNode_inj K T N R F Ix O B HD k Hk k Hk (TupArgs m s) (TupArgs m t) H). }
rewrite <- TupArgs_at m s j Hj.
rewrite <- TupArgs_at m t j Hj.
rewrite La.
reflexivity.
Qed.
