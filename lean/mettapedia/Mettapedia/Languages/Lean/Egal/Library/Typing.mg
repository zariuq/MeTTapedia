(** Typing in the interpretation: products of propositions are propositions
    (impredicativity), dependent products and applications stay in a
    universe, and the small facts about functions, propositions and proofs
    the generated typing proofs cite.  Loaded after the general
    construction. **)

(** A product of propositions is a proposition (impredicativity): each of its
    elements is a set of pairs with no pair in it. **)
Theorem LeanPi_prop : forall X, forall Y:set -> set, (forall x :e X, Y x :e LeanProp) -> (Pi_ x :e X, Y x) :e LeanProp.
let X Y. assume HY: forall x :e X, Y x :e LeanProp.
apply PowerI 1 (Pi_ x :e X, Y x).
let f. assume Hf: f :e Pi_ x :e X, Y x.
prove f :e 1.
apply PiE X Y f Hf.
assume Hpairs: forall u :e f, pair_p u /\ u 0 :e X.
assume Hvals: forall x :e X, f x :e Y x.
claim Lf: f = 0.
{ apply Empty_eq f.
  let u. assume Hu: u :e f.
  apply Hpairs u Hu.
  assume Hup: pair_p u. assume Hu0: u 0 :e X.
  claim L1: f (u 0) :e 1.
  { exact PowerE 1 (Y (u 0)) (HY (u 0) Hu0) (f (u 0)) (Hvals (u 0) Hu0). }
  claim L2: f (u 0) = 0.
  { exact SingE 0 (f (u 0)) (Subq_1_Sing0 (f (u 0)) L1). }
  claim L3: u 1 :e f (u 0).
  { exact pair_p_In_ap u f Hup Hu. }
  exact EmptyE (u 1) (In_eq_r (u 1) (f (u 0)) 0 L2 L3).
}
rewrite Lf. exact In_0_1.
Qed.

(** Its truth: the product holds when each factor does; the proof is the
    empty function. **)
Theorem LeanPi_prop_intro : forall X, forall Y:set -> set, (forall x :e X, 0 :e Y x) -> 0 :e (Pi_ x :e X, Y x).
let X Y. assume H0: forall x :e X, 0 :e Y x.
claim L1: (fun x :e X => 0) :e (Pi_ x :e X, Y x).
{ exact lam_Pi X Y (fun x => 0) H0. }
claim L2: (fun x :e X => 0) = 0.
{ apply Empty_eq.
  let u. assume Hu: u :e (fun x :e X => 0).
  apply lamE X (fun x => 0) u Hu.
  let x. assume Hx. apply Hx.
  assume Hx1: x :e X. assume Hx2: exists y :e 0, u = setsum x y.
  apply Hx2.
  let y. assume Hy. apply Hy.
  assume Hy0: y :e 0.
  assume _: u = setsum x y.
  exact EmptyE y Hy0.
}
exact In_eq_l (fun x :e X => 0) 0 (Pi_ x :e X, Y x) L2 L1.
Qed.

(** ---- dependent products in a universe ---- **)

Theorem LeanPi_LeanUniv : forall n, nat_p n -> forall X :e LeanUniv n, forall Y:set -> set,
  (forall x :e X, Y x :e LeanUniv n) -> (Pi_ x :e X, Y x) :e LeanUniv n.
let n. assume Hn: nat_p n.
exact ZF_Pi_In (LeanUniv n) (LeanUniv_TransSet n Hn) (LeanUniv_ZF_closed n Hn).
Qed.

Theorem LeanApp : forall X, forall Y:set -> set, forall f :e (Pi_ x :e X, Y x), forall a :e X, f a :e Y a.
let X Y f. assume Hf. let a. assume Ha.
exact ap_Pi X Y f a Hf Ha.
Qed.

Theorem LeanLam : forall X, forall Y:set -> set, forall F:set -> set,
  (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
exact lam_Pi.
Qed.

Theorem LeanBeta : forall X, forall F:set -> set, forall a :e X, (fun x :e X => F x) a = F a.
let X F a. assume Ha.
exact beta X F a Ha.
Qed.

(** Control: dependent application.  The type of the result depends on the
    argument, and a constant type would be wrong. **)
Theorem control_dep_lam : (fun n :e omega => n) :e (Pi_ n :e omega, ordsucc n).
exact lam_Pi omega ordsucc (fun n => n) (fun n Hn => ordsuccI2 n).
Qed.

Theorem control_dep_app : forall m :e omega, (fun n :e omega => n) m :e ordsucc m.
let m. assume Hm.
exact LeanApp omega ordsucc (fun n :e omega => n) control_dep_lam m Hm.
Qed.

Theorem control_dep_not_constant : ~ (forall m :e omega, (fun n :e omega => n) m :e 1).
assume H: forall m :e omega, (fun n :e omega => n) m :e 1.
claim L1: (fun n :e omega => n) 1 :e 1.
{ exact H 1 (nat_p_omega 1 nat_1). }
claim L2: (fun n :e omega => n) 1 = 1.
{ exact beta omega (fun n => n) 1 (nat_p_omega 1 nat_1). }
exact In_irref 1 (In_eq_l ((fun n :e omega => n) 1) 1 1 L2 L1).
Qed.


(** A set function applied to any argument stays in a universe holding 0
    and its values: inside the domain by beta, outside it is 0. **)
Theorem lam_ap_In : forall U, 0 :e U -> forall X, forall F:set -> set,
  (forall x :e X, F x :e U) -> forall x, (fun x :e X => F x) x :e U.
let U. assume H0: 0 :e U. let X F. assume HF: forall x :e X, F x :e U. let x.
apply xm (x :e X).
- assume Hx: x :e X. rewrite beta X F x Hx. exact HF x Hx.
- assume Hx: x /:e X. rewrite beta0 X F x Hx. exact H0.
Qed.

Theorem LeanUniv_0_In : forall u, nat_p u -> 0 :e LeanUniv u.
let u. assume Hu: nat_p u.
exact LeanUniv_TransSet u Hu omega (omega_In_LeanUniv u Hu) 0 (nat_p_omega 0 nat_0).
Qed.

Theorem LeanUniv_nat_In : forall u, nat_p u -> forall n, nat_p n -> n :e LeanUniv u.
let u. assume Hu: nat_p u. let n. assume Hn: nat_p n.
exact LeanUniv_TransSet u Hu omega (omega_In_LeanUniv u Hu) n (nat_p_omega n Hn).
Qed.

(** A constructor node lies in a universe that holds its tag, its index and
    its argument tuple; the tuple, when the universe holds its length and
    every entry.  Family indices are read as nodes, so their universe
    membership comes from their fields'. **)
Theorem IndNode_univ : forall U, TransSet U -> ZF_closed U ->
  forall K:set, forall T:set -> set, forall N:set -> set, forall R:set -> set -> prop,
  forall F:set -> set -> set -> set, forall Ix:set -> set -> set -> set, forall O:set -> set -> set, forall B:set,
  forall k a, T k :e U -> O k a :e U -> a :e U -> IndNode K T N R F Ix O B k a :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U.
let K T N R F Ix O B k a. assume HT: T k :e U. assume HO: O k a :e U. assume Ha: a :e U.
prove setsum (setsum (T k) (O k a)) a :e U.
exact ZF_pair_In U Ht Hz (setsum (T k) (O k a)) (ZF_pair_In U Ht Hz (T k) HT (O k a) HO) a Ha.
Qed.

Theorem TupArgs_univ : forall U, TransSet U -> ZF_closed U -> forall m :e U, forall s,
  (forall j :e m, SeqAt s j :e U) -> TupArgs m s :e U.
let U. assume Ht: TransSet U. assume Hz: ZF_closed U. let m. assume Hm: m :e U.
let s. assume Hs: forall j :e m, SeqAt s j :e U.
prove (fun j :e m => SeqAt s j) :e U.
exact ZF_lam_In U Ht Hz m Hm (fun j => SeqAt s j) Hs.
Qed.

(** A family with two indices has its fiber at their pair; the motive of its
    recursor takes the two indices, read from the pair by its projections. **)
Theorem In_motive2_pair : forall C:set -> set -> set -> set, forall x y t z,
  z :e C x y t -> z :e C (proj0 (setsum x y)) (proj1 (setsum x y)) t.
let C x y t z. assume H: z :e C x y t.
apply In_fam_eq (fun v => C (proj0 (setsum x y)) v t) y (proj1 (setsum x y)) (eq_sym_i (proj1 (setsum x y)) y (proj1_pair_eq x y)) z.
exact In_fam_eq (fun v => C v y t) x (proj0 (setsum x y)) (eq_sym_i (proj0 (setsum x y)) x (proj0_pair_eq x y)) z H.
Qed.

Theorem In_motive2_unpair : forall C:set -> set -> set -> set, forall x y t z,
  z :e C (proj0 (setsum x y)) (proj1 (setsum x y)) t -> z :e C x y t.
let C x y t z. assume H: z :e C (proj0 (setsum x y)) (proj1 (setsum x y)) t.
apply In_fam_eq (fun v => C x v t) (proj1 (setsum x y)) y (proj1_pair_eq x y) z.
exact In_fam_eq (fun v => C v (proj1 (setsum x y)) t) (proj0 (setsum x y)) x (proj0_pair_eq x y) z H.
Qed.

(** The empty set is a function into Y when every Y x contains it. **)
Theorem Pi_0_In : forall X:set, forall Y:set -> set, (forall x :e X, 0 :e Y x) -> 0 :e (Pi_ x :e X, Y x).
let X Y. assume H: forall x :e X, 0 :e Y x.
prove 0 :e {f :e Power (Sigma_ x :e X, Union (Y x)) | forall x :e X, f x :e Y x}.
apply SepI (Power (Sigma_ x :e X, Union (Y x))) (fun f => forall x :e X, f x :e Y x) 0 (Empty_In_Power (Sigma_ x :e X, Union (Y x))).
let x. assume Hx: x :e X. rewrite ap_const_0 x. exact H x Hx.
Qed.

(** Reflexivity of equality, as a term: the proof of a proof argument a = a. **)
Theorem Lean_eq_refl : forall x:set, x = x.
let x. reflexivity.
Qed.

(** A proposition P read as a set: {z :e 1 | P} is a proposition (a subset of 1). **)
Theorem Lean_sep1_prop : forall P:prop, {z :e 1 | P} :e LeanProp.
let P. exact PowerI 1 {z :e 1 | P} (Sep_Subq 1 (fun z => P)).
Qed.

(** Constructor proof fields keep their condition as a subset of the singleton. **)
Definition Lean_ProofField : set -> set := fun P => {z :e 1 | z :e P}.

Theorem Lean_ProofField_prop : forall P, Lean_ProofField P :e LeanProp.
let P. exact PowerI 1 (Lean_ProofField P) (Sep_Subq 1 (fun z => z :e P)).
Qed.

Theorem Lean_ProofField_intro : forall P, 0 :e P -> 0 :e Lean_ProofField P.
let P. assume HP: 0 :e P.
exact SepI 1 (fun z => z :e P) 0 In_0_1 HP.
Qed.

Theorem Lean_ProofField_sound : forall P z, z :e Lean_ProofField P -> z :e P.
let P z. assume Hz: z :e Lean_ProofField P.
exact SepE2 1 (fun z => z :e P) z Hz.
Qed.

(** A constructor stores its full field tuple, including proof positions. **)
Definition Lean_RecordField : set -> set -> set := fun j record => (proj1 record) j.

Theorem Lean_RecordField_pair : forall tag index args j,
  Lean_RecordField j (setsum (setsum tag index) args) = args j.
let tag index args j.
prove (proj1 (setsum (setsum tag index) args)) j = args j.
rewrite proj1_pair_eq (setsum tag index) args. reflexivity.
Qed.

Theorem Lean_RecordField_tuple : forall tag index n s j, j :e n ->
  Lean_RecordField j (setsum (setsum tag index) (TupArgs n s)) = SeqAt s j.
let tag index n s j. assume Hj: j :e n.
rewrite Lean_RecordField_pair tag index (TupArgs n s) j.
exact TupArgs_at n s j Hj.
Qed.

(** A two-argument operation as a value of the interpreted function type. **)
Definition Lean_BinaryMap : set -> set -> (set -> set -> set) -> set :=
  fun X Y f => fun x :e X => fun y :e Y => f x y.

Theorem Lean_BinaryMap_typed : forall X Y Z, forall f:set -> set -> set,
  (forall x :e X, forall y :e Y, f x y :e Z) ->
  Lean_BinaryMap X Y f :e (Pi_ x :e X, (Pi_ y :e Y, Z)).
let X Y Z f. assume H: forall x :e X, forall y :e Y, f x y :e Z.
exact lam_Pi X (fun _ => Pi_ y :e Y, Z) (fun x => fun y :e Y => f x y)
  (fun x Hx => lam_Pi Y (fun _ => Z) (f x) (fun y Hy => H x Hx y Hy)).
Qed.

Theorem Lean_BinaryMap_apply : forall X Y, forall f:set -> set -> set,
  forall x :e X, forall y :e Y, (Lean_BinaryMap X Y f) x y = f x y.
let X Y f x. assume Hx: x :e X. let y. assume Hy: y :e Y.
prove ((fun x :e X => fun y :e Y => f x y) x) y = f x y.
rewrite beta X (fun x => fun y :e Y => f x y) x Hx.
exact beta Y (f x) y Hy.
Qed.

(** A proposition lies in every universe: the universe is transitive and contains LeanProp. **)
Theorem Lean_prop_In_LeanUniv : forall n, nat_p n -> forall p :e LeanProp, p :e LeanUniv n.
let n. assume Hn: nat_p n. let p. assume Hp: p :e LeanProp.
exact LeanUniv_TransSet n Hn LeanProp (LeanProp_In_LeanUniv n Hn) p Hp.
Qed.
