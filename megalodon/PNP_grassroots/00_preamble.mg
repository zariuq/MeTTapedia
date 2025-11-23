(* ========================================================================= *)
(* Self-Contained Foundations for P ≠ NP Formalization                       *)
(* ========================================================================= *)
(*                                                                           *)
(* AXIOM SOURCES AND FOUNDATIONS                                             *)
(* =============================                                             *)
(*                                                                           *)
(* This file uses a Tarski-Grothendieck style set theory as implemented in   *)
(* Megalodon/Egal. Key references:                                           *)
(*                                                                           *)
(* [TG] Tarski, A. (1938). "Über unerreichbare Kardinalzahlen"               *)
(*      Fundamenta Mathematicae 30: 68-89                                    *)
(*      - Foundation for Tarski-Grothendieck set theory axioms               *)
(*                                                                           *)
(* [ZFC] Zermelo, E. (1908). "Untersuchungen über die Grundlagen der         *)
(*       Mengenlehre I". Mathematische Annalen 65: 261-281                   *)
(*       - Pairing, Union, Power set, Empty set axioms                       *)
(*                                                                           *)
(* [VN] von Neumann, J. (1923). "Zur Einführung der transfiniten Zahlen"     *)
(*      Acta Szeged 1: 199-208                                               *)
(*      - Von Neumann ordinal representation: n = {0, 1, ..., n-1}           *)
(*      - ordsucc n = n ∪ {n}                                                *)
(*                                                                           *)
(* [EM] Excluded middle (classical logic) - standard in classical math       *)
(*      Required for reasoning by contradiction in complexity theory         *)
(*                                                                           *)
(* [Eps] Hilbert's epsilon operator (choice)                                 *)
(*       Hilbert, D. & Bernays, P. (1939). Grundlagen der Mathematik II      *)
(*                                                                           *)
(* ========================================================================= *)

Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.

Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
Definition neq : A->A->prop := fun x y:A => ~eq x y.
End Eq.
Infix = 502 := eq.
Infix <> 502 := neq.

Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.
Binder+ exists , := ex.

Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Definition iff : prop -> prop -> prop := fun A B:prop => and (A -> B) (B -> A).

Infix /\ 780 left := and.
Infix \/ 785 left := or.
Infix <-> 805 := iff.

(* Parameter Eps_i "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" *)
Parameter Eps_i : (set->prop)->set.

Parameter In : set->set->prop.

(* Parameter Empty "e2a83319facad3a3d8ff453f4ef821d9da495e56a623695546bb7d7ac333f3fe" *)
Parameter Empty : set.

(* Parameter Union "844774016d959cff921a3292054b30b52f175032308aa11e418cb73f5fef3d54" *)
Parameter Union : set->set.

(* Parameter Power "2a38dbb37506341b157c11dddf8eb7d8404ce97eb50d5e940b23d5094ae39d70" *)
Parameter Power : set->set.

Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.

Parameter UnivOf : set->set.

(* Parameter UPair "80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d" "74243828e4e6c9c0b467551f19c2ddaebf843f72e2437cc2dea41d079a31107f" *)
Parameter UPair : set -> set -> set.
Notation SetEnum2 UPair.
Axiom UPairI1 : forall y z:set, y :e {y,z}.
Axiom UPairI2 : forall y z:set, z :e {y,z}.
Axiom UPairE : forall x y z:set, x :e {y,z} -> x = y \/ x = z.

Definition Sing : set -> set := fun x => {x,x}.
Notation SetEnum1 Sing.

Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.
Infix :\/: 345 left := binunion.
Axiom binunionI1 : forall X Y z:set, z :e X -> z :e X :\/: Y.
Axiom binunionI2 : forall X Y z:set, z :e Y -> z :e X :\/: Y.
Axiom binunionE : forall X Y z:set, z :e X :\/: Y -> z :e X \/ z :e Y.

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" *)
Definition ordsucc : set->set := fun x:set => x :\/: {x}.

Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.

(* Basic subset properties - trivially provable from definition *)
Theorem Subq_ref : forall A:set, A c= A.
let A. let x. assume H: x :e A. exact H.
Qed.

Theorem Subq_tra : forall A B C:set, A c= B -> B c= C -> A c= C.
let A B C. assume Hab: A c= B. assume Hbc: B c= C.
let x. assume Hx: x :e A.
exact (Hbc x (Hab x Hx)).
Qed.

Binder+ exists , := ex; and.

Notation Nat Empty ordsucc.
Definition nat_p : set->prop := fun n:set => forall p:set->prop, p 0 -> (forall x:set, p x -> p (ordsucc x)) -> p n.
(* Parameter omega "54f5b491560ccfc13fb2334a544117bd0f7903fe3f22751e4485e0b838a1016c" "80d24834aa9f66bdb9a5e1bbd38abd569c0980b113318e3a60b061de5affc484" *)
Parameter omega : set.
Axiom omega_iff : forall x, x :e omega <-> nat_p x.

Section FE.
Variable A B : SType.
Axiom func_ext : forall f g : A -> B , (forall x : A , f x = g x) -> f = g.
End FE.
Axiom prop_ext : forall p q:prop, iff p q -> p = q.
Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.

Axiom Eps_i_ax : forall P:set->prop, forall x:set, P x -> P (Eps_i P).

Definition nIn : set->set->prop := fun x X => ~In x X.
Infix /:e 502 := nIn.

Axiom EmptyE : forall x, x /:e Empty.
Axiom UnionEq : forall X x, x :e Union X <-> exists Y, x :e Y /\ Y :e X.
Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.
Axiom ReplEq : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} <-> exists x :e A, y = F x.

Axiom ordsuccI1 : forall x:set, x c= ordsucc x.
Axiom ordsuccI2 : forall x:set, x :e ordsucc x.
Axiom ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.
Axiom neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
Axiom ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.

Axiom nat_0 : nat_p 0.
Axiom nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
Axiom nat_ind : forall p:set->prop, p 0 -> (forall n, nat_p n -> p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
Axiom nat_p_omega : forall n:set, nat_p n -> n :e omega.
Axiom omega_nat_p : forall n :e omega, nat_p n.

Theorem nat_1 : nat_p 1. exact (nat_ordsucc 0 nat_0). Qed.
Theorem nat_2 : nat_p 2. exact (nat_ordsucc 1 nat_1). Qed.

(* --- Derived ordinal membership facts --- *)
(* These were previously axioms but are provable from ordsucc axioms *)

(* Proof: 1 = ordsucc 0, and ordsuccI2 gives x :e ordsucc x *)
Theorem In_0_1 : 0 :e 1.
exact (ordsuccI2 0).
Qed.

(* Proof: 0 :e 1 and 1 c= 2 by ordsuccI1, so 0 :e 2 *)
Theorem In_0_2 : 0 :e 2.
exact (ordsuccI1 1 0 In_0_1).
Qed.

(* Proof: 2 = ordsucc 1, and ordsuccI2 gives 1 :e ordsucc 1 = 2 *)
Theorem In_1_2 : 1 :e 2.
exact (ordsuccI2 1).
Qed.

(* Proof: neq_0_ordsucc says 0 <> ordsucc a for any a; take a=0 *)
Theorem neq_0_1 : 0 <> 1.
exact (neq_0_ordsucc 0).
Qed.

(* Proof: from neq_0_1 and symmetry of inequality *)
Theorem neq_1_0 : 1 <> 0.
assume H: 1 = 0.
claim L: 0 = 1. { symmetry. exact H. }
exact (neq_0_1 L).
Qed.

Axiom FalseE : False -> forall p:prop, p.

(* Convenient form of false elimination *)
Definition False_rect : forall p:prop, False -> p :=
  fun p H => FalseE H p.

Axiom TrueI : True.
Axiom andI : forall A B:prop, A -> B -> A /\ B.
Axiom andEL : forall A B:prop, A /\ B -> A.
Axiom andER : forall A B:prop, A /\ B -> B.
Axiom orIL : forall A B:prop, A -> A \/ B.
Axiom orIR : forall A B:prop, B -> A \/ B.
Axiom orE : forall A B C:prop, (A -> C) -> (B -> C) -> A \/ B -> C.
Axiom iffI : forall A B:prop, (A -> B) -> (B -> A) -> A <-> B.

Definition If_i : prop->set->set->set := fun p x y => Eps_i (fun z:set => p /\ z = x \/ ~p /\ z = y).
Notation IfThenElse If_i.

Axiom If_i_0 : forall p:prop, forall x y:set, ~p -> (if p then x else y) = y.
Axiom If_i_1 : forall p:prop, forall x y:set, p -> (if p then x else y) = x.

Parameter pair : set -> set -> set.
Parameter ap : set -> set -> set.
Parameter Sigma : set -> (set -> set) -> set.

Notation SetImplicitOp ap.
Notation SetLam Sigma.

Axiom beta : forall X:set, forall F:set -> set, forall x:set, x :e X -> (fun x :e X => F x) x = F x.

(* Pair projection axioms *)
Axiom ap_pair_0 : forall x y:set, ap (pair x y) 0 = x.
Axiom ap_pair_1 : forall x y:set, ap (pair x y) 1 = y.

(* Excluded middle for classical reasoning *)
Axiom classic : forall p:prop, p \/ ~p.

Definition TransSet : set->prop := fun U:set => forall x :e U, x c= U.
Definition ordinal : set->prop := fun alpha:set => TransSet alpha /\ forall beta :e alpha, TransSet beta.

Axiom nat_p_ordinal : forall n:set, nat_p n -> ordinal n.

Definition nat_primrec_F : set -> (set -> set) -> set :=
  fun z f X g => if exists n :e X, nat_p n /\ X = ordsucc n
                 then f (Eps_i (fun n => n :e X /\ nat_p n /\ X = ordsucc n))
                        (g (Eps_i (fun n => n :e X /\ nat_p n /\ X = ordsucc n)))
                 else z.

Parameter In_rec_i : (set->(set->set)->set)->set->set.
Axiom In_rec_i_eq : forall F:set->(set->set)->set,
  (forall X:set, forall g h:set->set, (forall x :e X, g x = h x) -> F X g = F X h) ->
  forall X:set, In_rec_i F X = F X (In_rec_i F).

Definition nat_primrec : set -> (set -> set -> set) -> set -> set :=
  fun z f => In_rec_i (fun X g => if exists n :e X, nat_p n /\ X = ordsucc n
                                  then f (Eps_i (fun n => n :e X /\ nat_p n /\ X = ordsucc n))
                                         (g (Eps_i (fun n => n :e X /\ nat_p n /\ X = ordsucc n)))
                                  else z).

Axiom nat_primrec_0 : forall z:set, forall f:set->set->set, nat_primrec z f 0 = z.
Axiom nat_primrec_S : forall z:set, forall f:set->set->set, forall n:set, nat_p n ->
  nat_primrec z f (ordsucc n) = f n (nat_primrec z f n).

Definition add_nat : set->set->set := fun n m:set => nat_primrec n (fun _ r => ordsucc r) m.
Infix + 360 right := add_nat.

(* Natural number addition axioms *)
(* Source: Grassmann, H. (1861). Lehrbuch der Arithmetik. *)
(* These define addition via primitive recursion and establish its algebraic properties. *)

Axiom add_nat_0R : forall n:set, n + 0 = n.
Axiom add_nat_SR : forall n m:set, nat_p m -> n + ordsucc m = ordsucc (n + m).
Axiom add_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n + m).

(* Additional arithmetic properties - provable by induction but stated for convenience *)
(* Source: Standard results in Peano arithmetic *)
Axiom add_nat_0L : forall n:set, nat_p n -> 0 + n = n.
Axiom add_nat_com : forall m:set, nat_p m -> forall n:set, nat_p n -> m + n = n + m.
Axiom add_nat_asso : forall a:set, nat_p a -> forall b:set, nat_p b -> forall c:set, nat_p c ->
  (a + b) + c = a + (b + c).

Definition mul_nat : set->set->set := fun n m:set => nat_primrec 0 (fun _ r => n + r) m.
Infix * 355 right := mul_nat.

Axiom mul_nat_0R : forall n:set, n * 0 = 0.
Axiom mul_nat_SR : forall n m:set, nat_p m -> n * ordsucc m = n + n * m.
Axiom mul_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n * m).

Definition exp_nat : set -> set -> set := fun n m => nat_primrec 1 (fun _ r => n * r) m.

Axiom exp_nat_0 : forall n:set, exp_nat n 0 = 1.
Axiom exp_nat_S : forall n m:set, nat_p m -> exp_nat n (ordsucc m) = n * exp_nat n m.

Parameter setexp : set -> set -> set.
Notation SetExp setexp.
Axiom setexp_In : forall X Y x, x :e X :^: Y <-> (forall y :e Y, ap x y :e X).

Parameter setprod : set -> set -> set.
Notation SetProd setprod.
Axiom setprod_In : forall X Y z, z :e X :*: Y <-> exists x :e X, exists y :e Y, z = (x,y).

Definition is_bit : set -> prop := fun b => b = 0 \/ b = 1.
Definition Bits : set := 2.

Theorem bit_0 : is_bit 0. apply orIL. reflexivity. Qed.
Theorem bit_1 : is_bit 1. apply orIR. reflexivity. Qed.

Theorem bit_in_Bits : forall b, is_bit b -> b :e Bits.
let b. assume H: is_bit b.
apply orE (b = 0) (b = 1) (b :e Bits).
- assume H0: b = 0. rewrite H0. exact In_0_2.
- assume H1: b = 1. rewrite H1. exact In_1_2.
- exact H.
Qed.

Theorem Bits_is_bit : forall b :e Bits, is_bit b.
let b. assume Hb: b :e 2.
apply ordsuccE 1 b Hb.
- assume H: b :e 1.
  apply ordsuccE 0 b H.
  + assume H2: b :e 0. apply FalseE. exact (EmptyE b H2).
  + assume H2: b = 0. apply orIL. exact H2.
- assume H: b = 1. apply orIR. exact H.
Qed.

Definition xor : set -> set -> set :=
  fun a b => if a = b then 0 else 1.

Theorem xor_0_0 : xor 0 0 = 0.
claim L: 0 = 0. { reflexivity. }
exact (If_i_1 (0 = 0) 0 1 L).
Qed.

Theorem xor_0_1 : xor 0 1 = 1.
exact (If_i_0 (0 = 1) 0 1 neq_0_1).
Qed.

Theorem xor_1_0 : xor 1 0 = 1.
exact (If_i_0 (1 = 0) 0 1 neq_1_0).
Qed.

Theorem xor_1_1 : xor 1 1 = 0.
claim L: 1 = 1. { reflexivity. }
exact (If_i_1 (1 = 1) 0 1 L).
Qed.

Theorem xor_is_bit : forall a b, is_bit a -> is_bit b -> is_bit (xor a b).
let a b. assume Ha: is_bit a. assume Hb: is_bit b.
apply orE (a = 0) (a = 1) (is_bit (xor a b)).
- assume Ha0: a = 0. rewrite Ha0.
  apply orE (b = 0) (b = 1) (is_bit (xor 0 b)).
  + assume Hb0: b = 0. rewrite Hb0. rewrite xor_0_0. exact bit_0.
  + assume Hb1: b = 1. rewrite Hb1. rewrite xor_0_1. exact bit_1.
  + exact Hb.
- assume Ha1: a = 1. rewrite Ha1.
  apply orE (b = 0) (b = 1) (is_bit (xor 1 b)).
  + assume Hb0: b = 0. rewrite Hb0. rewrite xor_1_0. exact bit_1.
  + assume Hb1: b = 1. rewrite Hb1. rewrite xor_1_1. exact bit_0.
  + exact Hb.
- exact Ha.
Qed.

Theorem xor_comm : forall a b, is_bit a -> is_bit b -> xor a b = xor b a.
let a b. assume Ha: is_bit a. assume Hb: is_bit b.
apply orE (a = 0) (a = 1) (xor a b = xor b a).
- assume Ha0: a = 0. rewrite Ha0.
  apply orE (b = 0) (b = 1) (xor 0 b = xor b 0).
  + assume Hb0: b = 0. rewrite Hb0. reflexivity.
  + assume Hb1: b = 1. rewrite Hb1. rewrite xor_0_1. rewrite xor_1_0. reflexivity.
  + exact Hb.
- assume Ha1: a = 1. rewrite Ha1.
  apply orE (b = 0) (b = 1) (xor 1 b = xor b 1).
  + assume Hb0: b = 0. rewrite Hb0. rewrite xor_1_0. rewrite xor_0_1. reflexivity.
  + assume Hb1: b = 1. rewrite Hb1. reflexivity.
  + exact Hb.
- exact Ha.
Qed.

Theorem xor_0_r : forall a, is_bit a -> xor a 0 = a.
let a. assume Ha: is_bit a.
apply orE (a = 0) (a = 1) (xor a 0 = a).
- assume H: a = 0. rewrite H. exact xor_0_0.
- assume H: a = 1. rewrite H. exact xor_1_0.
- exact Ha.
Qed.

Theorem xor_self : forall a, is_bit a -> xor a a = 0.
let a. assume Ha: is_bit a.
apply orE (a = 0) (a = 1) (xor a a = 0).
- assume H: a = 0. rewrite H. exact xor_0_0.
- assume H: a = 1. rewrite H. exact xor_1_1.
- exact Ha.
Qed.

Theorem xor_in_Bits : forall a b, is_bit a -> is_bit b -> xor a b :e Bits.
let a b. assume Ha: is_bit a. assume Hb: is_bit b.
exact (bit_in_Bits (xor a b) (xor_is_bit a b Ha Hb)).
Qed.

Theorem xor_0_l : forall a, is_bit a -> xor 0 a = a.
let a. assume Ha: is_bit a.
apply Ha.
- assume H: a = 0. rewrite H. exact xor_0_0.
- assume H: a = 1. rewrite H. exact xor_0_1.
Qed.

Theorem xor_assoc : forall a b c, is_bit a -> is_bit b -> is_bit c ->
  xor (xor a b) c = xor a (xor b c).
let a b c. assume Ha: is_bit a. assume Hb: is_bit b. assume Hc: is_bit c.
apply Ha.
- assume Ha0: a = 0. rewrite Ha0.
  apply Hb.
  + assume Hb0: b = 0. rewrite Hb0.
    apply Hc.
    * assume Hc0: c = 0. rewrite Hc0. rewrite xor_0_0. rewrite xor_0_0. rewrite xor_0_0. reflexivity.
    * assume Hc1: c = 1. rewrite Hc1. rewrite xor_0_0. rewrite xor_0_1. rewrite xor_0_1. reflexivity.
  + assume Hb1: b = 1. rewrite Hb1.
    apply Hc.
    * assume Hc0: c = 0. rewrite Hc0. rewrite xor_0_1. rewrite xor_1_0. rewrite xor_1_0. reflexivity.
    * assume Hc1: c = 1. rewrite Hc1. rewrite xor_0_1. rewrite xor_1_1. rewrite xor_1_1. rewrite xor_0_0. reflexivity.
- assume Ha1: a = 1. rewrite Ha1.
  apply Hb.
  + assume Hb0: b = 0. rewrite Hb0.
    apply Hc.
    * assume Hc0: c = 0. rewrite Hc0. rewrite xor_1_0. rewrite xor_1_0. rewrite xor_0_0. reflexivity.
    * assume Hc1: c = 1. rewrite Hc1. rewrite xor_1_0. rewrite xor_1_1. rewrite xor_0_1. rewrite xor_1_0. reflexivity.
  + assume Hb1: b = 1. rewrite Hb1.
    apply Hc.
    * assume Hc0: c = 0. rewrite Hc0. rewrite xor_1_1. rewrite xor_0_0. rewrite xor_1_0. rewrite xor_1_0. reflexivity.
    * assume Hc1: c = 1. rewrite Hc1. rewrite xor_1_1. rewrite xor_0_1. rewrite xor_1_1. rewrite xor_1_0. reflexivity.
Qed.

(* --- Bit-wise AND for F_2 multiplication --- *)

Definition bit_and : set -> set -> set :=
  fun a b => if a = 1 /\ b = 1 then 1 else 0.

Theorem bit_and_0_0 : bit_and 0 0 = 0.
prove (if 0 = 1 /\ 0 = 1 then 1 else 0) = 0.
claim L: ~(0 = 1 /\ 0 = 1).
{ assume H. apply H. assume H1: 0 = 1. exact (neq_0_1 H1). }
exact (If_i_0 (0 = 1 /\ 0 = 1) 1 0 L).
Qed.

Theorem bit_and_0_1 : bit_and 0 1 = 0.
prove (if 0 = 1 /\ 1 = 1 then 1 else 0) = 0.
claim L: ~(0 = 1 /\ 1 = 1).
{ assume H. apply H. assume H1: 0 = 1. exact (neq_0_1 H1). }
exact (If_i_0 (0 = 1 /\ 1 = 1) 1 0 L).
Qed.

Theorem bit_and_1_0 : bit_and 1 0 = 0.
prove (if 1 = 1 /\ 0 = 1 then 1 else 0) = 0.
claim L: ~(1 = 1 /\ 0 = 1).
{ assume H. apply H. assume _ H1: 0 = 1. exact (neq_0_1 H1). }
exact (If_i_0 (1 = 1 /\ 0 = 1) 1 0 L).
Qed.

Theorem bit_and_1_1 : bit_and 1 1 = 1.
prove (if 1 = 1 /\ 1 = 1 then 1 else 0) = 1.
claim L: 1 = 1 /\ 1 = 1.
{ apply andI. reflexivity. reflexivity. }
exact (If_i_1 (1 = 1 /\ 1 = 1) 1 0 L).
Qed.

Theorem bit_and_is_bit : forall a b, is_bit a -> is_bit b -> is_bit (bit_and a b).
let a b. assume Ha: is_bit a. assume Hb: is_bit b.
apply Ha.
- assume Ha0: a = 0. rewrite Ha0.
  apply Hb.
  + assume Hb0: b = 0. rewrite Hb0. rewrite bit_and_0_0. exact bit_0.
  + assume Hb1: b = 1. rewrite Hb1. rewrite bit_and_0_1. exact bit_0.
- assume Ha1: a = 1. rewrite Ha1.
  apply Hb.
  + assume Hb0: b = 0. rewrite Hb0. rewrite bit_and_1_0. exact bit_0.
  + assume Hb1: b = 1. rewrite Hb1. rewrite bit_and_1_1. exact bit_1.
Qed.

Definition BitString : set -> set -> prop :=
  fun n s => forall i :e n, ap s i :e Bits.

(* BitStrings can be defined when Sep is available *)
(* Definition BitStrings : set -> set := fun n => {s :e Bits :^: n | BitString n s}. *)

Theorem BitString_ap_bit : forall n s, BitString n s -> forall i :e n, is_bit (ap s i).
let n s. assume H: BitString n s.
let i. assume Hi: i :e n.
exact (Bits_is_bit (ap s i) (H i Hi)).
Qed.

Definition zero_vector : set -> set :=
  fun n => fun i :e n => 0.

Definition ones_vector : set -> set :=
  fun n => fun i :e n => 1.

Theorem zero_vector_BitString : forall n, nat_p n -> BitString n (zero_vector n).
let n. assume Hn: nat_p n.
let i. assume Hi: i :e n.
rewrite beta n (fun _ => 0) i Hi.
exact In_0_2.
Qed.

Definition vec_xor : set -> set -> set -> set :=
  fun n v1 v2 => fun i :e n => xor (ap v1 i) (ap v2 i).

Theorem vec_xor_BitString : forall n v1 v2,
  BitString n v1 -> BitString n v2 -> BitString n (vec_xor n v1 v2).
let n v1 v2. assume H1: BitString n v1. assume H2: BitString n v2.
let i. assume Hi: i :e n.
rewrite beta n (fun j => xor (ap v1 j) (ap v2 j)) i Hi.
apply bit_in_Bits.
apply xor_is_bit.
- exact (Bits_is_bit (ap v1 i) (H1 i Hi)).
- exact (Bits_is_bit (ap v2 i) (H2 i Hi)).
Qed.

Theorem vec_xor_self : forall n v, nat_p n -> BitString n v ->
  vec_xor n v v = zero_vector n.
let n v. assume Hn: nat_p n. assume Hv: BitString n v.
apply func_ext n set.
let i. assume Hi: i :e n.
rewrite beta n (fun j => xor (ap v j) (ap v j)) i Hi.
rewrite beta n (fun _ => 0) i Hi.
apply xor_self.
exact (Bits_is_bit (ap v i) (Hv i Hi)).
Qed.
