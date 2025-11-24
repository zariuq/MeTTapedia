(* Parameter Eps_i "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" *)
Parameter Eps_i : (set->prop)->set.
Axiom Eps_i_ax : forall P:set->prop, forall x:set, P x -> P (Eps_i P).
Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
(* Unicode /\ "2227" *)
Infix /\ 780 left := and.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
(* Unicode \/ "2228" *)
Infix \/ 785 left := or.
Definition iff : prop -> prop -> prop := fun A B:prop => and (A -> B) (B -> A).
(* Unicode <-> "2194" *)
Infix <-> 805 := iff.
Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
Definition neq : A->A->prop := fun x y:A => ~ eq x y.
End Eq.
Infix = 502 := eq.
(* Unicode <> "2260" *)
Infix <> 502 := neq.
Section FE.
Variable A B : SType.
Axiom func_ext : forall f g : A -> B , (forall x : A , f x = g x) -> f = g.
End FE.
Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.
(* Unicode exists "2203" *)
Binder+ exists , := ex.
Axiom prop_ext : forall p q:prop, iff p q -> p = q.
Parameter In:set->set->prop.
Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.
Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.
Axiom In_ind : forall P:set->prop, (forall X:set, (forall x :e X, P x) -> P X) -> forall X:set, P X.
Binder+ exists , := ex; and.
Parameter Empty : set.
Axiom EmptyAx : ~exists x:set, x :e Empty.
(* Unicode Union "22C3" *)
Parameter Union : set->set.
Axiom UnionEq : forall X x, x :e Union X <-> exists Y, x :e Y /\ Y :e X.
(* Unicode Power "1D4AB" *)
Parameter Power : set->set.
Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.
Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.
Axiom ReplEq : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} <-> exists x :e A, y = F x.
Definition TransSet : set->prop := fun U:set => forall x :e U, x c= U.
Definition Union_closed : set->prop := fun U:set => forall X:set, X :e U -> Union X :e U.
Definition Power_closed : set->prop := fun U:set => forall X:set, X :e U -> Power X :e U.
Definition Repl_closed : set->prop := fun U:set => forall X:set, X :e U -> forall F:set->set,
   (forall x:set, x :e X -> F x :e U) -> {F x|x :e X} :e U.
Definition ZF_closed : set->prop := fun U:set =>
   Union_closed U
/\ Power_closed U
/\ Repl_closed U.
Parameter UnivOf : set->set.
Axiom UnivOf_In : forall N:set, N :e UnivOf N.
Axiom UnivOf_TransSet : forall N:set, TransSet (UnivOf N).
Axiom UnivOf_ZF_closed : forall N:set, ZF_closed (UnivOf N).
Axiom UnivOf_Min : forall N U:set, N :e U
  -> TransSet U
  -> ZF_closed U
  -> UnivOf N c= U.

Theorem andI : forall (A B : prop), A -> B -> A /\ B.
exact (fun A B a b P H => H a b).
Qed.

Theorem orIL : forall (A B : prop), A -> A \/ B.
exact (fun A B a P H1 H2 => H1 a).
Qed.

Theorem orIR : forall (A B : prop), B -> A \/ B.
exact (fun A B b P H1 H2 => H2 b).
Qed.

Theorem iffI : forall A B:prop, (A -> B) -> (B -> A) -> (A <-> B).
exact (fun A B => andI (A -> B) (B -> A)).
Qed.

Theorem pred_ext : forall P Q:set -> prop, (forall x, P x <-> Q x) -> P = Q.
let P Q. assume H1. apply func_ext set prop.
let x. apply prop_ext.
prove P x <-> Q x. exact H1 x.
Qed.

Definition nIn : set->set->prop :=
fun x X => ~In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.

Theorem EmptyE : forall x:set, x /:e Empty.
let x. assume H.
apply EmptyAx.
witness x. exact H.
Qed.

Theorem PowerI : forall X Y:set, Y c= X -> Y :e Power X.
let X Y. apply PowerEq X Y. exact (fun _ H => H).
Qed.

Theorem Subq_Empty : forall X:set, Empty c= X.
exact (fun (X x : set) (H : x :e Empty) => EmptyE x H (x :e X)).
Qed.

Theorem Empty_In_Power : forall X:set, Empty :e Power X.
exact (fun X : set => PowerI X Empty (Subq_Empty X)).
Qed.


Theorem xm : forall P:prop, P \/ ~P.
let P:prop.
set p1 := fun x : set => x = Empty \/ P.
set p2 := fun x : set => x <> Empty \/ P.
claim L1:p1 Empty.
{ prove (Empty = Empty \/ P). apply orIL. exact (fun q H => H). }
claim L2: (Eps_i p1) = Empty \/ P.
{ exact (Eps_i_ax p1 Empty L1). }
claim L3:p2 (Power Empty).
{ prove ~(Power Empty = Empty) \/ P. apply orIL.
  assume H1: Power Empty = Empty.
  apply EmptyE Empty.
  prove Empty :e Empty.
  rewrite <- H1 at 2. apply Empty_In_Power.
}
claim L4: Eps_i p2 <> Empty \/ P.
{ exact (Eps_i_ax p2 (Power Empty) L3). }
apply L2.
- assume H1: Eps_i p1 = Empty.
  apply L4.
  + assume H2: Eps_i p2 <> Empty.
    prove P \/ ~ P.
    apply orIR.
    prove ~ P.
    assume H3 : P.
    claim L5:p1 = p2.
    { apply pred_ext. let x. apply iffI.
      - assume H4.
        prove (~(x = Empty) \/ P).
        apply orIR.
        prove P.
        exact H3.
      - assume H4.
        prove (x = Empty \/ P).
        apply orIR.
        prove P.
        exact H3.
    }
    apply H2. rewrite <- L5. exact H1.
  + assume H2:P.
    prove P \/ ~ P.
    apply orIL.
    prove P.
    exact H2.
- assume H1:P.
    prove P \/ ~ P.
    apply orIL.
    prove P.
    exact H1.
Qed.

Theorem FalseE : False -> forall p:prop, p.
exact (fun H => H).
Qed.

Theorem andEL : forall (A B : prop), A /\ B -> A.
exact (fun A B H => H A (fun a b => a)).
Qed.

Theorem andER : forall (A B : prop), A /\ B -> B.
exact (fun A B H => H B (fun a b => b)).
Qed.

Section PropN.
Variable P1 P2 P3:prop.

Theorem and3I : P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
exact (fun H1 H2 H3 => andI (P1 /\ P2) P3 (andI P1 P2 H1 H2) H3).
Qed.

Theorem and3E : P1 /\ P2 /\ P3 -> (forall p:prop, (P1 -> P2 -> P3 -> p) -> p).
exact (fun u p H => u p (fun u u3 => u p (fun u1 u2 => H u1 u2 u3))).
Qed.

Theorem or3I1 : P1 -> P1 \/ P2 \/ P3.
exact (fun u => orIL (P1 \/ P2) P3 (orIL P1 P2 u)).
Qed.

Theorem or3I2 : P2 -> P1 \/ P2 \/ P3.
exact (fun u => orIL (P1 \/ P2) P3 (orIR P1 P2 u)).
Qed.

Theorem or3I3 : P3 -> P1 \/ P2 \/ P3.
exact (orIR (P1 \/ P2) P3).
Qed.

Theorem or3E : P1 \/ P2 \/ P3 -> (forall p:prop, (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> p).
exact (fun u p H1 H2 H3 => u p (fun u => u p H1 H2) H3).
Qed.

Variable P4:prop.

Theorem and4I : P1 -> P2 -> P3 -> P4 -> P1 /\ P2 /\ P3 /\ P4.
exact (fun H1 H2 H3 H4 => andI (P1 /\ P2 /\ P3) P4 (and3I H1 H2 H3) H4).
Qed.

Variable P5:prop.

Theorem and5I : P1 -> P2 -> P3 -> P4 -> P5 -> P1 /\ P2 /\ P3 /\ P4 /\ P5.
exact (fun H1 H2 H3 H4 H5 => andI (P1 /\ P2 /\ P3 /\ P4) P5 (and4I H1 H2 H3 H4) H5).
Qed.

Variable P6:prop.

Theorem and6I: P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6.
exact (fun H1 H2 H3 H4 H5 H6 => andI (P1 /\ P2 /\ P3 /\ P4 /\ P5) P6 (and5I H1 H2 H3 H4 H5) H6).
Qed.

Variable P7:prop.

Theorem and7I: P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P7 -> P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ P7.
exact (fun H1 H2 H3 H4 H5 H6 H7 => andI (P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6) P7 (and6I H1 H2 H3 H4 H5 H6) H7).
Qed.

End PropN.

Theorem not_or_and_demorgan : forall A B:prop, ~(A \/ B) -> ~A /\ ~B.
let A B.
assume u : ~(A \/ B).
apply andI.
- prove ~A. assume a:A. exact (u (orIL A B a)).
- prove ~B. assume b:B. exact (u (orIR A B b)).
Qed.

Theorem not_ex_all_demorgan_i : forall P:set->prop, (~exists x, P x) -> forall x, ~P x.
let P. assume H1. let x. assume H2. apply H1.
witness x.
exact H2.
Qed.

Theorem iffEL : forall A B:prop, (A <-> B) -> A -> B.
exact (fun A B => andEL (A -> B) (B -> A)).
Qed.

Theorem iffER : forall A B:prop, (A <-> B) -> B -> A.
exact (fun A B => andER (A -> B) (B -> A)).
Qed.

Theorem iff_refl : forall A:prop, A <-> A.
exact (fun A:prop => andI (A -> A) (A -> A) (fun H : A => H) (fun H : A => H)).
Qed.

Theorem iff_sym : forall A B:prop, (A <-> B) -> (B <-> A).
let A B.
assume H1: (A -> B) /\ (B -> A).
apply H1.
assume H2: A -> B.
assume H3: B -> A.
exact iffI B A H3 H2.
Qed.

Theorem iff_trans : forall A B C: prop, (A <-> B) -> (B <-> C) -> (A <-> C).
let A B C.
assume H1: A <-> B.
assume H2: B <-> C.
apply H1.
assume H3: A -> B.
assume H4: B -> A.
apply H2.
assume H5: B -> C.
assume H6: C -> B.
exact (iffI A C (fun H => H5 (H3 H)) (fun H => H4 (H6 H))).
Qed.

Theorem eq_i_tra : forall x y z, x = y -> y = z -> x = z.
let x y z. assume H1 H2. rewrite <- H2. exact H1.
Qed.

Theorem neq_i_sym: forall x y, x <> y -> y <> x.
let x y. assume H1 H2. apply H1. symmetry. exact H2.
Qed.

Theorem Eps_i_ex : forall P:set -> prop, (exists x, P x) -> P (Eps_i P).
let P. assume H1. apply H1.
let x. assume H2.
exact Eps_i_ax P x H2.
Qed.

Theorem prop_ext_2 : forall p q:prop, (p -> q) -> (q -> p) -> p = q.
let p q. assume H1 H2. apply prop_ext. apply iffI.
- exact H1.
- exact H2.
Qed.

Theorem Subq_ref : forall X:set, X c= X.
exact (fun (X x : set) (H : x :e X) => H).
Qed.

Theorem Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
exact (fun (X Y Z : set) (H1 : X c= Y) (H2 : Y c= Z) (x : set) (H : x :e X) => (H2 x (H1 x H))).
Qed.

Theorem Empty_Subq_eq : forall X:set, X c= Empty -> X = Empty.
let X.
assume H1: X c= Empty.
apply set_ext.
- exact H1.
- exact (Subq_Empty X).
Qed.

Theorem Empty_eq : forall X:set, (forall x, x /:e X) -> X = Empty.
let X.
assume H1: forall x, x /:e X.
apply Empty_Subq_eq.
let x.
assume H2: x :e X.
prove False.
exact (H1 x H2).
Qed.

Theorem UnionI : forall X x Y:set, x :e Y -> Y :e X -> x :e Union X.
let X x Y.
assume H1: x :e Y.
assume H2: Y :e X.
apply UnionEq X x.
assume _ H3. apply H3.
prove exists Y:set, x :e Y /\ Y :e X.
witness Y.
apply andI.
- exact H1.
- exact H2.
Qed.

Theorem UnionE : forall X x:set, x :e Union X -> exists Y:set, x :e Y /\ Y :e X.
exact (fun X x : set => iffEL (x :e Union X) (exists Y:set, x :e Y /\ Y :e X) (UnionEq X x)).
Qed.

Theorem UnionE_impred : forall X x:set, x :e Union X -> forall p:prop, (forall Y:set, x :e Y -> Y :e X -> p) -> p.
let X x. assume H1.
let p. assume Hp.
apply UnionE X x H1.
let x. assume H2. apply H2.
exact Hp x.
Qed.

Theorem PowerE : forall X Y:set, Y :e Power X -> Y c= X.
let X Y. apply PowerEq X Y. exact (fun H _ => H).
Qed.

Theorem Self_In_Power : forall X:set, X :e Power X.
exact (fun X : set => PowerI X X (Subq_ref X)).
Qed.

Theorem dneg : forall P:prop, ~~P -> P.
let P. assume H1.
apply xm P.
- exact (fun H => H).
- assume H2: ~P.
  prove False.
  exact H1 H2.
Qed.

Theorem not_all_ex_demorgan_i : forall P:set->prop, ~(forall x, P x) -> exists x, ~P x.
let P.
assume u:~forall x, P x.
apply dneg.
assume v:~exists x, ~P x.
apply u. let x. apply dneg.
assume w:~P x. 
exact (not_ex_all_demorgan_i (fun x => ~P x) v x w).
Qed.

Theorem eq_or_nand : or = (fun (x y:prop) => ~(~x /\ ~y)).
apply func_ext prop (prop -> prop).
let x. apply func_ext prop prop.
let y. apply prop_ext_2.
- assume H1: x \/ y.
  assume H2: ~x /\ ~y.
  apply H2. assume H3 H4. exact (H1 False H3 H4).
- assume H1:~(~x /\ ~y).
  apply (xm x).
  + assume H2: x. apply orIL. exact H2.
  + assume H2: ~x. apply (xm y).
    * assume H3: y. apply orIR. exact H3.
    * assume H3: ~y. apply H1. exact (andI (~x) (~y) H2 H3).
Qed.

(* Parameter exactly1of2 "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" "163602f90de012a7426ee39176523ca58bc964ccde619b652cb448bd678f7e21" *)
Definition exactly1of2 : prop->prop->prop := fun A B:prop =>
A /\ ~B \/ ~A /\ B.

Theorem exactly1of2_I1 : forall A B:prop, A -> ~B -> exactly1of2 A B.
let A B.
assume HA: A.
assume HB: ~B.
prove A /\ ~B \/ ~A /\ B.
apply orIL.
prove A /\ ~B.
exact (andI A (~B) HA HB).
Qed.

Theorem exactly1of2_I2 : forall A B:prop, ~A -> B -> exactly1of2 A B.
let A B.
assume HA: ~A.
assume HB: B.
prove A /\ ~B \/ ~A /\ B.
apply orIR.
prove ~A /\ B.
exact (andI (~A) B HA HB).
Qed.

Theorem exactly1of2_E : forall A B:prop, exactly1of2 A B ->
forall p:prop,
(A -> ~B -> p) ->
(~A -> B -> p) ->
p.
let A B.
assume H1: exactly1of2 A B.
let p.
assume H2 : A -> ~B -> p.
assume H3 : ~A -> B -> p.
apply (H1 p).
- exact (fun H4 : A /\ ~B => H4 p H2).
- exact (fun H4 : ~A /\ B => H4 p H3).
Qed.

Theorem exactly1of2_or : forall A B:prop, exactly1of2 A B -> A \/ B.
let A B.
assume H1: exactly1of2 A B.
apply (exactly1of2_E A B H1 (A \/ B)).
- exact (fun (HA : A) (_ : ~B) => orIL A B HA).
- exact (fun (_ : ~A) (HB : B) => orIR A B HB).
Qed.

Theorem ReplI : forall A:set, forall F:set->set, forall x:set, x :e A -> F x :e {F x|x :e A}.
let A F x. assume H1.
apply ReplEq A F (F x).
assume _ H2. apply H2.
prove exists x' :e A, F x = F x'.
witness x. apply andI.
- exact H1.
- exact (fun q H => H).
Qed.

Theorem ReplE : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> exists x :e A, y = F x.
let A F y. apply ReplEq A F y. exact (fun H _ => H).
Qed.

Theorem ReplE_impred : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> forall p:prop, (forall x:set, x :e A -> y = F x -> p) -> p.
let A F y. assume H1.
apply ReplE A F y H1.
let x. assume H2. apply H2.
assume H3 H4.
let p. assume Hp.
exact Hp x H3 H4.
Qed.

Theorem ReplE' : forall X, forall f:set -> set, forall p:set -> prop, (forall x :e X, p (f x)) -> forall y :e {f x|x :e X}, p y.
let X f p. assume H1. let y. assume Hy.
apply ReplE_impred X f y Hy.
let x. assume Hx: x :e X. assume Hx2: y = f x.
prove p y. rewrite Hx2. exact H1 x Hx.
Qed.

Theorem Repl_Empty : forall F:set -> set, {F x|x :e Empty} = Empty.
let F. apply (Empty_eq {F x|x :e Empty}).
let y.
assume H1: y :e {F x|x :e Empty}.
apply (ReplE_impred Empty F y H1).
let x.
assume H2: x :e Empty.
assume _.
exact (EmptyE x H2).
Qed.

Theorem ReplEq_ext_sub : forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> {F x|x :e X} c= {G x|x :e X}.
let X F G.
assume H1: forall x :e X, F x = G x.
let y. assume Hy: y :e {F x|x :e X}.
apply ReplE_impred X F y Hy.
let x. assume Hx: x :e X.
assume H2: y = F x.
prove y :e {G x|x :e X}.
rewrite H2.
prove F x :e {G x|x :e X}.
rewrite H1 x Hx.
prove G x :e {G x|x :e X}.
apply ReplI. exact Hx.
Qed.

Theorem ReplEq_ext : forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> {F x|x :e X} = {G x|x :e X}.
let X F G.
assume H1: forall x :e X, F x = G x.
apply set_ext.
- exact ReplEq_ext_sub X F G H1.
- apply ReplEq_ext_sub X G F.
  let x. assume Hx. symmetry. exact H1 x Hx.
Qed.

Theorem Repl_inv_eq : forall P:set -> prop, forall f g:set -> set,
    (forall x, P x -> g (f x) = x)
 -> forall X, (forall x :e X, P x) -> {g y|y :e {f x|x :e X}} = X.
let P f g. assume H1. let X. assume HX.
apply set_ext.
- let w. assume Hw: w :e {g y|y :e {f x|x :e X}}.
  apply ReplE_impred {f x|x :e X} g w Hw.
  let y. assume Hy: y :e {f x|x :e X}.
  assume Hwy: w = g y.
  apply ReplE_impred X f y Hy.
  let x. assume Hx: x :e X.
  assume Hyx: y = f x.
  prove w :e X. rewrite Hwy. rewrite Hyx.
  prove g (f x) :e X.
  rewrite H1 x (HX x Hx).
  exact Hx.
- let x. assume Hx: x :e X.
  rewrite <- H1 x (HX x Hx).
  prove g (f x) :e {g y|y :e {f x|x :e X}}.
  apply ReplI.
  prove f x :e {f x|x :e X}.
  apply ReplI. exact Hx.
Qed.

Theorem Repl_invol_eq : forall P:set -> prop, forall f:set -> set,
    (forall x, P x -> f (f x) = x)
 -> forall X, (forall x :e X, P x) -> {f y|y :e {f x|x :e X}} = X.
let P f. assume H1.
exact Repl_inv_eq P f f H1.
Qed.

(* Parameter If_i "8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf" "b8ff52f838d0ff97beb955ee0b26fad79602e1529f8a2854bda0ecd4193a8a3c" *)
Definition If_i : prop->set->set->set := (fun p x y => Eps_i (fun z:set => p /\ z = x \/ ~p /\ z = y)).
Notation IfThenElse If_i.

Theorem If_i_correct : forall p:prop, forall x y:set,
p /\ (if p then x else y) = x \/ ~p /\ (if p then x else y) = y.
let p x y.
apply (xm p).
- assume H1: p.
  claim L1: p /\ x = x \/ ~p /\ x = y.
  {
    apply orIL. apply andI.
    - exact H1.
    - reflexivity.
  }
  exact (Eps_i_ax (fun z : set => p /\ z = x \/ ~ p /\ z = y) x L1).
- assume H1: ~p.
  claim L1: p /\ y = x \/ ~p /\ y = y.
  {
    apply orIR. apply andI.
    - exact H1.
    - reflexivity.
  }
  exact (Eps_i_ax (fun z : set => p /\ z = x \/ ~ p /\ z = y) y L1).
Qed.

Theorem If_i_0 : forall p:prop, forall x y:set,
~ p -> (if p then x else y) = y.
let p x y.
assume H1: ~p.
apply (If_i_correct p x y).
- assume H2: p /\ (if p then x else y) = x.
  exact (H1 (andEL p ((if p then x else y) = x) H2) ((if p then x else y) = y)).
- assume H2: ~p /\ (if p then x else y) = y.
  exact (andER (~p) ((if p then x else y) = y) H2).
Qed.

Theorem If_i_1 : forall p:prop, forall x y:set,
p -> (if p then x else y) = x.
let p x y.
assume H1: p.
apply (If_i_correct p x y).
- assume H2: p /\ (if p then x else y) = x.
  exact (andER p ((if p then x else y) = x) H2).
- assume H2: ~p /\ (if p then x else y) = y.
  exact (andEL (~p) ((if p then x else y) = y) H2 H1 ((if p then x else y) = x)).
Qed.

Theorem If_i_or : forall p:prop, forall x y:set, (if p then x else y) = x \/ (if p then x else y) = y.
let p x y.
apply (xm p).
- assume H1: p. apply orIL. exact (If_i_1 p x y H1).
- assume H1: ~p. apply orIR. exact (If_i_0 p x y H1).
Qed.

(* Parameter UPair "80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d" "74243828e4e6c9c0b467551f19c2ddaebf843f72e2437cc2dea41d079a31107f" *)
Definition UPair : set->set->set :=
fun y z => {if Empty :e X then y else z | X :e Power (Power Empty)}.
Notation SetEnum2 UPair.

Theorem UPairE :
forall x y z:set, x :e {y,z} -> x = y \/ x = z.
let x y z.
assume H1: x :e {y,z}.
apply (ReplE (Power (Power Empty)) (fun X => if Empty :e X then y else z) x H1).
let X.
assume H2: X :e Power (Power Empty) /\ x = if Empty :e X then y else z.
claim L1: x = if Empty :e X then y else z.
{ exact (andER (X :e Power (Power Empty)) (x = if Empty :e X then y else z) H2). }
apply (If_i_or (Empty :e X) y z).
- assume H3: (if Empty :e X then y else z) = y.
  apply orIL.
  prove x = y.
  rewrite <- H3. exact L1.
- assume H3: (if Empty :e X then y else z) = z.
  apply orIR.
  prove x = z.
  rewrite <- H3. exact L1.
Qed.

Theorem UPairI1 : forall y z:set, y :e {y,z}.
let y z.
prove y :e {y,z}.
rewrite <- (If_i_1 (Empty :e Power Empty) y z (Empty_In_Power Empty)) at 1.
prove (if Empty :e Power Empty then y else z) :e {y,z}.
prove (if Empty :e Power Empty then y else z) :e {if Empty :e X then y else z | X :e Power (Power Empty)}.
apply (ReplI (Power (Power Empty)) (fun X : set => if (Empty :e X) then y else z) (Power Empty)).
prove Power Empty :e Power (Power Empty).
exact (Self_In_Power (Power Empty)).
Qed.

Theorem UPairI2 : forall y z:set, z :e {y,z}.
let y z.
prove z :e {y,z}.
rewrite <- (If_i_0 (Empty :e Empty) y z (EmptyE Empty)) at 1.
prove (if Empty :e Empty then y else z) :e {y,z}.
prove (if Empty :e Empty then y else z) :e {if Empty :e X then y else z | X :e Power (Power Empty)}.
apply (ReplI (Power (Power Empty)) (fun X : set => if (Empty :e X) then y else z) Empty).
prove Empty :e Power (Power Empty).
exact (Empty_In_Power (Power Empty)).
Qed.

(* Parameter Sing "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "bd01a809e97149be7e091bf7cbb44e0c2084c018911c24e159f585455d8e6bd0" *)
Definition Sing : set -> set := fun x => {x,x}.
Notation SetEnum1 Sing.

Theorem SingI : forall x:set, x :e {x}. 
exact (fun x : set => UPairI1 x x).
Qed.

Theorem SingE : forall x y:set, y :e {x} -> y = x. 
exact (fun x y H => UPairE y x x H (y = x) (fun H => H) (fun H => H)).
Qed.

(* Parameter binunion "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" "5e1ac4ac93257583d0e9e17d6d048ff7c0d6ccc1a69875b2a505a2d4da305784" *)
Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.
(* Unicode :\/: "222a" *)
Infix :\/: 345 left := binunion.

Theorem binunionI1 : forall X Y z:set, z :e X -> z :e X :\/: Y.
let X Y z.
assume H1: z :e X.
prove z :e X :\/: Y.
prove z :e Union {X,Y}.
apply (UnionI {X,Y} z X).
- prove z :e X. exact H1.
- prove X :e {X,Y}. exact (UPairI1 X Y).
Qed.

Theorem binunionI2 : forall X Y z:set, z :e Y -> z :e X :\/: Y.
let X Y z.
assume H1: z :e Y.
prove z :e X :\/: Y.
prove z :e Union {X,Y}.
apply (UnionI {X,Y} z Y).
- prove z :e Y. exact H1.
- prove Y :e {X,Y}. exact (UPairI2 X Y).
Qed.

Theorem binunionE : forall X Y z:set, z :e X :\/: Y -> z :e X \/ z :e Y.
let X Y z.
assume H1: z :e X :\/: Y.
prove z :e X \/ z :e Y.
apply (UnionE_impred {X,Y} z H1).
let Z.
assume H2: z :e Z.
assume H3: Z :e {X,Y}.
apply (UPairE Z X Y H3).
- assume H4: Z = X.
  apply orIL.
  prove z :e X.
  rewrite <- H4.
  prove z :e Z.
  exact H2.
- assume H4: Z = Y.
  apply orIR.
  prove z :e Y.
  rewrite <- H4.
  prove z :e Z.
  exact H2.
Qed.

Theorem binunionE' : forall X Y z, forall p:prop, (z :e X -> p) -> (z :e Y -> p) -> (z :e X :\/: Y -> p).
let X Y z p. assume H1 H2 Hz.
apply binunionE X Y z Hz.
- assume H3: z :e X. exact H1 H3.
- assume H3: z :e Y. exact H2 H3.
Qed.

Theorem binunion_asso:forall X Y Z:set, X :\/: (Y :\/: Z) = (X :\/: Y) :\/: Z.
let X Y Z. apply set_ext.
- let w. assume H1: w :e X :\/: (Y :\/: Z).
  prove w :e (X :\/: Y) :\/: Z.
  apply (binunionE X (Y :\/: Z) w H1).
  + assume H2: w :e X.
    apply binunionI1. apply binunionI1. exact H2.
  + assume H2: w :e Y :\/: Z.
    apply (binunionE Y Z w H2).
    * assume H3: w :e Y.
      apply binunionI1. apply binunionI2. exact H3.
    * assume H3: w :e Z.
      apply binunionI2. exact H3.
- let w. assume H1: w :e (X :\/: Y) :\/: Z.
  prove w :e X :\/: (Y :\/: Z).
  apply (binunionE (X :\/: Y) Z w H1).
  + assume H2: w :e X :\/: Y.
    apply (binunionE X Y w H2).
    * assume H3: w :e X.
      apply binunionI1. exact H3.
    * assume H3: w :e Y.
      apply binunionI2. apply binunionI1. exact H3.
  + assume H2: w :e Z.
    apply binunionI2. apply binunionI2. exact H2.
Qed.

Theorem binunion_com_Subq:forall X Y:set, X :\/: Y c= Y :\/: X.
let X Y w. assume H1: w :e X :\/: Y.
prove w :e Y :\/: X.
apply (binunionE X Y w H1).
- assume H2: w :e X. apply binunionI2. exact H2.
- assume H2: w :e Y. apply binunionI1. exact H2.
Qed.

Theorem binunion_com:forall X Y:set, X :\/: Y = Y :\/: X.
let X Y. apply set_ext.
- exact (binunion_com_Subq X Y).
- exact (binunion_com_Subq Y X).
Qed.

Theorem binunion_idl:forall X:set, Empty :\/: X = X.
let X. apply set_ext.
- let x. assume H1: x :e Empty :\/: X.
  apply (binunionE Empty X x H1).
  + assume H2: x :e Empty. prove False. exact (EmptyE x H2).
  + assume H2: x :e X. exact H2.
- let x. assume H2: x :e X. prove x :e Empty :\/: X. apply binunionI2. exact H2.
Qed.

Theorem binunion_idr:forall X:set, X :\/: Empty = X.
let X.
rewrite (binunion_com X Empty).
exact (binunion_idl X).
Qed.

Theorem binunion_Subq_1: forall X Y:set, X c= X :\/: Y.
exact binunionI1.
Qed.

Theorem binunion_Subq_2: forall X Y:set, Y c= X :\/: Y.
exact binunionI2.
Qed.

Theorem binunion_Subq_min: forall X Y Z:set, X c= Z -> Y c= Z -> X :\/: Y c= Z.
let X Y Z.
assume H1: X c= Z.
assume H2: Y c= Z.
let w.
assume H3: w :e X :\/: Y.
apply (binunionE X Y w H3).
- assume H4: w :e X. exact (H1 w H4).
- assume H4: w :e Y. exact (H2 w H4).
Qed.

Theorem Subq_binunion_eq:forall X Y, (X c= Y) = (X :\/: Y = Y).
let X Y. apply prop_ext_2.
- assume H1: X c= Y.
  prove X :\/: Y = Y.
  apply set_ext.
  + prove X :\/: Y c= Y. apply (binunion_Subq_min X Y Y).
    * prove X c= Y. exact H1.
    * prove Y c= Y. exact (Subq_ref Y).
  + prove Y c= X :\/: Y. exact (binunion_Subq_2 X Y).
- assume H1: X :\/: Y = Y.
  prove X c= Y.
  rewrite <- H1.
  prove X c= X :\/: Y.
  exact (binunion_Subq_1 X Y).
Qed.

Definition SetAdjoin : set->set->set := fun X y => X :\/: {y}.
Notation SetEnum Empty Sing UPair SetAdjoin.
(* Parameter famunion "d772b0f5d472e1ef525c5f8bd11cf6a4faed2e76d4eacfa455f4d65cc24ec792" "b3e3bf86a58af5d468d398d3acad61ccc50261f43c856a68f8594967a06ec07a" *)
Definition famunion:set->(set->set)->set
:= fun X F => Union {F x|x :e X}.
(* Unicode \/_ "22C3" *)
(* Subscript \/_ *)
Binder \/_ , := famunion.

Theorem famunionI:forall X:set, forall F:(set->set), forall x y:set, x :e X -> y :e F x -> y :e \/_ x :e X, F x.
exact (fun X F x y H1 H2 => UnionI (Repl X F) y (F x) H2 (ReplI X F x H1)).
Qed.

Theorem famunionE:forall X:set, forall F:(set->set), forall y:set, y :e (\/_ x :e X, F x) -> exists x :e X, y :e F x.
let X F y.
assume H1: y :e (\/_ x :e X, F x).
prove exists x :e X, y :e F x.
apply (UnionE_impred {F x|x :e X} y H1).
let Y.
assume H2: y :e Y.
assume H3: Y :e {F x|x :e X}.
apply (ReplE_impred X F Y H3).
let x.
assume H4: x :e X.
assume H5: Y = F x.
witness x.
prove x :e X /\ y :e F x.
apply andI.
- exact H4.
- prove y :e F x.
  rewrite <- H5.
  exact H2.
Qed.

Theorem famunionE_impred : forall X : set , forall F : (set -> set) , forall y : set , y :e (\/_ x :e X , F x) -> forall p:prop, (forall x, x :e X -> y :e F x -> p) -> p.
let X F y. assume Hy.
let p. assume Hp.
apply famunionE X F y Hy.
let x. assume H1. apply H1.
exact Hp x.
Qed.

Theorem famunion_Empty: forall F:set -> set, (\/_ x :e Empty, F x) = Empty.
let F. apply Empty_Subq_eq.
let y. assume Hy: y :e \/_ x :e Empty, F x.
apply famunionE_impred Empty F y Hy.
let x. assume Hx: x :e Empty. prove False. exact EmptyE x Hx.
Qed.

Theorem famunion_Subq: forall X, forall f g:set -> set, (forall x :e X, f x c= g x) -> famunion X f c= famunion X g.
let X f g. assume Hfg.
let y. assume Hy. apply famunionE_impred X f y Hy.
let x. assume Hx.
assume H1: y :e f x.
apply famunionI X g x y Hx.
prove y :e g x.
exact Hfg x Hx y H1.
Qed.

Theorem famunion_ext: forall X, forall f g:set -> set, (forall x :e X, f x = g x) -> famunion X f = famunion X g.
let X f g. assume Hfg.
apply set_ext.
- apply famunion_Subq.
  let x. assume Hx. rewrite Hfg x Hx. apply Subq_ref.
- apply famunion_Subq.
  let x. assume Hx. rewrite Hfg x Hx. apply Subq_ref.
Qed.

Section SepSec.
Variable X:set.
Variable P:set->prop.
Let z : set := Eps_i (fun z => z :e X /\ P z).
Let F:set->set := fun x => if P x then x else z.
(* Parameter Sep "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" "f336a4ec8d55185095e45a638507748bac5384e04e0c48d008e4f6a9653e9c44" *)
Definition Sep:set
:= if (exists z :e X, P z) then {F x|x :e X} else Empty.
End SepSec.
Notation Sep Sep.

Theorem SepI:forall X:set, forall P:(set->prop), forall x:set, x :e X -> P x -> x :e {x :e X|P x}.
let X P x.
set z : set := Eps_i (fun z => z :e X /\ P z).
set F : set->set := fun x => if P x then x else z.
assume H1: x :e X.
assume H2: P x.
claim L1: exists z :e X, P z.
{
  witness x. apply andI.
  - exact H1.
  - exact H2.
}
prove x :e {x :e X|P x}.
prove x :e if (exists z :e X, P z) then {F x|x :e X} else Empty.
(*** Note:
 Making L2 a claim and then rewriting with it succeeds, but rewrite (If_i_1 (exists z :e X, P z) {F x|x :e X} Empty L1) fails.
 The reason is that when the proposition proved by (If_i_1 (exists z :e X, P z) {F x|x :e X} Empty L1) is
 extracted by the code, the F x will be beta reduced to be if P x then x else z. After this beta reduction, the left hand side of the
 equation does not match the right hand side of the claim x :e if (exists z :e X, P z) then {F x|x :e X} else Empty.
 This is an example of how one must be careful using the apply and rewrite tactics and must sometimes give these
 kinds of explicit annotations, i.e., proving a beta-eta-delta equivalent claim.
 ***)
claim L2: (if (exists z :e X, P z) then {F x|x :e X} else Empty) = {F x|x :e X}.
{
  exact (If_i_1 (exists z :e X, P z) {F x|x :e X} Empty L1).
}
rewrite L2.
prove x :e {F x|x :e X}.
claim L3: F x = x.
{
  prove (if P x then x else z) = x.
  exact (If_i_1 (P x) x z H2).
}
rewrite <- L3.
prove F x :e {F x|x :e X}.
exact (ReplI X F x H1).
Qed.

Theorem SepE:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X /\ P x.
let X P x.
set z : set := Eps_i (fun z => z :e X /\ P z).
set F : set->set := fun x => if P x then x else z.
apply (xm (exists z :e X, P z)).
- assume H1: exists z :e X, P z.
  prove (x :e (if (exists z :e X, P z) then {F x|x :e X} else Empty) -> x :e X /\ P x).
  claim L1: (if (exists z :e X, P z) then {F x|x :e X} else Empty) = {F x|x :e X}.
  {
    exact (If_i_1 (exists z :e X, P z) {F x|x :e X} Empty H1).
  }
  rewrite L1.
  prove x :e {F x|x :e X} -> x :e X /\ P x.
  assume H2: x :e {F x|x :e X}.
  apply (ReplE_impred X F x H2).
  let y.
  assume H3: y :e X.
  assume H4: x = F y.
  prove x :e X /\ P x.
  apply (xm (P y)).
  + assume H5: P y.
    claim L2: x = y.
    {
      rewrite <- (If_i_1 (P y) y z H5).
      exact H4.
    }
    rewrite L2.
    prove y :e X /\ P y.
    apply andI.
    * exact H3.
    * exact H5.
  + assume H5: ~P y.
    claim L2: x = z.
    {
      rewrite <- (If_i_0 (P y) y z H5).
      exact H4.
    }
    rewrite L2.
    prove z :e X /\ P z.
    exact (Eps_i_ex (fun z => z :e X /\ P z) H1).
- assume H1: ~exists z :e X, P z.
  prove (x :e (if (exists z :e X, P z) then {F x|x :e X} else Empty) -> x :e X /\ P x).
  claim L1: (if (exists z :e X, P z) then {F x|x :e X} else Empty) = Empty.
  { exact (If_i_0 (exists z :e X, P z) {F x|x :e X} Empty H1). }
  rewrite L1.
  prove x :e Empty -> x :e X /\ P x.
  assume H2: x :e Empty.
  prove False.
  exact (EmptyE x H2).
Qed.

Theorem SepE1:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X.
exact (fun X P x H => SepE X P x H (x :e X) (fun H _ => H)).
Qed.

Theorem SepE2:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> P x.
exact (fun X P x H => SepE X P x H (P x) (fun _ H => H)).
Qed.

Theorem Sep_Empty: forall P:set -> prop, {x :e Empty|P x} = Empty.
let P. apply Empty_eq.
let x. assume Hx.
exact EmptyE x (SepE1 Empty P x Hx).
Qed.

Theorem Sep_Subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.
exact SepE1.
Qed.

Theorem Sep_In_Power : forall X:set, forall P:set->prop, {x :e X|P x} :e Power X.
exact (fun X P => PowerI X (Sep X P) (Sep_Subq X P)).
Qed.

(* Parameter ReplSep "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd" "ec807b205da3293041239ff9552e2912636525180ddecb3a2b285b91b53f70d8" *)
Definition ReplSep : set->(set->prop)->(set->set)->set := fun X P F => {F x|x :e {z :e X|P z}}.
Notation ReplSep ReplSep.

Theorem ReplSepI: forall X:set, forall P:set->prop, forall F:set->set, forall x:set, x :e X -> P x -> F x :e {F x|x :e X, P x}.
exact (fun X P F x u v => ReplI (Sep X P) F x (SepI X P x u v)).
Qed.

Theorem ReplSepE:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> exists x:set, x :e X /\ P x /\ y = F x.
let X P F y.
assume H1: y :e {F x|x :e {z :e X|P z}}.
apply (ReplE {z :e X|P z} F y H1).
let x.
assume H2: x :e {z :e X|P z} /\ y = F x.
apply H2.
assume H3: x :e {z :e X|P z}.
assume H4: y = F x.
apply (SepE X P x H3).
assume H5: x :e X.
assume H6: P x.
witness x.
apply and3I.
- exact H5.
- exact H6.
- exact H4.
Qed.

Theorem ReplSepE_impred: forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> forall p:prop, (forall x :e X, P x -> y = F x -> p) -> p.
let X P F y.
assume H1: y :e {F x|x :e X, P x}.
let p.
assume H2: forall x :e X, P x -> y = F x -> p.
prove p.
apply ReplSepE X P F y H1.
let x. assume H3. apply H3. assume H3. apply H3.
exact H2 x.
Qed.

(* Parameter binintersect "8cf6b1f490ef8eb37db39c526ab9d7c756e98b0eb12143156198f1956deb5036" "b2abd2e5215c0170efe42d2fa0fb8a62cdafe2c8fbd0d37ca14e3497e54ba729" *)
Definition binintersect:set->set->set
:= fun X Y => {x :e X |x :e Y}.
(* Unicode :/\: "2229" *)
Infix :/\: 340 left := binintersect.

Theorem binintersectI:forall X Y z, z :e X -> z :e Y -> z :e X :/\: Y.
exact (fun X Y z H1 H2 => SepI X (fun x:set => x :e Y) z H1 H2).
Qed.

Theorem binintersectE:forall X Y z, z :e X :/\: Y -> z :e X /\ z :e Y.
exact (fun X Y z H1 => SepE X (fun x:set => x :e Y) z H1).
Qed.

Theorem binintersectE1:forall X Y z, z :e X :/\: Y -> z :e X.
exact (fun X Y z H1 => SepE1 X (fun x:set => x :e Y) z H1).
Qed.

Theorem binintersectE2:forall X Y z, z :e X :/\: Y -> z :e Y.
exact (fun X Y z H1 => SepE2 X (fun x:set => x :e Y) z H1).
Qed.

Theorem binintersect_Subq_1:forall X Y:set, X :/\: Y c= X.
exact binintersectE1.
Qed.

Theorem binintersect_Subq_2:forall X Y:set, X :/\: Y c= Y.
exact binintersectE2.
Qed.

Theorem binintersect_Subq_eq_1 : forall X Y, X c= Y -> X :/\: Y = X.
let X Y.
assume H1: X c= Y.
apply set_ext.
- apply binintersect_Subq_1.
- let x. assume H2: x :e X.
  apply binintersectI.
  + exact H2.
  + apply H1. exact H2.
Qed.

Theorem binintersect_Subq_max:forall X Y Z:set, Z c= X -> Z c= Y -> Z c= X :/\: Y.
let X Y Z.
assume H1: Z c= X.
assume H2: Z c= Y.
let w.
assume H3: w :e Z.
apply (binintersectI X Y w).
- prove w :e X. exact (H1 w H3).
- prove w :e Y. exact (H2 w H3).
Qed.

Theorem binintersect_com_Subq: forall X Y:set, X :/\: Y c= Y :/\: X.
let X Y. apply (binintersect_Subq_max Y X (X :/\: Y)).
- prove X :/\: Y c= Y. apply binintersect_Subq_2.
- prove X :/\: Y c= X. apply binintersect_Subq_1.
Qed.

Theorem binintersect_com: forall X Y:set, X :/\: Y = Y :/\: X.
let X Y. apply set_ext.
- exact (binintersect_com_Subq X Y).
- exact (binintersect_com_Subq Y X).
Qed.

(* Parameter setminus "cc569397a7e47880ecd75c888fb7c5512aee4bcb1e7f6bd2c5f80cccd368c060" "c68e5a1f5f57bc5b6e12b423f8c24b51b48bcc32149a86fc2c30a969a15d8881" *)
Definition setminus:set->set->set
:= fun X Y => Sep X (fun x => x /:e Y).
(* Unicode :\: "2216" *)
Infix :\: 350 := setminus.

Theorem setminusI:forall X Y z, (z :e X) -> (z /:e Y) -> z :e X :\: Y.
exact (fun X Y z H1 H2 => SepI X (fun x:set => x /:e Y) z H1 H2).
Qed.

Theorem setminusE:forall X Y z, (z :e X :\: Y) -> z :e X /\ z /:e Y.
exact (fun X Y z H => SepE X (fun x:set => x /:e Y) z H).
Qed.

Theorem setminusE1:forall X Y z, (z :e X :\: Y) -> z :e X.
exact (fun X Y z H => SepE1 X (fun x:set => x /:e Y) z H).
Qed.

Theorem setminusE2:forall X Y z, (z :e X :\: Y) -> z /:e Y.
exact (fun X Y z H => SepE2 X (fun x:set => x /:e Y) z H).
Qed.

Theorem setminus_Subq:forall X Y:set, X :\: Y c= X.
exact setminusE1.
Qed.

Theorem setminus_In_Power : forall A U, A :\: U :e Power A.
let A U. apply PowerI. apply setminus_Subq.
Qed.

Theorem binunion_remove1_eq: forall X, forall x :e X, X = (X :\: {x}) :\/: {x}.
let X x.
assume Hx: x :e X.
apply set_ext.
- let y. assume Hy: y :e X.
  prove y :e (X :\: {x}) :\/: {x}.
  apply xm (y :e {x}).
  + assume H1: y :e {x}.
    apply binunionI2. exact H1.
  + assume H1: y /:e {x}.
    apply binunionI1. apply setminusI.
    * exact Hy.
    * exact H1.
- let y. assume Hy: y :e (X :\: {x}) :\/: {x}.
  apply binunionE (X :\: {x}) {x} y Hy.
  + assume H1: y :e X :\: {x}.
    prove y :e X.
    exact setminusE1 X {x} y H1.
  + assume H1: y :e {x}.
    prove y :e X.
    rewrite SingE x y H1.
    prove x :e X.
    exact Hx.
Qed.

Theorem In_irref : forall x, x /:e x.
apply In_ind.
prove (forall X:set, (forall x:set, x :e X -> x /:e x) -> X /:e X).
let X.
assume IH: forall x : set, x :e X -> x /:e x.
assume H: X :e X.
exact IH X H H.
Qed.

Theorem In_no2cycle : forall x y, x :e y -> y :e x -> False.
apply In_ind.
let x.
assume IH: forall z, z :e x -> forall y, z :e y -> y :e z -> False.
let y.
assume H1: x :e y.
assume H2: y :e x.
exact IH y H2 x H2 H1.
Qed.

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "65d8837d7b0172ae830bed36c8407fcd41b7d875033d2284eb2df245b42295a6" *)
Definition ordsucc : set->set := fun x:set => x :\/: {x}.

Theorem ordsuccI1 : forall x:set, x c= ordsucc x.
let x.
exact (fun (y : set) (H1 : y :e x) => binunionI1 x {x} y H1).
Qed.

Theorem ordsuccI2 : forall x:set, x :e ordsucc x.
exact (fun x : set => binunionI2 x {x} x (SingI x)).
Qed.

Theorem ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.
let x y.
assume H1: y :e x :\/: {x}.
apply (binunionE x {x} y H1).
- assume H2: y :e x. apply orIL. exact H2.
- assume H2: y :e {x}. apply orIR. exact (SingE x y H2).
Qed.

Notation Nat Empty ordsucc.

Theorem neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
let a. prove ~(0 = ordsucc a).
assume H1: 0 = ordsucc a.
claim L1: a :e ordsucc a -> False.
{ rewrite <- H1. exact (EmptyE a). }
exact (L1 (ordsuccI2 a)).
Qed.

Theorem neq_ordsucc_0 : forall a:set, ordsucc a <> 0.
let a. exact neq_i_sym 0 (ordsucc a) (neq_0_ordsucc a).
Qed.

Theorem ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.
let a b.
assume H1: ordsucc a = ordsucc b.
claim L1: a :e ordsucc b.
{
  rewrite <- H1.
  exact (ordsuccI2 a).
}
apply (ordsuccE b a L1).
- assume H2: a :e b.
  claim L2: b :e ordsucc a.
  {
    rewrite H1.
    exact (ordsuccI2 b).
  }
  apply (ordsuccE a b L2).
  + assume H3: b :e a. prove False. exact (In_no2cycle a b H2 H3).
  + assume H3: b = a. symmetry. exact H3.
- assume H2: a = b. exact H2.
Qed.

Theorem In_0_1 : 0 :e 1.
exact (ordsuccI2 0).
Qed.

Theorem In_0_2 : 0 :e 2.
exact (ordsuccI1 1 0 In_0_1).
Qed.

Theorem In_1_2 : 1 :e 2.
exact (ordsuccI2 1).
Qed.

Definition nat_p : set->prop := fun n:set => forall p:set->prop, p 0 -> (forall x:set, p x -> p (ordsucc x)) -> p n.

Theorem nat_0 : nat_p 0.
exact (fun p H _ => H).
Qed.

Theorem nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
exact (fun n H1 p H2 H3 => H3 n (H1 p H2 H3)).
Qed.

Theorem nat_1 : nat_p 1.
exact (nat_ordsucc 0 nat_0).
Qed.

Theorem nat_2 : nat_p 2.
exact (nat_ordsucc 1 nat_1).
Qed.

Theorem nat_0_in_ordsucc : forall n, nat_p n -> 0 :e ordsucc n.
let n.
assume H1.
apply H1 (fun n => 0 :e ordsucc n).
- prove 0 :e ordsucc 0.
  exact In_0_1.
- let n.
  assume IH: 0 :e ordsucc n.
  prove 0 :e ordsucc (ordsucc n).
  exact (ordsuccI1 (ordsucc n) 0 IH).
Qed.

Theorem nat_ordsucc_in_ordsucc : forall n, nat_p n -> forall m :e n, ordsucc m :e ordsucc n.
let n.
assume H1.
apply (H1 (fun n => forall m :e n, ordsucc m :e ordsucc n)).
- prove forall m :e 0, ordsucc m :e ordsucc 0.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume IH: forall m :e n, ordsucc m :e ordsucc n.
  prove forall m :e ordsucc n, ordsucc m :e ordsucc (ordsucc n).
  let m.
  assume H2: m :e ordsucc n.
  prove ordsucc m :e ordsucc (ordsucc n).
  apply (ordsuccE n m H2).
  + assume H3: m :e n.
    claim L1: ordsucc m :e ordsucc n.
    { exact (IH m H3). }
    exact (ordsuccI1 (ordsucc n) (ordsucc m) L1).
  + assume H3: m = n.
    rewrite H3.
    prove ordsucc n :e ordsucc (ordsucc n).
    exact (ordsuccI2 (ordsucc n)).
Qed.

Theorem nat_ind : forall p:set->prop, p 0 -> (forall n, nat_p n -> p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
let p.
assume H1: p 0.
assume H2: forall n, nat_p n -> p n -> p (ordsucc n).
claim L1: nat_p 0 /\ p 0.
{ exact (andI (nat_p 0) (p 0) nat_0 H1). }
claim L2: forall n, nat_p n /\ p n -> nat_p (ordsucc n) /\ p (ordsucc n).
{ let n.
  assume H3: nat_p n /\ p n.
  apply H3.
  assume H4: nat_p n.
  assume H5: p n.
  apply andI.
  - prove nat_p (ordsucc n).
    exact (nat_ordsucc n H4).
  - prove p (ordsucc n).
    exact (H2 n H4 H5).
}
let n.
assume H3.
claim L3: nat_p n /\ p n.
{ exact (H3 (fun n => nat_p n /\ p n) L1 L2). }
exact (andER (nat_p n) (p n) L3).
Qed.

Theorem nat_complete_ind : forall p:set->prop, (forall n, nat_p n -> (forall m :e n, p m) -> p n) -> forall n, nat_p n -> p n.
let p.
assume H1: forall n, nat_p n -> (forall m :e n, p m) -> p n.
claim L1: forall n:set, nat_p n -> forall m :e n, p m.
{ apply nat_ind.
  - prove forall m :e 0, p m.
    let m.
    assume Hm: m :e 0.
    prove False.
    exact (EmptyE m Hm).
  - let n.
    assume Hn: nat_p n.
    assume IHn: forall m :e n, p m.
    prove forall m :e ordsucc n, p m.
    let m.
    assume Hm: m :e ordsucc n.
    prove p m.
    apply (ordsuccE n m Hm).
    + assume H2: m :e n.
      exact (IHn m H2).
    + assume H2: m = n.
      prove p m.
      rewrite H2.
      prove p n.
      exact (H1 n Hn IHn).
}
prove forall n, nat_p n -> p n.
exact (fun n Hn => H1 n Hn (L1 n Hn)).
Qed.

Theorem nat_inv_impred : forall p:set->prop, p 0 -> (forall n, nat_p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
let p. assume H1 H2. exact nat_ind p H1 (fun n H _ => H2 n H).
Qed.

Theorem nat_inv : forall n, nat_p n -> n = 0 \/ exists x, nat_p x /\ n = ordsucc x.
apply nat_inv_impred.
- apply orIL. reflexivity.
- let n. assume Hn. apply orIR. witness n. apply andI.
  + exact Hn.
  + reflexivity.
Qed.

Theorem nat_p_trans : forall n, nat_p n -> forall m :e n, nat_p m.
apply nat_ind.
- prove forall m :e 0, nat_p m.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, nat_p m.
  prove forall m :e ordsucc n, nat_p m.
  let m.
  assume Hm: m :e ordsucc n.
  apply (ordsuccE n m Hm).
  + assume H1: m :e n.
    exact (IHn m H1).
  + assume H1: m = n.
    rewrite H1.
    exact Hn.
Qed.

Theorem nat_trans : forall n, nat_p n -> forall m :e n, m c= n.
apply nat_ind.
- prove forall m :e 0, m c= 0.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, m c= n.
  prove forall m :e ordsucc n, m c= ordsucc n.
  let m.
  assume Hm: m :e ordsucc n.
  apply (ordsuccE n m Hm).
  + assume H1: m :e n.
    prove m c= ordsucc n.
    apply (Subq_tra m n (ordsucc n)).
    * exact (IHn m H1).
    * exact (ordsuccI1 n).
  + assume H1: m = n.
    prove m c= ordsucc n.
    rewrite H1.
    prove n c= ordsucc n.
    exact (ordsuccI1 n).
Qed.

Theorem nat_ordsucc_trans : forall n, nat_p n -> forall m :e ordsucc n, m c= n.
let n.
assume Hn: nat_p n.
let m.
assume Hm: m :e ordsucc n.
let k.
assume Hk: k :e m.
prove k :e n.
apply (ordsuccE n m Hm).
- assume H1: m :e n.
  exact nat_trans n Hn m H1 k Hk.
- assume H1: m = n.
  rewrite <- H1.
  exact Hk.
Qed.

Definition surj : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall w :e Y, exists u :e X, f u = w).

Theorem form100_63_surjCantor: forall A:set, forall f:set -> set, ~surj A (Power A) f.
let A f. assume H. apply H.
assume H1: forall u :e A, f u :e Power A.
assume H2: forall w :e Power A, exists u :e A, f u = w.
set D := {x :e A|x /:e f x}.
claim L1: D :e Power A.
{ exact Sep_In_Power A (fun x => x /:e f x). }
apply H2 D L1.
let d. assume H. apply H.
assume Hd: d :e A.
assume HfdD: f d = D.
claim L2: d /:e D.
{ assume H3: d :e D.
  apply SepE2 A (fun x => x /:e f x) d H3.
  prove d :e f d.
  rewrite HfdD.
  prove d :e D.
  exact H3.
}
apply L2.
prove d :e D.
apply SepI.
- prove d :e A. exact Hd.
- prove d /:e f d. rewrite HfdD. exact L2.
Qed.

Definition inj : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall u v :e X, f u = f v -> u = v).

Theorem form100_63_injCantor: forall A:set, forall f:set -> set, ~inj (Power A) A f.
let A f. assume H. apply H.
assume H1: forall X :e Power A, f X :e A.
assume H2: forall X Y :e Power A, f X = f Y -> X = Y.
set D := {f X | X :e Power A, f X /:e X}.
claim L1: D :e Power A.
{ apply PowerI.
  let n. assume H3: n :e D.
  apply ReplSepE_impred (Power A) (fun X => f X /:e X) f n H3.
  let X. assume HX: X :e Power A.
  assume H4: f X /:e X.
  assume H5: n = f X.
  prove n :e A. rewrite H5. apply H1. exact HX.
}
claim L2: f D /:e D.
{ assume H3: f D :e D.
  apply ReplSepE_impred (Power A) (fun X => f X /:e X) f (f D) H3.
  let X. assume HX: X :e Power A.
  assume H4: f X /:e X.
  assume H5: f D = f X.
  claim L2a: D = X.
  { exact H2 D L1 X HX H5. }
  apply H4. rewrite <- L2a. exact H3.
}
apply L2.
prove f D :e D.
apply ReplSepI.
- prove D :e Power A. exact L1.
- prove f D /:e D. exact L2.
Qed.

Theorem injI : forall X Y, forall f:set -> set, (forall x :e X, f x :e Y) -> (forall x z :e X, f x = f z -> x = z) -> inj X Y f.
let X Y f. assume H1 H2.
prove (forall x :e X, f x :e Y) /\ (forall x z :e X, f x = f z -> x = z).
apply andI.
- exact H1.
- exact H2.
Qed.

Theorem inj_comp : forall X Y Z:set, forall f g:set->set, inj X Y f -> inj Y Z g -> inj X Z (fun x => g (f x)).
let X Y Z f g.
assume Hf.
assume Hg.
apply Hf.
assume Hf1 Hf2.
apply Hg.
assume Hg1 Hg2.
apply injI.
- let u. assume Hu: u :e X. exact (Hg1 (f u) (Hf1 u Hu)).
- let u. assume Hu: u :e X. let v. assume Hv: v :e X.
  assume H1: g (f u) = g (f v).
  prove u = v.
  apply Hf2 u Hu v Hv.
  prove f u = f v.
  apply Hg2 (f u) (Hf1 u Hu) (f v) (Hf1 v Hv).
  prove g (f u) = g (f v).
  exact H1.
Qed.

Definition bij : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall u v :e X, f u = f v -> u = v)
  /\
  (forall w :e Y, exists u :e X, f u = w).

Theorem bijI : forall X Y, forall f:set -> set,
    (forall u :e X, f u :e Y)
 -> (forall u v :e X, f u = f v -> u = v)
 -> (forall w :e Y, exists u :e X, f u = w)
 -> bij X Y f.
let X Y f. assume Hf1 Hf2 Hf3.
prove (forall u :e X, f u :e Y)
   /\ (forall u v :e X, f u = f v -> u = v)
   /\ (forall w :e Y, exists u :e X, f u = w).
apply and3I.
- exact Hf1.
- exact Hf2.
- exact Hf3.
Qed.

Theorem bijE : forall X Y, forall f:set -> set,
    bij X Y f
 -> forall p:prop,
      ((forall u :e X, f u :e Y)
    -> (forall u v :e X, f u = f v -> u = v)
    -> (forall w :e Y, exists u :e X, f u = w)
    -> p)
   -> p.
let X Y f. assume Hf. let p. assume Hp.
apply Hf. assume Hf. apply Hf.
assume Hf1 Hf2 Hf3.
exact Hp Hf1 Hf2 Hf3.
Qed.

Theorem bij_inj : forall X Y, forall f:set -> set, bij X Y f -> inj X Y f.
let X Y f. assume H1. apply H1. assume H1 _. exact H1.
Qed.

Theorem bij_id : forall X, bij X X (fun x => x).
let X.
prove (forall u :e X, u :e X) /\ (forall u v :e X, u = v -> u = v) /\ (forall w :e X, exists u :e X, u = w).
apply and3I.
- exact (fun u Hu => Hu).
- exact (fun u Hu v Hv H1 => H1).
- let w. assume Hw. witness w. apply andI.
  + exact Hw.
  + reflexivity.
Qed.

Theorem bij_comp : forall X Y Z:set, forall f g:set->set, bij X Y f -> bij Y Z g -> bij X Z (fun x => g (f x)).
let X Y Z f g.
assume Hf. apply Hf. assume Hf12 Hf3. apply Hf12. assume Hf1 Hf2.
assume Hg. apply Hg. assume Hg12 Hg3. apply Hg12. assume Hg1 Hg2.
prove (forall u :e X, g (f u) :e Z)
  /\
  (forall u v :e X, g (f u) = g (f v) -> u = v)
  /\
  (forall w :e Z, exists u :e X, g (f u) = w).
apply and3I.
- let u. assume Hu: u :e X. exact (Hg1 (f u) (Hf1 u Hu)).
- let u. assume Hu: u :e X. let v. assume Hv: v :e X.
  assume H1: g (f u) = g (f v).
  prove u = v.
  apply Hf2 u Hu v Hv.
  prove f u = f v.
  apply Hg2 (f u) (Hf1 u Hu) (f v) (Hf1 v Hv).
  prove g (f u) = g (f v).
  exact H1.
- let w. assume Hw: w :e Z. apply Hg3 w Hw.
  let y. assume Hy12. apply Hy12.
  assume Hy1: y :e Y. assume Hy2: g y = w.
  apply Hf3 y Hy1.
  let u. assume Hu12. apply Hu12.
  assume Hu1: u :e X. assume Hu2: f u = y.
  prove exists u :e X, g (f u) = w.
  witness u.
  apply andI.
  + exact Hu1.
  + rewrite Hu2. exact Hy2.
Qed.

Theorem bij_surj : forall X Y, forall f:set -> set, bij X Y f -> surj X Y f.
let X Y f. assume H1. apply H1. assume H1. apply H1.
assume H1 _ H2.
prove (forall u :e X, f u :e Y)
   /\ (forall w :e Y, exists u :e X, f u = w).
apply andI.
- exact H1.
- exact H2.
Qed.

Definition inv : set -> (set -> set) -> set -> set := fun X f => fun y:set => Eps_i (fun x => x :e X /\ f x = y).

Theorem surj_rinv : forall X Y, forall f:set->set, (forall w :e Y, exists u :e X, f u = w) -> forall y :e Y, inv X f y :e X /\ f (inv X f y) = y.
let X Y f. assume H1.
let y. assume Hy: y :e Y.
apply H1 y Hy.
let x.
assume H2.
exact Eps_i_ax (fun x => x :e X /\ f x = y) x H2.
Qed.

Theorem inj_linv : forall X, forall f:set->set, (forall u v :e X, f u = f v -> u = v) -> forall x :e X, inv X f (f x) = x.
let X f.
assume H1.
let x. assume Hx.
claim L1: inv X f (f x) :e X /\ f (inv X f (f x)) = f x.
{ apply Eps_i_ax (fun x' => x' :e X /\ f x' = f x) x.
  apply andI.
  - exact Hx.
  - reflexivity.
}
apply L1.
assume H2 H3.
exact H1 (inv X f (f x)) H2 x Hx H3.
Qed.

Theorem bij_inv : forall X Y, forall f:set->set, bij X Y f -> bij Y X (inv X f).
let X Y f.
assume H1. apply H1.
assume H2. apply H2.
assume H3: forall u :e X, f u :e Y.
assume H4: forall u v :e X, f u = f v -> u = v.
assume H5: forall w :e Y, exists u :e X, f u = w.
set g : set->set := fun y => Eps_i (fun x => x :e X /\ f x = y).
claim L1: forall y :e Y, g y :e X /\ f (g y) = y.
{ exact surj_rinv X Y f H5. }
prove (forall u :e Y, g u :e X)
      /\
      (forall u v :e Y, g u = g v -> u = v)
      /\
      (forall w :e X, exists u :e Y, g u = w).
apply and3I.
- prove forall u :e Y, g u :e X.
  let u. assume Hu. apply L1 u Hu. assume H _. exact H.
- prove forall u v :e Y, g u = g v -> u = v.
  let u. assume Hu. let v. assume Hv H6.
  prove u = v.
  apply L1 u Hu.
  assume H7: g u :e X.
  assume H8: f (g u) = u.
  apply L1 v Hv.
  assume H9: g v :e X.
  assume H10: f (g v) = v.
  rewrite <- H8.
  rewrite <- H10.
  rewrite <- H6.
  reflexivity.
- prove forall w :e X, exists u :e Y, g u = w.
  let w. assume Hw.
  claim Lfw: f w :e Y.
  { exact H3 w Hw. }
  witness f w.
  apply andI.
  + exact Lfw.
  + exact inj_linv X f H4 w Hw.
Qed.

Definition atleastp : set -> set -> prop
 := fun X Y : set => exists f : set -> set, inj X Y f.

Theorem atleastp_tra: forall X Y Z, atleastp X Y -> atleastp Y Z -> atleastp X Z.
admit.
Qed.

Theorem Subq_atleastp : forall X Y, X c= Y -> atleastp X Y.
admit.
Qed.

Definition equip : set -> set -> prop
 := fun X Y : set => exists f : set -> set, bij X Y f.

Theorem equip_atleastp: forall X Y, equip X Y -> atleastp X Y.
admit.
Qed.

Theorem equip_ref : forall X, equip X X.
admit.
Qed.

Theorem equip_sym : forall X Y, equip X Y -> equip Y X.
admit.
Qed.

Theorem equip_tra : forall X Y Z, equip X Y -> equip Y Z -> equip X Z.
admit.
Qed.

Theorem equip_0_Empty : forall X, equip X 0 -> X = 0.
admit.
Qed.

Theorem equip_adjoin_ordsucc : forall N X y, y /:e X -> equip N X -> equip (ordsucc N) (X :\/: {y}).
admit.
Qed.

Theorem equip_ordsucc_remove1: forall X N, forall x :e X, equip X (ordsucc N) -> equip (X :\: {x}) N.
admit.
Qed.

Section SchroederBernstein.

Theorem KnasterTarski_set: forall A, forall F:set->set,
    (forall U :e Power A, F U :e Power A)
 -> (forall U V :e Power A, U c= V -> F U c= F V)
 -> exists Y :e Power A, F Y = Y.
admit.
Qed.

Theorem image_In_Power : forall A B, forall f:set -> set, (forall x :e A, f x :e B) -> forall U :e Power A, {f x|x :e U} :e Power B.
admit.
Qed.

Theorem image_monotone : forall f:set -> set, forall U V, U c= V -> {f x|x :e U} c= {f x|x :e V}.
admit.
Qed.

Theorem setminus_antimonotone : forall A U V, U c= V -> A :\: V c= A :\: U.
admit.
Qed.

Theorem SchroederBernstein: forall A B, forall f g:set -> set, inj A B f -> inj B A g -> equip A B.
admit.
Qed.

Theorem atleastp_antisym_equip: forall A B, atleastp A B -> atleastp B A -> equip A B.
admit.
Qed.

End SchroederBernstein.

Section PigeonHole.

Theorem PigeonHole_nat : forall n, nat_p n -> forall f:set -> set, (forall i :e ordsucc n, f i :e n) -> ~(forall i j :e ordsucc n, f i = f j -> i = j).
admit.
Qed.

Theorem Pigeonhole_not_atleastp_ordsucc : forall n, nat_p n -> ~atleastp (ordsucc n) n.
admit.
Qed.

End PigeonHole.

Theorem Union_ordsucc_eq : forall n, nat_p n -> Union (ordsucc n) = n.
admit.
Qed.

Theorem cases_1: forall i :e 1, forall p:set->prop, p 0 -> p i.
admit.
Qed.

Theorem cases_2: forall i :e 2, forall p:set->prop, p 0 -> p 1 -> p i.
admit.
Qed.

Theorem neq_0_1 : 0 <> 1.
admit.
Qed.

Theorem neq_1_0 : 1 <> 0.
admit.
Qed.

Theorem neq_0_2 : 0 <> 2.
admit.
Qed.

Theorem neq_2_0 : 2 <> 0.
admit.
Qed.

Definition ordinal : set->prop := fun (alpha:set) => TransSet alpha /\ forall beta :e alpha, TransSet beta.

Theorem ordinal_TransSet : forall alpha:set, ordinal alpha -> TransSet alpha.
admit.
Qed.

Theorem ordinal_Empty : ordinal Empty.
admit.
Qed.

Theorem ordinal_Hered : forall alpha:set, ordinal alpha -> forall beta :e alpha, ordinal beta.
admit.
Qed.

Theorem TransSet_ordsucc : forall X:set, TransSet X -> TransSet (ordsucc X).
admit.
Qed.

Theorem ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).
admit.
Qed.

Theorem nat_p_ordinal : forall n:set, nat_p n -> ordinal n.
admit.
Qed.

Theorem ordinal_1 : ordinal 1.
admit.
Qed.

Theorem ordinal_2 : ordinal 2.
admit.
Qed.

Theorem TransSet_ordsucc_In_Subq : forall X:set, TransSet X -> forall x :e X, ordsucc x c= X.
admit.
Qed.

Theorem ordinal_ordsucc_In_Subq : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta c= alpha.
admit.
Qed.

Theorem ordinal_trichotomy_or : forall alpha beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
admit.
Qed.    

Theorem ordinal_trichotomy_or_impred : forall alpha beta:set, ordinal alpha -> ordinal beta -> forall p:prop, (alpha :e beta -> p) -> (alpha = beta -> p) -> (beta :e alpha -> p) -> p.
admit.
Qed.

Theorem ordinal_In_Or_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha :e beta \/ beta c= alpha.
admit.
Qed.

Theorem ordinal_linear : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta \/ beta c= alpha.
admit.
Qed.

Theorem ordinal_ordsucc_In_eq : forall alpha beta, ordinal alpha -> beta :e alpha -> ordsucc beta :e alpha \/ alpha = ordsucc beta.
admit.
Qed.

Theorem ordinal_lim_or_succ : forall alpha, ordinal alpha -> (forall beta :e alpha, ordsucc beta :e alpha) \/ (exists beta :e alpha, alpha = ordsucc beta).
admit.
Qed.

Theorem ordinal_ordsucc_In : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta :e ordsucc alpha.
admit.
Qed.

Theorem ordinal_famunion : forall X, forall F:set -> set, (forall x :e X, ordinal (F x)) -> ordinal (\/_ x :e X, F x).
admit.
Qed.

Theorem ordinal_binintersect : forall alpha beta, ordinal alpha -> ordinal beta -> ordinal (alpha :/\: beta).
admit.
Qed.

Theorem ordinal_binunion : forall alpha beta, ordinal alpha -> ordinal beta -> ordinal (alpha :\/: beta).
admit.
Qed.

Theorem ordinal_ind : forall p:set->prop, 
(forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha)
->
forall alpha, ordinal alpha -> p alpha.
admit.
Qed.

Theorem least_ordinal_ex : forall p:set -> prop, (exists alpha, ordinal alpha /\ p alpha) -> exists alpha, ordinal alpha /\ p alpha /\ forall beta :e alpha, ~p beta.
admit.
Qed.

Theorem equip_Sing_1 : forall x, equip {x} 1.
admit.
Qed.

Theorem TransSet_In_ordsucc_Subq : forall x y, TransSet y -> x :e ordsucc y -> x c= y.
admit.
Qed.

Theorem exandE_i : forall P Q:set -> prop, (exists x, P x /\ Q x) -> forall r:prop, (forall x, P x -> Q x -> r) -> r.
admit.
Qed.

Theorem exandE_ii : forall P Q:(set -> set) -> prop, (exists x:set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set, P x -> Q x -> p) -> p.
admit.
Qed.

Theorem exandE_iii : forall P Q:(set -> set -> set) -> prop, (exists x:set -> set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set -> set, P x -> Q x -> p) -> p.
admit.
Qed.

Theorem exandE_iiii : forall P Q:(set -> set -> set -> set) -> prop, (exists x:set -> set -> set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set -> set -> set, P x -> Q x -> p) -> p.
admit.
Qed.

Section Descr_ii.
Variable P : (set -> set) -> prop.
(* Parameter Descr_ii "a6e81668bfd1db6e6eb6a13bf66094509af176d9d0daccda274aa6582f6dcd7c" "3bae39e9880bbf5d70538d82bbb05caf44c2c11484d80d06dee0589d6f75178c" *)
Definition Descr_ii : set -> set := fun x:set => Eps_i (fun y => forall h:set -> set, P h -> h x = y).
Hypothesis Pex: exists f:set -> set, P f.
Hypothesis Puniq: forall f g:set -> set, P f -> P g -> f = g.

Theorem Descr_ii_prop : P Descr_ii.
admit.
Qed.

End Descr_ii.
Section Descr_iii.
Variable P : (set -> set -> set) -> prop.
(* Parameter Descr_iii "dc42f3fe5d0c55512ef81fe5d2ad0ff27c1052a6814b1b27f5a5dcb6d86240bf" "ca5fc17a582fdd4350456951ccbb37275637ba6c06694213083ed9434fe3d545" *)
Definition Descr_iii : set -> set -> set := fun x y:set => Eps_i (fun z => forall h:set -> set -> set, P h -> h x y = z).
Hypothesis Pex: exists f:set -> set -> set, P f.
Hypothesis Puniq: forall f g:set -> set -> set, P f -> P g -> f = g.

Theorem Descr_iii_prop : P Descr_iii.
admit.
Qed.

End Descr_iii.
Section Descr_Vo1.
Variable P : Vo 1 -> prop.
(* Parameter Descr_Vo1 "322bf09a1711d51a4512e112e1767cb2616a7708dc89d7312c8064cfee6e3315" "615c0ac7fca2b62596ed34285f29a77b39225d1deed75d43b7ae87c33ba37083" *)
Definition Descr_Vo1 : Vo 1 := fun x:set => forall h:set -> prop, P h -> h x.
Hypothesis Pex: exists f:Vo 1, P f.
Hypothesis Puniq: forall f g:Vo 1, P f -> P g -> f = g.

Theorem Descr_Vo1_prop : P Descr_Vo1.
admit.
Qed.

End Descr_Vo1.
Section If_ii.
Variable p:prop.
Variable f g:set -> set.
(* Parameter If_ii "e76df3235104afd8b513a92c00d3cc56d71dd961510bf955a508d9c2713c3f29" "17057f3db7be61b4e6bd237e7b37125096af29c45cb784bb9cc29b1d52333779" *)
Definition If_ii : set -> set := fun x => if p then f x else g x.

Theorem If_ii_1 : p -> If_ii = f.
admit.
Qed.

Theorem If_ii_0 : ~p -> If_ii = g.
admit.
Qed.

End If_ii.
Section If_iii.
Variable p:prop.
Variable f g:set -> set -> set.
(* Parameter If_iii "53034f33cbed012c3c6db42812d3964f65a258627a765f5bede719198af1d1ca" "3314762dce5a2e94b7e9e468173b047dd4a9fac6ee2c5f553c6ea15e9c8b7542" *)
Definition If_iii : set -> set -> set := fun x y => if p then f x y else g x y.

Theorem If_iii_1 : p -> If_iii = f.
admit.
Qed.

Theorem If_iii_0 : ~p -> If_iii = g.
admit.
Qed.

End If_iii.
Section EpsilonRec_i.
Variable F:set -> (set -> set) -> set.
Definition In_rec_i_G : set -> set -> prop :=
fun X Y =>
forall R:set->set->prop,
(forall X:set, forall f:set->set, (forall x :e X, R x (f x)) -> R X (F X f)) ->
R X Y.
(* Parameter In_rec_i "f97da687c51f5a332ff57562bd465232bc70c9165b0afe0a54e6440fc4962a9f" "fac413e747a57408ad38b3855d3cde8673f86206e95ccdadff2b5babaf0c219e" *)
Definition In_rec_i : set -> set := fun X => Eps_i (In_rec_i_G X).

Theorem In_rec_i_G_c : forall X:set, forall f:set->set, (forall x :e X, In_rec_i_G x (f x)) -> In_rec_i_G X (F X f).
admit.
Qed.

Theorem In_rec_i_G_inv : forall X:set, forall Y:set, In_rec_i_G X Y -> exists f:set->set, (forall x :e X, In_rec_i_G x (f x)) /\ Y = F X f.
admit.
Qed.

Hypothesis Fr:forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.

Theorem In_rec_i_G_f : forall X:set, forall Y Z:set, In_rec_i_G X Y -> In_rec_i_G X Z -> Y = Z.
admit.
Qed.

Theorem In_rec_i_G_In_rec_i : forall X:set, In_rec_i_G X (In_rec_i X).
admit.
Qed.

Theorem In_rec_i_G_In_rec_i_d : forall X:set, In_rec_i_G X (F X In_rec_i).
admit.
Qed.

Theorem In_rec_i_eq : forall X:set, In_rec_i X = F X In_rec_i.
admit.
Qed.

End EpsilonRec_i.
Section EpsilonRec_ii.
Variable F:set -> (set -> (set -> set)) -> (set -> set).
Definition In_rec_G_ii : set -> (set -> set) -> prop :=
fun X Y =>
forall R:set->(set -> set)->prop,
(forall X:set, forall f:set->(set -> set), (forall x :e X, R x (f x)) -> R X (F X f)) ->
R X Y.
(* Parameter In_rec_ii "4d137cad40b107eb0fc2c707372525f1279575e6cadb4ebc129108161af3cedb" "f3c9abbc5074c0d68e744893a170de526469426a5e95400ae7fc81f74f412f7e" *)
Definition In_rec_ii : set -> (set -> set) := fun X => Descr_ii (In_rec_G_ii X).

Theorem In_rec_G_ii_c : forall X:set, forall f:set->(set -> set), (forall x :e X, In_rec_G_ii x (f x)) -> In_rec_G_ii X (F X f).
admit.
Qed.

Theorem In_rec_G_ii_inv : forall X:set, forall Y:(set -> set), In_rec_G_ii X Y -> exists f:set->(set -> set), (forall x :e X, In_rec_G_ii x (f x)) /\ Y = F X f.
admit.
Qed.

Hypothesis Fr:forall X:set, forall g h:set -> (set -> set), (forall x :e X, g x = h x) -> F X g = F X h.

Theorem In_rec_G_ii_f : forall X:set, forall Y Z:(set -> set), In_rec_G_ii X Y -> In_rec_G_ii X Z -> Y = Z.
admit.
Qed.

Theorem In_rec_G_ii_In_rec_ii : forall X:set, In_rec_G_ii X (In_rec_ii X).
admit.
Qed.

Theorem In_rec_G_ii_In_rec_ii_d : forall X:set, In_rec_G_ii X (F X In_rec_ii).
admit.
Qed.

Theorem In_rec_ii_eq : forall X:set, In_rec_ii X = F X In_rec_ii.
admit.
Qed.

End EpsilonRec_ii.
Section EpsilonRec_iii.
Variable F:set -> (set -> (set -> set -> set)) -> (set -> set -> set).
Definition In_rec_G_iii : set -> (set -> set -> set) -> prop :=
fun X Y =>
forall R:set->(set -> set -> set)->prop,
(forall X:set, forall f:set->(set -> set -> set), (forall x :e X, R x (f x)) -> R X (F X f)) ->
R X Y.
(* Parameter In_rec_iii "222f1b8dcfb0d2e33cc4b232e87cbcdfe5c4a2bdc5326011eb70c6c9aeefa556" "9b3a85b85e8269209d0ca8bf18ef658e56f967161bf5b7da5e193d24d345dd06" *)
Definition In_rec_iii : set -> (set -> set -> set) := fun X => Descr_iii (In_rec_G_iii X).

Theorem In_rec_G_iii_c : forall X:set, forall f:set->(set -> set -> set), (forall x :e X, In_rec_G_iii x (f x)) -> In_rec_G_iii X (F X f).
admit.
Qed.

Theorem In_rec_G_iii_inv : forall X:set, forall Y:(set -> set -> set), In_rec_G_iii X Y -> exists f:set->(set -> set -> set), (forall x :e X, In_rec_G_iii x (f x)) /\ Y = F X f.
admit.
Qed.

Hypothesis Fr:forall X:set, forall g h:set -> (set -> set -> set), (forall x :e X, g x = h x) -> F X g = F X h.

Theorem In_rec_G_iii_f : forall X:set, forall Y Z:(set -> set -> set), In_rec_G_iii X Y -> In_rec_G_iii X Z -> Y = Z.
admit.
Qed.

Theorem In_rec_G_iii_In_rec_iii : forall X:set, In_rec_G_iii X (In_rec_iii X).
admit.
Qed.

Theorem In_rec_G_iii_In_rec_iii_d : forall X:set, In_rec_G_iii X (F X In_rec_iii).
admit.
Qed.

Theorem In_rec_iii_eq : forall X:set, In_rec_iii X = F X In_rec_iii.
admit.
Qed.

End EpsilonRec_iii.
Section NatRec.
Variable z:set.
Variable f:set->set->set.
Let F : set->(set->set)->set := fun n g => if Union n :e n then f (Union n) (g (Union n)) else z.
Definition nat_primrec : set->set := In_rec_i F.

Theorem nat_primrec_r : forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.
admit.
Qed.

Theorem nat_primrec_0 : nat_primrec 0 = z.
admit.
Qed.

Theorem nat_primrec_S : forall n:set, nat_p n -> nat_primrec (ordsucc n) = f n (nat_primrec n).
admit.
Qed.

End NatRec.

Section NatAdd.

Definition add_nat : set->set->set := fun n m:set => nat_primrec n (fun _ r => ordsucc r) m.
Infix + 360 right := add_nat.

Theorem add_nat_0R : forall n:set, n + 0 = n.
admit.
Qed.

Theorem add_nat_SR : forall n m:set, nat_p m -> n + ordsucc m = ordsucc (n + m).
admit.
Qed.

Theorem add_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n + m).
admit.
Qed.

Theorem add_nat_1_1_2 : 1 + 1 = 2.
admit.
Qed.

Theorem add_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n+m)+k = n+(m+k).
admit.
Qed.

Theorem add_nat_0L : forall m:set, nat_p m -> 0+m = m.
admit.
Qed.

Theorem add_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n + m = ordsucc (n+m).
admit.
Qed.

Theorem add_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n + m = m + n.
admit.
Qed.

Theorem add_nat_In_R: forall m, nat_p m -> forall k :e m, forall n, nat_p n -> k + n :e m + n.
admit.
Qed.

Theorem add_nat_In_L: forall n, nat_p n -> forall m, nat_p m -> forall k :e m, n + k :e n + m.
admit.
Qed.

Theorem add_nat_Subq_R: forall k, nat_p k -> forall m, nat_p m -> k c= m -> forall n, nat_p n -> k + n c= m + n.
admit.
Qed.

Theorem add_nat_Subq_L: forall n, nat_p n -> forall k, nat_p k -> forall m, nat_p m -> k c= m -> n + k c= n + m.
admit.
Qed.

Theorem add_nat_Subq_R' : forall m, nat_p m -> forall n, nat_p n -> m c= m + n.
admit.
Qed.

Theorem nat_Subq_add_ex: forall n, nat_p n -> forall m, nat_p m -> n c= m -> exists k, nat_p k /\ m = k + n.
admit.
Qed.

Theorem add_nat_cancel_R : forall k, nat_p k -> forall m, nat_p m -> forall n, nat_p n -> k + n = m + n -> k = m.
admit.
Qed.

End NatAdd.

Section NatMul.

Infix + 360 right := add_nat.

Definition mul_nat : set->set->set := fun n m:set => nat_primrec 0 (fun _ r => n + r) m.
Infix * 355 right := mul_nat.

Theorem mul_nat_0R : forall n:set, n * 0 = 0.
admit.
Qed.

Theorem mul_nat_SR : forall n m, nat_p m -> n * ordsucc m = n + n * m.
admit.
Qed.

Theorem mul_nat_1R: forall n, n * 1 = n.
admit.
Qed.

Theorem mul_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n * m).
admit.
Qed.

Theorem mul_nat_0L : forall m:set, nat_p m -> 0 * m = 0.
admit.
Qed.

Theorem mul_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n * m = n * m + m.
admit.
Qed.

Theorem mul_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n * m = m * n.
admit.
Qed.

Theorem mul_add_nat_distrL : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> n * (m + k) = n * m + n * k.
admit.
Qed.

Theorem mul_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n*m)*k = n*(m*k).
admit.
Qed.

Theorem mul_nat_Subq_R : forall m n, nat_p m -> nat_p n -> m c= n -> forall k, nat_p k -> m * k c= n * k.
admit.
Qed.

Theorem mul_nat_Subq_L : forall m n, nat_p m -> nat_p n -> m c= n -> forall k, nat_p k -> k * m c= k * n.
admit.
Qed.

Theorem mul_nat_0_or_Subq: forall m, nat_p m -> forall n, nat_p n -> n = 0 \/ m c= m * n.
admit.
Qed.

(** If m times n = 0 for naturals m and n, then one must be 0. **)
Theorem mul_nat_0_inv : forall m, nat_p m -> forall n, nat_p n -> m * n = 0 -> m = 0 \/ n = 0.
admit.
Qed.

Theorem mul_nat_0m_1n_In: forall m, nat_p m -> forall n, nat_p n -> 0 :e m -> 1 :e n -> m :e m * n.
admit.
Qed.

Theorem nat_le1_cases: forall m, nat_p m -> m c= 1 -> m = 0 \/ m = 1.
admit.
Qed.

Definition Pi_nat : (set -> set) -> set -> set := fun f n =>
  nat_primrec 1 (fun i r => r * f i) n.

Theorem Pi_nat_0: forall f:set -> set, Pi_nat f 0 = 1.
admit.
Qed.

Theorem Pi_nat_S: forall f:set -> set, forall n, nat_p n -> Pi_nat f (ordsucc n) = Pi_nat f n * f n.
admit.
Qed.

Theorem Pi_nat_p: forall f:set -> set,
 forall n, nat_p n ->
     (forall i :e n, nat_p (f i))
  -> nat_p (Pi_nat f n).
admit.
Qed.

Theorem Pi_nat_0_inv: forall f:set->set,
  forall n, nat_p n ->
      (forall i :e n, nat_p (f i))
   -> Pi_nat f n = 0
   -> (exists i :e n, f i = 0).
admit.
Qed.

Definition exp_nat : set->set->set := fun n m:set => nat_primrec 1 (fun _ r => n * r) m.

Infix ^ 342 right := exp_nat.

Theorem exp_nat_0 : forall n, n ^ 0 = 1.
admit.
Qed.

Theorem exp_nat_S : forall n m, nat_p m -> n ^ (ordsucc m) = n * n ^ m.
admit.
Qed.

Theorem exp_nat_p : forall n, nat_p n -> forall m, nat_p m -> nat_p (n ^ m).
admit.
Qed.

Theorem exp_nat_1 : forall n, n ^ 1 = n.
admit.
Qed.

End NatMul.

Section form100_52.

Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.
Infix ^ 342 right := exp_nat.

Theorem Subq_Sing0_1 : {0} c= 1.
admit.
Qed.

Theorem Subq_1_Sing0 : 1 c= {0}.
admit.
Qed.

Theorem eq_1_Sing0 : 1 = {0}.
admit.
Qed.

Theorem Power_0_Sing_0 : Power 0 = {0}.
admit.
Qed.

Theorem equip_finite_Power: forall n, nat_p n -> forall X,
  equip X n -> equip (Power X) (2 ^ n).
admit.
Qed.

End form100_52.

Theorem ZF_closed_E : forall U, ZF_closed U ->
 forall p:prop,
 (Union_closed U ->
  Power_closed U ->
  Repl_closed U -> p)
 -> p.
admit.
Qed.

Theorem ZF_Union_closed : forall U, ZF_closed U ->
  forall X :e U, Union X :e U.
admit.
Qed.

Theorem ZF_Power_closed : forall U, ZF_closed U ->
  forall X :e U, Power X :e U.
admit.
Qed.

Theorem ZF_Repl_closed : forall U, ZF_closed U ->
  forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> {F x|x:eX} :e U.
admit.
Qed.

Theorem ZF_UPair_closed : forall U, ZF_closed U ->
  forall x y :e U, {x,y} :e U.
admit.
Qed.

Theorem ZF_Sing_closed : forall U, ZF_closed U ->
  forall x :e U, {x} :e U.
admit.
Qed.

Theorem ZF_binunion_closed : forall U, ZF_closed U ->
  forall X Y :e U, (X :\/: Y) :e U.
admit.
Qed.

Theorem ZF_ordsucc_closed : forall U, ZF_closed U ->
  forall x :e U, ordsucc x :e U.
admit.
Qed.

Theorem nat_p_UnivOf_Empty : forall n:set, nat_p n -> n :e UnivOf Empty.
admit.
Qed.

(* Unicode omega "3c9" *)
(* Parameter omega "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" "6fc30ac8f2153537e397b9ff2d9c981f80c151a73f96cf9d56ae2ee27dfd1eb2" *)
Definition omega : set := {n :e UnivOf Empty|nat_p n}.

Theorem omega_nat_p : forall n :e omega, nat_p n.
admit.
Qed.

Theorem nat_p_omega : forall n:set, nat_p n -> n :e omega.
admit.
Qed.

Theorem omega_ordsucc : forall n :e omega, ordsucc n :e omega.
admit.
Qed.

Theorem form100_22_v2: forall f:set -> set, ~inj (Power omega) omega f.
admit.
Qed.

Theorem form100_22_v3: forall g:set -> set, ~surj omega (Power omega) g.
admit.
Qed.

Theorem form100_22_v1: ~equip omega (Power omega).
admit.
Qed.

Theorem omega_TransSet : TransSet omega.
admit.
Qed.

Theorem omega_ordinal : ordinal omega.
admit.
Qed.

Theorem ordsucc_omega_ordinal: ordinal (ordsucc omega).
admit.
Qed.

Definition finite : set -> prop := fun X => exists n :e omega, equip X n.

Theorem nat_finite: forall n, nat_p n -> finite n.
admit.
Qed.

Theorem finite_ind : forall p:set -> prop,
    p Empty
 -> (forall X y, finite X -> y /:e X -> p X -> p (X :\/: {y}))
 -> forall X, finite X -> p X.
admit.
Qed.

Theorem finite_Empty: finite 0.
admit.
Qed.

Theorem Sing_finite: forall x, finite {x}.
admit.
Qed.

Theorem adjoin_finite: forall X y, finite X -> finite (X :\/: {y}).
admit.
Qed.

Theorem binunion_finite: forall X, finite X -> forall Y, finite Y -> finite (X :\/: Y).
admit.
Qed.

Theorem famunion_nat_finite : forall X:set -> set, forall n, nat_p n -> (forall i :e n, finite (X i)) -> finite (\/_ i :e n, X i).
admit.
Qed.

Theorem Subq_finite : forall X, finite X -> forall Y, Y c= X -> finite Y.
admit.
Qed.

Definition infinite : set -> prop := fun A => ~finite A.

Section InfinitePrimes.

Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.

Definition divides_nat : set -> set -> prop :=
  fun m n => m :e omega /\ n :e omega /\ exists k :e omega, m * k = n.

Theorem divides_nat_ref: forall n, nat_p n -> divides_nat n n.
admit.
Qed.

Theorem divides_nat_tra: forall k m n, divides_nat k m -> divides_nat m n -> divides_nat k n.
admit.
Qed.

Definition prime_nat : set -> prop :=
  fun n => n :e omega /\ 1 :e n /\ forall k :e omega, divides_nat k n -> k = 1 \/ k = n.

Theorem divides_nat_mulR: forall m n :e omega, divides_nat m (m * n).
admit.
Qed.

Theorem divides_nat_mulL: forall m n :e omega, divides_nat n (m * n).
admit.
Qed.

Theorem Pi_nat_divides: forall f:set->set,
  forall n, nat_p n ->
      (forall i :e n, nat_p (f i))
   -> (forall i :e n, divides_nat (f i) (Pi_nat f n)).
admit.
Qed.

Definition composite_nat : set -> prop :=
  fun n => n :e omega /\ exists k m :e omega, 1 :e k /\ 1 :e m /\ k * m = n.

Theorem prime_nat_or_composite_nat: forall n :e omega, 1 :e n -> prime_nat n \/ composite_nat n.
admit.
Qed.

Theorem prime_nat_divisor_ex: forall n, nat_p n -> 1 :e n -> exists p, prime_nat p /\ divides_nat p n.
admit.
Qed.

Theorem nat_1In_not_divides_ordsucc: forall m n, 1 :e m -> divides_nat m n -> ~divides_nat m (ordsucc n).
admit.
Qed.

Definition primes : set := {n :e omega|prime_nat n}.

Theorem form100_11_infinite_primes: infinite primes.
admit.
Qed.

End InfinitePrimes.

Section InfiniteRamsey.

Infix + 360 right := add_nat.

Theorem atleastp_omega_infinite: forall X, atleastp omega X -> infinite X.
admit.
Qed.

Theorem infinite_remove1: forall X, infinite X -> forall y, infinite (X :\: {y}).
admit.
Qed.

Theorem infinite_Finite_Subq_ex: forall X, infinite X ->
  forall n, nat_p n -> exists Y c= X, equip Y n.
admit.
Qed.

Theorem infiniteRamsey_lem: forall X, forall f g f':set -> set,
    infinite X
 -> (forall Z c= X, infinite Z -> f Z c= Z /\ infinite (f Z))
 -> (forall Z c= X, infinite Z -> g Z :e Z /\ g Z /:e f Z)
 -> f' 0 = f X
 -> (forall m, nat_p m -> f' (ordsucc m) = f (f' m))
 -> (forall m, nat_p m -> f' m c= X /\ infinite (f' m))
 /\ (forall m m' :e omega, m c= m' -> f' m' c= f' m)
 /\ (forall m m' :e omega, g (f' m) = g (f' m') -> m = m').
admit.
Qed.

Theorem infiniteRamsey: forall c, nat_p c -> forall n, nat_p n ->
  forall X, infinite X -> forall C:set -> set,
    (forall Y c= X, equip Y n -> C Y :e c)
 -> exists H c= X, exists i :e c, infinite H /\ forall Y c= H, equip Y n -> C Y = i.
admit.
Qed.

End InfiniteRamsey.

(*** Injection of set into itself that will correspond to x |-> (1,x) after pairing is defined. ***)
Definition Inj1 : set -> set := In_rec_i (fun X f => {0} :\/: {f x|x :e X}).

Theorem Inj1_eq : forall X:set, Inj1 X = {0} :\/: {Inj1 x|x :e X}.
admit.
Qed.

Theorem Inj1I1 : forall X:set, 0 :e Inj1 X.
admit.
Qed.

Theorem Inj1I2 : forall X x:set, x :e X -> Inj1 x :e Inj1 X.
admit.
Qed.

Theorem Inj1E : forall X y:set, y :e Inj1 X -> y = 0 \/ exists x :e X, y = Inj1 x.
admit.
Qed.

Theorem Inj1NE1 : forall x:set, Inj1 x <> 0.
admit.
Qed.

Theorem Inj1NE2 : forall x:set, Inj1 x /:e {0}.
admit.
Qed.

(*** Injection of set into itself that will correspond to x |-> (0,x) after pairing is defined. ***)
Definition Inj0 : set -> set := fun X => {Inj1 x|x :e X}.

Theorem Inj0I : forall X x:set, x :e X -> Inj1 x :e Inj0 X.
admit.
Qed.

Theorem Inj0E : forall X y:set, y :e Inj0 X -> exists x:set, x :e X /\ y = Inj1 x.
admit.
Qed.

(*** Unj : Left inverse of Inj1 and Inj0 ***)
Definition Unj : set -> set := In_rec_i (fun X f => {f x|x :e X :\: {0}}).

Theorem Unj_eq : forall X:set, Unj X = {Unj x|x :e X :\: {0}}.
admit.
Qed.

Theorem Unj_Inj1_eq : forall X:set, Unj (Inj1 X) = X.
admit.
Qed.

Theorem Inj1_inj : forall X Y:set, Inj1 X = Inj1 Y -> X = Y.
admit.
Qed.

Theorem Unj_Inj0_eq : forall X:set, Unj (Inj0 X) = X.
admit.
Qed.

Theorem Inj0_inj : forall X Y:set, Inj0 X = Inj0 Y -> X = Y.
admit.
Qed.

Theorem Inj0_0 : Inj0 0 = 0.
admit.
Qed.

Theorem Inj0_Inj1_neq : forall X Y:set, Inj0 X <> Inj1 Y.
admit.
Qed.

(*** setsum ***)
Definition setsum : set -> set -> set := fun X Y => {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.
(* Unicode :+: "002b" *)
Infix :+: 450 left := setsum.

Theorem Inj0_setsum : forall X Y x:set, x :e X -> Inj0 x :e X :+: Y.
admit.
Qed.

Theorem Inj1_setsum : forall X Y y:set, y :e Y -> Inj1 y :e X :+: Y.
admit.
Qed.

Theorem setsum_Inj_inv : forall X Y z:set, z :e X :+: Y -> (exists x :e X, z = Inj0 x) \/ (exists y :e Y, z = Inj1 y).
admit.
Qed.

Theorem Inj0_setsum_0L : forall X:set, 0 :+: X = Inj0 X.
admit.
Qed.

Theorem Inj1_setsum_1L : forall X:set, 1 :+: X = Inj1 X.
admit.
Qed.

Section pair_setsum.
Let pair := setsum.
Definition proj0 : set -> set := fun Z => {Unj z|z :e Z, exists x:set, Inj0 x = z}.
Definition proj1 : set -> set := fun Z => {Unj z|z :e Z, exists y:set, Inj1 y = z}.

Theorem Inj0_pair_0_eq : Inj0 = pair 0.
admit.
Qed.

Theorem Inj1_pair_1_eq : Inj1 = pair 1.
admit.
Qed.

Theorem pairI0 : forall X Y x, x :e X -> pair 0 x :e pair X Y.
admit.
Qed.

Theorem pairI1 : forall X Y y, y :e Y -> pair 1 y :e pair X Y.
admit.
Qed.

Theorem pairE : forall X Y z, z :e pair X Y -> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
admit.
Qed.

Theorem pairE0 : forall X Y x, pair 0 x :e pair X Y -> x :e X.
admit.
Qed.

Theorem pairE1 : forall X Y y, pair 1 y :e pair X Y -> y :e Y.
admit.
Qed.

Theorem proj0I : forall w u:set, pair 0 u :e w -> u :e proj0 w.
admit.
Qed.

Theorem proj0E : forall w u:set, u :e proj0 w -> pair 0 u :e w.
admit.
Qed.

Theorem proj1I : forall w u:set, pair 1 u :e w -> u :e proj1 w.
admit.
Qed.

Theorem proj1E : forall w u:set, u :e proj1 w -> pair 1 u :e w.
admit.
Qed.

Theorem proj0_pair_eq : forall X Y:set, proj0 (pair X Y) = X.
admit.
Qed.

Theorem proj1_pair_eq : forall X Y:set, proj1 (pair X Y) = Y.
admit.
Qed.

Opaque add_nat mul_nat omega ordsucc setminus binintersect ReplSep Sep famunion binunion Sing UPair exactly1of2 If_i If_ii If_iii Descr_Vo1 Descr_iii Descr_ii inv In_rec_i In_rec_ii In_rec_iii.

(*** Sigma X Y = {(x,y) | x in X, y in Y x} ***)
Definition Sigma : set -> (set -> set) -> set :=
fun X Y => \/_ x :e X, {pair x y|y :e Y x}.
(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.

Theorem Sigma_eta_proj0_proj1 : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z /\ proj0 z :e X /\ proj1 z :e Y (proj0 z).
admit.
Qed.

Theorem proj0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj0 z :e X.
admit.
Qed.

Theorem proj1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj1 z :e Y (proj0 z).
admit.
Qed.

Theorem pair_Sigma : forall X:set, forall Y:set -> set, forall x :e X, forall y :e Y x, pair x y :e Sigma_ x :e X, Y x.
admit.
Qed.

Theorem pair_Sigma_E1 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> y :e Y x.
admit.
Qed.

Theorem Sigma_E : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) -> exists x :e X, exists y :e Y x, z = pair x y.
admit.
Qed.

Definition setprod : set->set->set := fun X Y:set => Sigma_ x :e X, Y.
(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.
(*** lam X F = {(x,y) | x :e X, y :e F x} = \/_{x :e X} {(x,y) | y :e (F x)} = Sigma X F ***)
Let lam : set -> (set -> set) -> set := Sigma.
(***  ap f x = {proj1 z | z :e f,  exists y, z = pair x y}} ***)
Definition ap : set -> set -> set := fun f x => {proj1 z|z :e f, exists y:set, z = pair x y}.
Notation SetImplicitOp ap.
Notation SetLam Sigma.

Theorem lamI : forall X:set, forall F:set->set, forall x :e X, forall y :e F x, pair x y :e fun x :e X => F x.
admit.
Qed.

Theorem lamE : forall X:set, forall F:set->set, forall z:set, z :e (fun x :e X => F x) -> exists x :e X, exists y :e F x, z = pair x y.
admit.
Qed.

Theorem apI : forall f x y, pair x y :e f -> y :e f x.
admit.
Qed.

Theorem apE : forall f x y, y :e f x -> pair x y :e f.
admit.
Qed.

Theorem beta : forall X:set, forall F:set -> set, forall x:set, x :e X -> (fun x :e X => F x) x = F x.
admit.
Qed.

Theorem proj0_ap_0 : forall u, proj0 u = u 0.
admit.
Qed.

Theorem proj1_ap_1 : forall u, proj1 u = u 1.
admit.
Qed.

Theorem pair_ap_0 : forall x y:set, (pair x y) 0 = x.
admit.
Qed.

Theorem pair_ap_1 : forall x y:set, (pair x y) 1 = y.
admit.
Qed.

Theorem ap0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 0) :e X.
admit.
Qed.

Theorem ap1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 1) :e (Y (z 0)).
admit.
Qed.

Definition pair_p:set->prop
:= fun u:set => pair (u 0) (u 1) = u.

Theorem pair_p_I : forall x y, pair_p (pair x y).
admit.
Qed.

Theorem Subq_2_UPair01 : 2 c= {0,1}.
admit.
Qed.

Theorem tuple_pair : forall x y:set, pair x y = (x,y).
admit.
Qed.

Definition Pi : set -> (set -> set) -> set := fun X Y => {f :e Power (Sigma_ x :e X, Union (Y x)) | forall x :e X, f x :e Y x}.
(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

Theorem PiI : forall X:set, forall Y:set->set, forall f:set,
    (forall u :e f, pair_p u /\ u 0 :e X) -> (forall x :e X, f x :e Y x) -> f :e Pi_ x :e X, Y x.
admit.
Qed.

Theorem lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set,
 (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
admit.
Qed.

Theorem ap_Pi : forall X:set, forall Y:set -> set, forall f:set, forall x:set, f :e (Pi_ x :e X, Y x) -> x :e X -> f x :e Y x.
admit.
Qed.

Definition setexp : set->set->set := fun X Y:set => Pi_ y :e Y, X.
(* Superscript :^: *)
Infix :^: 430 left := setexp.

Theorem pair_tuple_fun : pair = (fun x y => (x,y)).
admit.
Qed.

Section Tuples.
Variable x0 x1: set.

Theorem tuple_2_0_eq: (x0,x1) 0 = x0.
admit.
Qed.

Theorem tuple_2_1_eq: (x0,x1) 1 = x1.
admit.
Qed.

End Tuples.

Theorem ReplEq_setprod_ext : forall X Y, forall F G:set -> set -> set, (forall x :e X, forall y :e Y, F x y = G x y) -> {F (w 0) (w 1)|w :e X :*: Y} = {G (w 0) (w 1)|w :e X :*: Y}.
admit.
Qed.

Theorem lamI2 : forall X, forall F:set->set, forall x :e X, forall y :e F x, (x,y) :e fun x :e X => F x.
admit.
Qed.

Theorem tuple_2_Sigma : forall X:set, forall Y:set -> set, forall x :e X, forall y :e Y x, (x,y) :e Sigma_ x :e X, Y x.
admit.
Qed.

Theorem tuple_2_setprod : forall X:set, forall Y:set, forall x :e X, forall y :e Y, (x,y) :e X :*: Y.
admit.
Qed.

End pair_setsum.
(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.
(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.
(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.
(* Superscript :^: *)
Infix :^: 430 left := setexp.
(* Parameter DescrR_i_io_1 "1f005fdad5c6f98763a15a5e5539088f5d43b7d1be866b0b204fda1ce9ed9248" "1d3fd4a14ef05bd43f5c147d7966cf05fd2fed808eea94f56380454b9a6044b2" *)
Definition DescrR_i_io_1 : (set->(set->prop)->prop) -> set := fun R => Eps_i (fun x => (exists y:set -> prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z)).
(* Parameter DescrR_i_io_2 "28d8599686476258c12dcc5fc5f5974335febd7d5259e1a8e5918b7f9b91ca03" "768eb2ad186988375e6055394e36e90c81323954b8a44eb08816fb7a84db2272" *)
Definition DescrR_i_io_2 : (set->(set->prop)->prop) -> set->prop := fun R => Descr_Vo1 (fun y => R (DescrR_i_io_1 R) y).

Theorem DescrR_i_io_12 : forall R:set->(set->prop)->prop, (exists x, (exists y:set->prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z)) -> R (DescrR_i_io_1 R) (DescrR_i_io_2 R).
admit.
Qed.

(** Conway describes this way of formalizing in ZF in an appendix to Part Zero of his book,
    but rejects formalization in favor of "Mathematician's Liberation."
 **)
Definition PNoEq_ : set -> (set -> prop) -> (set -> prop) -> prop
 := fun alpha p q => forall beta :e alpha, p beta <-> q beta.

Theorem PNoEq_ref_ : forall alpha, forall p:set -> prop, PNoEq_ alpha p p.
admit.
Qed.

Theorem PNoEq_sym_ : forall alpha, forall p q:set -> prop, PNoEq_ alpha p q -> PNoEq_ alpha q p.
admit.
Qed.

Theorem PNoEq_tra_ : forall alpha, forall p q r:set -> prop, PNoEq_ alpha p q -> PNoEq_ alpha q r -> PNoEq_ alpha p r.
admit.
Qed.

Theorem PNoEq_antimon_ : forall p q:set -> prop, forall alpha, ordinal alpha -> forall beta :e alpha, PNoEq_ alpha p q -> PNoEq_ beta p q.
admit.
Qed.

Definition PNoLt_ : set -> (set -> prop) -> (set -> prop) -> prop
 := fun alpha p q => exists beta :e alpha, PNoEq_ beta p q /\ ~p beta /\ q beta.

Theorem PNoLt_E_ : forall alpha, forall p q:set -> prop, PNoLt_ alpha p q ->
  forall R:prop, (forall beta, beta :e alpha -> PNoEq_ beta p q -> ~p beta -> q beta -> R) -> R.
admit.
Qed.

Theorem PNoLt_irref_ : forall alpha, forall p:set -> prop, ~PNoLt_ alpha p p.
admit.
Qed.

Theorem PNoLt_mon_ : forall p q:set -> prop, forall alpha, ordinal alpha -> forall beta :e alpha, PNoLt_ beta p q -> PNoLt_ alpha p q.
admit.
Qed.

Theorem PNoLt_trichotomy_or_ : forall p q:set -> prop, forall alpha, ordinal alpha
  -> PNoLt_ alpha p q \/ PNoEq_ alpha p q \/ PNoLt_ alpha q p.
admit.
Qed.

(* Parameter PNoLt "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" "8f57a05ce4764eff8bc94b278352b6755f1a46566cd7220a5488a4a595a47189" *)
Definition PNoLt : set -> (set -> prop) -> set -> (set -> prop) -> prop
 := fun alpha p beta q =>
        PNoLt_ (alpha :/\: beta) p q
     \/ alpha :e beta /\ PNoEq_ alpha p q /\ q alpha
     \/ beta :e alpha /\ PNoEq_ beta p q /\ ~p beta.

Theorem PNoLtI1 : forall alpha beta, forall p q:set -> prop,
  PNoLt_ (alpha :/\: beta) p q -> PNoLt alpha p beta q.
admit.
Qed.

Theorem PNoLtI2 : forall alpha beta, forall p q:set -> prop,
  alpha :e beta -> PNoEq_ alpha p q -> q alpha -> PNoLt alpha p beta q.
admit.
Qed.

Theorem PNoLtI3 : forall alpha beta, forall p q:set -> prop,
  beta :e alpha -> PNoEq_ beta p q -> ~p beta -> PNoLt alpha p beta q.
admit.
Qed.

Theorem PNoLtE : forall alpha beta, forall p q:set -> prop,
  PNoLt alpha p beta q ->
  forall R:prop,
      (PNoLt_ (alpha :/\: beta) p q -> R)
   -> (alpha :e beta -> PNoEq_ alpha p q -> q alpha -> R)
   -> (beta :e alpha -> PNoEq_ beta p q -> ~p beta -> R)
   -> R.
admit.
Qed.

Theorem PNoLt_irref : forall alpha, forall p:set -> prop, ~PNoLt alpha p alpha p.
admit.
Qed.

Theorem PNoLt_trichotomy_or : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q \/ PNoLt beta q alpha p.
admit.
Qed.

Theorem PNoLtEq_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoEq_ beta q r -> PNoLt alpha p beta r.
admit.
Qed.

Theorem PNoEqLt_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoEq_ alpha p q -> PNoLt alpha q beta r -> PNoLt alpha p beta r.
admit.
Qed.

Theorem PNoLt_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoLt beta q gamma r -> PNoLt alpha p gamma r.
admit.
Qed.

Definition PNoLe : set -> (set -> prop) -> set -> (set -> prop) -> prop
   := fun alpha p beta q => PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q.

Theorem PNoLeI1 : forall alpha beta, forall p q:set -> prop,
   PNoLt alpha p beta q -> PNoLe alpha p beta q.
admit.
Qed.

Theorem PNoLeI2 : forall alpha, forall p q:set -> prop,
   PNoEq_ alpha p q -> PNoLe alpha p alpha q.
admit.
Qed.

Theorem PNoLe_ref : forall alpha, forall p:set -> prop, PNoLe alpha p alpha p.
admit.
Qed.

Theorem PNoLe_antisym : forall alpha beta, ordinal alpha -> ordinal beta ->
 forall p q:set -> prop,
 PNoLe alpha p beta q -> PNoLe beta q alpha p -> alpha = beta /\ PNoEq_ alpha p q.
admit.
Qed.

Theorem PNoLtLe_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoLe beta q gamma r -> PNoLt alpha p gamma r.
admit.
Qed.

Theorem PNoLeLt_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoLt beta q gamma r -> PNoLt alpha p gamma r.
admit.
Qed.

Theorem PNoEqLe_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoEq_ alpha p q -> PNoLe alpha q beta r -> PNoLe alpha p beta r.
admit.
Qed.

Theorem PNoLe_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoLe beta q gamma r -> PNoLe alpha p gamma r.
admit.
Qed.

Definition PNo_downc : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
 := fun L alpha p => exists beta, ordinal beta /\ exists q:set -> prop, L beta q /\ PNoLe alpha p beta q.
Definition PNo_upc : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
 := fun R alpha p => exists beta, ordinal beta /\ exists q:set -> prop, R beta q /\ PNoLe beta q alpha p.

Theorem PNoLe_downc : forall L:set -> (set -> prop) -> prop, forall alpha beta, forall p q:set -> prop,
  ordinal alpha -> ordinal beta ->
  PNo_downc L alpha p -> PNoLe beta q alpha p -> PNo_downc L beta q.
admit.
Qed.

Theorem PNo_downc_ref : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, L alpha p -> PNo_downc L alpha p.
admit.
Qed.

Theorem PNo_upc_ref : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, R alpha p -> PNo_upc R alpha p.
admit.
Qed.

Theorem PNoLe_upc : forall R:set -> (set -> prop) -> prop, forall alpha beta, forall p q:set -> prop,
  ordinal alpha -> ordinal beta ->
  PNo_upc R alpha p -> PNoLe alpha p beta q -> PNo_upc R beta q.
admit.
Qed.

Definition PNoLt_pwise : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> prop
  := fun L R => forall gamma, ordinal gamma -> forall p:set -> prop, L gamma p -> forall delta, ordinal delta -> forall q:set -> prop, R delta q -> PNoLt gamma p delta q.

Theorem PNoLt_pwise_downc_upc : forall L R:set -> (set -> prop) -> prop,
    PNoLt_pwise L R -> PNoLt_pwise (PNo_downc L) (PNo_upc R).
admit.
Qed.

Definition PNo_rel_strict_upperbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L alpha p =>
       forall beta :e alpha, forall q:set -> prop, PNo_downc L beta q -> PNoLt beta q alpha p.
Definition PNo_rel_strict_lowerbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun R alpha p =>
       forall beta :e alpha, forall q:set -> prop, PNo_upc R beta q -> PNoLt alpha p beta q.
Definition PNo_rel_strict_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_rel_strict_upperbd L alpha p /\ PNo_rel_strict_lowerbd R alpha p.

Theorem PNoEq_rel_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L alpha q.
admit.
Qed.

Theorem PNo_rel_strict_upperbd_antimon : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L beta p.
admit.
Qed.

Theorem PNoEq_rel_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R alpha q.
admit.
Qed.

Theorem PNo_rel_strict_lowerbd_antimon : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R beta p.
admit.
Qed.

Theorem PNoEq_rel_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R alpha q.
admit.
Qed.

Theorem PNo_rel_strict_imv_antimon : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R beta p.
admit.
Qed.

Definition PNo_rel_strict_uniq_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_rel_strict_imv L R alpha p /\ forall q:set -> prop, PNo_rel_strict_imv L R alpha q -> PNoEq_ alpha p q.
Definition PNo_rel_strict_split_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p =>
         PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha)
      /\ PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha).

Theorem PNo_extend0_eq : forall alpha, forall p:set -> prop, PNoEq_ alpha p (fun delta => p delta /\ delta <> alpha).
admit.
Qed.

Theorem PNo_extend1_eq : forall alpha, forall p:set -> prop, PNoEq_ alpha p (fun delta => p delta \/ delta = alpha).
admit.
Qed.

Theorem PNo_rel_imv_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha ->
      (exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p)
   \/ (exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p).
admit.
Qed.

Definition PNo_lenbdd : set -> (set -> (set -> prop) -> prop) -> prop
  := fun alpha L => forall beta, forall p:set -> prop, L beta p -> beta :e alpha.

Theorem PNo_lenbdd_strict_imv_extend0 : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha).
admit.
Qed.

Theorem PNo_lenbdd_strict_imv_extend1 : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha).
admit.
Qed.

Theorem PNo_lenbdd_strict_imv_split : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_split_imv L R alpha p.
admit.
Qed.

Theorem PNo_rel_imv_bdd_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta :e ordsucc alpha,
      exists p:set -> prop, PNo_rel_strict_split_imv L R beta p.
admit.
Qed.

Definition PNo_strict_upperbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L alpha p =>
       forall beta, ordinal beta -> forall q:set -> prop, L beta q -> PNoLt beta q alpha p.
Definition PNo_strict_lowerbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun R alpha p =>
       forall beta, ordinal beta -> forall q:set -> prop, R beta q -> PNoLt alpha p beta q.
Definition PNo_strict_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_strict_upperbd L alpha p /\ PNo_strict_lowerbd R alpha p.

Theorem PNoEq_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_upperbd L alpha p -> PNo_strict_upperbd L alpha q.
admit.
Qed.

Theorem PNoEq_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_lowerbd R alpha p -> PNo_strict_lowerbd R alpha q.
admit.
Qed.

Theorem PNoEq_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_imv L R alpha p -> PNo_strict_imv L R alpha q.
admit.
Qed.

Theorem PNo_strict_upperbd_imp_rel_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L beta p.
admit.
Qed.

Theorem PNo_strict_lowerbd_imp_rel_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R beta p.
admit.
Qed.

Theorem PNo_strict_imv_imp_rel_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_imv L R alpha p -> PNo_rel_strict_imv L R beta p.
admit.
Qed.

Theorem PNo_rel_split_imv_imp_strict_imv : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> forall p:set -> prop,
       PNo_rel_strict_split_imv L R alpha p
    -> PNo_strict_imv L R alpha p.
admit.
Qed.

Theorem PNo_lenbdd_strict_imv_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta :e ordsucc alpha,
      exists p:set -> prop, PNo_strict_imv L R beta p.
admit.
Qed.

Definition PNo_least_rep : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R beta p => ordinal beta
       /\ PNo_strict_imv L R beta p
       /\ forall gamma :e beta,
           forall q:set -> prop, ~PNo_strict_imv L R gamma q.
Definition PNo_least_rep2 : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R beta p => PNo_least_rep L R beta p /\ forall x, x /:e beta -> ~p x.

Theorem PNo_strict_imv_pred_eq : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha -> forall p q:set -> prop,
     PNo_least_rep L R alpha p
  -> PNo_strict_imv L R alpha q
  -> forall beta :e alpha, p beta <-> q beta.
admit.
Qed.

Theorem PNo_lenbdd_least_rep2_exuniq2 : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta,
        (exists p:set -> prop, PNo_least_rep2 L R beta p)
     /\ (forall p q:set -> prop, PNo_least_rep2 L R beta p -> PNo_least_rep2 L R beta q -> p = q).
admit.
Qed.

(* Parameter PNo_bd "1b39e85278dd9e820e7b6258957386ac55934d784aa3702c57a28ec807453b01" "ed76e76de9b58e621daa601cca73b4159a437ba0e73114924cb92ec8044f2aa2" *)
Definition PNo_bd : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set
 := fun L R => DescrR_i_io_1 (PNo_least_rep2 L R).
(* Parameter PNo_pred "be07c39b18a3aa93f066f4c064fee3941ec27cfd07a4728b6209135c77ce5704" "b2d51dcfccb9527e9551b0d0c47d891c9031a1d4ee87bba5a9ae5215025d107a" *)
Definition PNo_pred : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> prop
 := fun L R => DescrR_i_io_2 (PNo_least_rep2 L R).

Theorem PNo_bd_pred_lem : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_least_rep2 L R (PNo_bd L R) (PNo_pred L R).
admit.
Qed.

Theorem PNo_bd_pred : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_least_rep L R (PNo_bd L R) (PNo_pred L R).
admit.
Qed.

Theorem PNo_bd_In : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_bd L R :e ordsucc alpha.
admit.
Qed.

Opaque Sigma Pi ap PNo_pred PNo_bd PNoLt DescrR_i_io_1 DescrR_i_io_2.

Section TaggedSets.
Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Theorem not_TransSet_Sing1 : ~TransSet {1}.
admit.
Qed.

Theorem not_ordinal_Sing1 : ~ordinal {1}.
admit.
Qed.

Theorem tagged_not_ordinal : forall y, ~ordinal (y ').
admit.
Qed.

Theorem tagged_notin_ordinal : forall alpha y, ordinal alpha -> (y ') /:e alpha.
admit.
Qed.

Theorem tagged_eqE_Subq : forall alpha beta, ordinal alpha -> alpha ' = beta ' -> alpha c= beta.
admit.
Qed.

Theorem tagged_eqE_eq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha ' = beta ' -> alpha = beta.
admit.
Qed.

Theorem tagged_ReplE : forall alpha beta, ordinal alpha -> ordinal beta -> beta ' :e {gamma '|gamma :e alpha} -> beta :e alpha.
admit.
Qed.

Theorem ordinal_notin_tagged_Repl : forall alpha Y, ordinal alpha -> alpha /:e {y '|y :e Y}.
admit.
Qed.

Definition SNoElts_ : set -> set := fun alpha => alpha :\/: {beta '|beta :e alpha}.

Theorem SNoElts_mon : forall alpha beta, alpha c= beta -> SNoElts_ alpha c= SNoElts_ beta.
admit.
Qed.

Definition SNo_ : set -> set -> prop := fun alpha x =>
    x c= SNoElts_ alpha
 /\ forall beta :e alpha, exactly1of2 (beta ' :e x) (beta :e x).
Definition PSNo : set -> (set -> prop) -> set :=
  fun alpha p => {beta :e alpha|p beta} :\/: {beta '|beta :e alpha, ~p beta}.

Theorem PNoEq_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, PNoEq_ alpha (fun beta => beta :e PSNo alpha p) p.
admit.
Qed.

Theorem SNo_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, SNo_ alpha (PSNo alpha p).
admit.
Qed.

Theorem SNo_PSNo_eta_ : forall alpha x, ordinal alpha -> SNo_ alpha x -> x = PSNo alpha (fun beta => beta :e x).
admit.
Qed.

(* Parameter SNo "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" "11faa7a742daf8e4f9aaf08e90b175467e22d0e6ad3ed089af1be90cfc17314b" *)
Definition SNo : set -> prop := fun x => exists alpha, ordinal alpha /\ SNo_ alpha x.

Theorem SNo_SNo : forall alpha, ordinal alpha -> forall z, SNo_ alpha z -> SNo z.
admit.
Qed.

(* Parameter SNoLev "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" "293b77d05dab711767d698fb4484aab2a884304256765be0733e6bd5348119e8" *)
Definition SNoLev : set -> set := fun x => Eps_i (fun alpha => ordinal alpha /\ SNo_ alpha x).

Theorem SNoLev_uniq_Subq : forall x alpha beta, ordinal alpha -> ordinal beta -> SNo_ alpha x -> SNo_ beta x -> alpha c= beta.
admit.
Qed.

Theorem SNoLev_uniq : forall x alpha beta, ordinal alpha -> ordinal beta -> SNo_ alpha x -> SNo_ beta x -> alpha = beta.
admit.
Qed.

Theorem SNoLev_prop : forall x, SNo x -> ordinal (SNoLev x) /\ SNo_ (SNoLev x) x.
admit.
Qed.

Theorem SNoLev_ordinal : forall x, SNo x -> ordinal (SNoLev x).
admit.
Qed.

Theorem SNoLev_ : forall x, SNo x -> SNo_ (SNoLev x) x.
admit.
Qed.

Theorem SNo_PSNo_eta : forall x, SNo x -> x = PSNo (SNoLev x) (fun beta => beta :e x).
admit.
Qed.

Theorem SNoLev_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, SNoLev (PSNo alpha p) = alpha.
admit.
Qed.

Theorem SNo_Subq : forall x y, SNo x -> SNo y -> SNoLev x c= SNoLev y -> (forall alpha :e SNoLev x, alpha :e x <-> alpha :e y) -> x c= y.
admit.
Qed.

Definition SNoEq_ : set -> set -> set -> prop
 := fun alpha x y => PNoEq_ alpha (fun beta => beta :e x) (fun beta => beta :e y).

Theorem SNoEq_I : forall alpha x y, (forall beta :e alpha, beta :e x <-> beta :e y) -> SNoEq_ alpha x y.
admit.
Qed.

Theorem SNo_eq : forall x y, SNo x -> SNo y -> SNoLev x = SNoLev y -> SNoEq_ (SNoLev x) x y -> x = y.
admit.
Qed.

End TaggedSets.
Definition SNoLt : set -> set -> prop :=
  fun x y => PNoLt (SNoLev x) (fun beta => beta :e x) (SNoLev y) (fun beta => beta :e y).
Infix < 490 := SNoLt.
Definition SNoLe : set -> set -> prop :=
  fun x y => PNoLe (SNoLev x) (fun beta => beta :e x) (SNoLev y) (fun beta => beta :e y).
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Theorem SNoLtLe : forall x y, x < y -> x <= y.
admit.
Qed.

Theorem SNoLeE : forall x y, SNo x -> SNo y -> x <= y -> x < y \/ x = y.
admit.
Qed.

Theorem SNoEq_sym_ : forall alpha x y, SNoEq_ alpha x y -> SNoEq_ alpha y x.
admit.
Qed.

Theorem SNoEq_tra_ : forall alpha x y z, SNoEq_ alpha x y -> SNoEq_ alpha y z -> SNoEq_ alpha x z.
admit.
Qed.

Theorem SNoLtE : forall x y, SNo x -> SNo y -> x < y ->
 forall p:prop,
    (forall z, SNo z -> SNoLev z :e SNoLev x :/\: SNoLev y -> SNoEq_ (SNoLev z) z x -> SNoEq_ (SNoLev z) z y -> x < z -> z < y -> SNoLev z /:e x -> SNoLev z :e y -> p)
 -> (SNoLev x :e SNoLev y -> SNoEq_ (SNoLev x) x y -> SNoLev x :e y -> p)
 -> (SNoLev y :e SNoLev x -> SNoEq_ (SNoLev y) x y -> SNoLev y /:e x -> p)
 -> p.
admit.
Qed.

(** The analogous thm to PNoLtI1 can be recovered by SNoLt_tra (transitivity) and SNoLtI2 and SNoLtI3. **)
Theorem SNoLtI2 : forall x y,
     SNoLev x :e SNoLev y
  -> SNoEq_ (SNoLev x) x y
  -> SNoLev x :e y
  -> x < y.
admit.
Qed.

Theorem SNoLtI3 : forall x y,
     SNoLev y :e SNoLev x
  -> SNoEq_ (SNoLev y) x y
  -> SNoLev y /:e x
  -> x < y.
admit.
Qed.

Theorem SNoLt_irref : forall x, ~SNoLt x x.
admit.
Qed.

Theorem SNoLt_trichotomy_or : forall x y, SNo x -> SNo y -> x < y \/ x = y \/ y < x.
admit.
Qed.

Theorem SNoLt_trichotomy_or_impred : forall x y, SNo x -> SNo y ->
  forall p:prop,
      (x < y -> p)
   -> (x = y -> p)
   -> (y < x -> p)
   -> p.
admit.
Qed.

Theorem SNoLt_tra : forall x y z, SNo x -> SNo y -> SNo z -> x < y -> y < z -> x < z.
admit.
Qed.

Theorem SNoLe_ref : forall x, SNoLe x x.
admit.
Qed.

Theorem SNoLe_antisym : forall x y, SNo x -> SNo y -> x <= y -> y <= x -> x = y.
admit.
Qed.

Theorem SNoLtLe_tra : forall x y z, SNo x -> SNo y -> SNo z -> x < y -> y <= z -> x < z.
admit.
Qed.

Theorem SNoLeLt_tra : forall x y z, SNo x -> SNo y -> SNo z -> x <= y -> y < z -> x < z.
admit.
Qed.

Theorem SNoLe_tra : forall x y z, SNo x -> SNo y -> SNo z -> x <= y -> y <= z -> x <= z.
admit.
Qed.

Theorem SNoLtLe_or : forall x y, SNo x -> SNo y -> x < y \/ y <= x.
admit.
Qed.

Theorem SNoLt_PSNo_PNoLt : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PSNo alpha p < PSNo beta q -> PNoLt alpha p beta q.
admit.
Qed.

Theorem PNoLt_SNoLt_PSNo : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PNoLt alpha p beta q -> PSNo alpha p < PSNo beta q.
admit.
Qed.

Definition SNoCut : set -> set -> set :=
  fun L R => PSNo (PNo_bd (fun alpha p => ordinal alpha /\ PSNo alpha p :e L) (fun alpha p => ordinal alpha /\ PSNo alpha p :e R)) (PNo_pred (fun alpha p => ordinal alpha /\ PSNo alpha p :e L) (fun alpha p => ordinal alpha /\ PSNo alpha p :e R)).
Definition SNoCutP : set -> set -> prop :=
 fun L R =>
      (forall x :e L, SNo x)
   /\ (forall y :e R, SNo y)
   /\ (forall x :e L, forall y :e R, x < y).

Theorem SNoCutP_SNoCut : forall L R, SNoCutP L R
 -> SNo (SNoCut L R)
 /\ SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y)))
 /\ (forall x :e L, x < SNoCut L R)
 /\ (forall y :e R, SNoCut L R < y)
 /\ (forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z).
admit.
Qed.

Theorem SNoCutP_SNoCut_impred : forall L R, SNoCutP L R
 -> forall p:prop,
      (SNo (SNoCut L R)
    -> SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y)))
    -> (forall x :e L, x < SNoCut L R)
    -> (forall y :e R, SNoCut L R < y)
    -> (forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z)
    -> p)
   -> p.
admit.
Qed.

Theorem SNoCutP_L_0: forall L, (forall x :e L, SNo x) -> SNoCutP L 0.
admit.
Qed.

Theorem SNoCutP_0_0: SNoCutP 0 0.
admit.
Qed.

Definition SNoS_ : set -> set := fun alpha => {x :e Power (SNoElts_ alpha)|exists beta :e alpha, SNo_ beta x}.

Theorem SNoS_E : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, exists beta :e alpha, SNo_ beta x.
admit.
Qed.

Section TaggedSets2.
Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Theorem SNoS_I : forall alpha, ordinal alpha -> forall x, forall beta :e alpha, SNo_ beta x -> x :e SNoS_ alpha.
admit.
Qed.

Theorem SNoS_I2 : forall x y, SNo x -> SNo y -> SNoLev x :e SNoLev y -> x :e SNoS_ (SNoLev y).
admit.
Qed.  

Theorem SNoS_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta -> SNoS_ alpha c= SNoS_ beta.
admit.
Qed.

Theorem SNoLev_uniq2 : forall alpha, ordinal alpha -> forall x, SNo_ alpha x -> SNoLev x = alpha.
admit.
Qed.

Theorem SNoS_E2 : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha,
 forall p:prop,
     (SNoLev x :e alpha -> ordinal (SNoLev x) -> SNo x -> SNo_ (SNoLev x) x -> p)
  -> p.
admit.
Qed.

Theorem SNoS_In_neq : forall w, SNo w -> forall x :e SNoS_ (SNoLev w), x <> w.
admit.
Qed.

Theorem SNoS_SNoLev : forall z, SNo z -> z :e SNoS_ (ordsucc (SNoLev z)).
admit.
Qed.

Definition SNoL : set -> set := fun z => {x :e SNoS_ (SNoLev z) | x < z}.
Definition SNoR : set -> set := fun z => {y :e SNoS_ (SNoLev z) | z < y}.

Theorem SNoCutP_SNoL_SNoR: forall z, SNo z -> SNoCutP (SNoL z) (SNoR z).
admit.
Qed.

Theorem SNoL_E : forall x, SNo x -> forall w :e SNoL x,
  forall p:prop,
       (SNo w -> SNoLev w :e SNoLev x -> w < x -> p)
    -> p.
admit.
Qed.

Theorem SNoR_E : forall x, SNo x -> forall z :e SNoR x,
  forall p:prop,
       (SNo z -> SNoLev z :e SNoLev x -> x < z -> p)
    -> p.
admit.
Qed.

Theorem SNoL_SNoS_ : forall z, SNoL z c= SNoS_ (SNoLev z).
admit.
Qed.

Theorem SNoR_SNoS_ : forall z, SNoR z c= SNoS_ (SNoLev z).
admit.
Qed.

Theorem SNoL_SNoS : forall x, SNo x -> forall w :e SNoL x, w :e SNoS_ (SNoLev x).
admit.
Qed.

Theorem SNoR_SNoS : forall x, SNo x -> forall z :e SNoR x, z :e SNoS_ (SNoLev x).
admit.
Qed.

Theorem SNoL_I : forall z, SNo z -> forall x, SNo x -> SNoLev x :e SNoLev z -> x < z -> x :e SNoL z.
admit.
Qed.

Theorem SNoR_I : forall z, SNo z -> forall y, SNo y -> SNoLev y :e SNoLev z -> z < y -> y :e SNoR z.
admit.
Qed.

Theorem SNo_eta : forall z, SNo z -> z = SNoCut (SNoL z) (SNoR z).
admit.
Qed.

Theorem SNoCutP_SNo_SNoCut : forall L R, SNoCutP L R -> SNo (SNoCut L R).
admit.
Qed.

Theorem SNoCutP_SNoCut_L : forall L R, SNoCutP L R -> forall x :e L, x < SNoCut L R.
admit.
Qed.

Theorem SNoCutP_SNoCut_R : forall L R, SNoCutP L R -> forall y :e R, SNoCut L R < y.
admit.
Qed.

Theorem SNoCutP_SNoCut_fst : forall L R, SNoCutP L R ->
 forall z, SNo z
   -> (forall x :e L, x < z)
   -> (forall y :e R, z < y)
   -> SNoLev (SNoCut L R) c= SNoLev z
   /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z.
admit.
Qed.

Theorem SNoCut_Le : forall L1 R1 L2 R2, SNoCutP L1 R1 -> SNoCutP L2 R2
  -> (forall w :e L1, w < SNoCut L2 R2)
  -> (forall z :e R2, SNoCut L1 R1 < z)
  -> SNoCut L1 R1 <= SNoCut L2 R2.
admit.
Qed.

Theorem SNoCut_ext : forall L1 R1 L2 R2, SNoCutP L1 R1 -> SNoCutP L2 R2
  -> (forall w :e L1, w < SNoCut L2 R2)
  -> (forall z :e R1, SNoCut L2 R2 < z)
  -> (forall w :e L2, w < SNoCut L1 R1)
  -> (forall z :e R2, SNoCut L1 R1 < z)
  -> SNoCut L1 R1 = SNoCut L2 R2.
admit.
Qed.

Theorem SNoLt_SNoL_or_SNoR_impred: forall x y, SNo x -> SNo y -> x < y ->
 forall p:prop,
    (forall z :e SNoL y, z :e SNoR x -> p)
 -> (x :e SNoL y -> p)
 -> (y :e SNoR x -> p)
 -> p.
admit.
Qed.

Theorem SNoL_or_SNoR_impred: forall x y, SNo x -> SNo y ->
 forall p:prop,
    (x = y -> p)
 -> (forall z :e SNoL y, z :e SNoR x -> p)
 -> (x :e SNoL y -> p)
 -> (y :e SNoR x -> p)
 -> (forall z :e SNoR y, z :e SNoL x -> p)
 -> (x :e SNoR y -> p)
 -> (y :e SNoL x -> p)
 -> p.
admit.
Qed.

Theorem SNoL_SNoCutP_ex: forall L R, SNoCutP L R -> forall w :e SNoL (SNoCut L R), exists w' :e L, w <= w'.
admit.
Qed.

Theorem SNoR_SNoCutP_ex: forall L R, SNoCutP L R -> forall z :e SNoR (SNoCut L R), exists z' :e R, z' <= z.
admit.
Qed.

Theorem ordinal_SNo_ : forall alpha, ordinal alpha -> SNo_ alpha alpha.
admit.
Qed.

Theorem ordinal_SNo : forall alpha, ordinal alpha -> SNo alpha.
admit.
Qed.

Theorem ordinal_SNoLev : forall alpha, ordinal alpha -> SNoLev alpha = alpha.
admit.
Qed.

Theorem ordinal_SNoLev_max : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e alpha -> z < alpha.
admit.
Qed.

Theorem ordinal_SNoL : forall alpha, ordinal alpha -> SNoL alpha = SNoS_ alpha.
admit.
Qed.

Theorem ordinal_SNoR : forall alpha, ordinal alpha -> SNoR alpha = Empty.
admit.
Qed.

Theorem nat_p_SNo: forall n, nat_p n -> SNo n.
admit.
Qed.

Theorem omega_SNo: forall n :e omega, SNo n.
admit.
Qed.

Theorem omega_SNoS_omega : omega c= SNoS_ omega.
admit.
Qed.

Theorem ordinal_In_SNoLt : forall alpha, ordinal alpha -> forall beta :e alpha, beta < alpha.
admit.
Qed.

Theorem ordinal_SNoLev_max_2 : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e ordsucc alpha -> z <= alpha.
admit.
Qed.

Theorem ordinal_Subq_SNoLe : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta -> alpha <= beta.
admit.
Qed.

Theorem ordinal_SNoLt_In : forall alpha beta, ordinal alpha -> ordinal beta -> alpha < beta -> alpha :e beta.
admit.
Qed.

Theorem omega_nonneg : forall m :e omega, 0 <= m.
admit.
Qed.

Theorem SNo_0 : SNo 0.
admit.
Qed.

Theorem SNo_1 : SNo 1.
admit.
Qed.

Theorem SNo_2 : SNo 2.
admit.
Qed.

Theorem SNoLev_0 : SNoLev 0 = 0.
admit.
Qed.

Theorem SNoCut_0_0: SNoCut 0 0 = 0.
admit.
Qed.

Theorem SNoL_0 : SNoL 0 = 0.
admit.
Qed.

Theorem SNoR_0 : SNoR 0 = 0.
admit.
Qed.

Theorem SNoL_1 : SNoL 1 = 1.
admit.
Qed.

Theorem SNoR_1 : SNoR 1 = 0.
admit.
Qed.

Theorem SNo_max_SNoLev : forall x, SNo x -> (forall y :e SNoS_ (SNoLev x), y < x) -> SNoLev x = x.
admit.
Qed.

Theorem SNo_max_ordinal : forall x, SNo x -> (forall y :e SNoS_ (SNoLev x), y < x) -> ordinal x.
admit.
Qed.

Theorem pos_low_eq_one : forall x, SNo x -> 0 < x -> SNoLev x c= 1 -> x = 1.
admit.
Qed.

Definition SNo_extend0 : set -> set := fun x => PSNo (ordsucc (SNoLev x)) (fun delta => delta :e x /\ delta <> SNoLev x).
Definition SNo_extend1 : set -> set := fun x => PSNo (ordsucc (SNoLev x)) (fun delta => delta :e x \/ delta = SNoLev x).

Theorem SNo_extend0_SNo_ : forall x, SNo x -> SNo_ (ordsucc (SNoLev x)) (SNo_extend0 x).
admit.
Qed.

Theorem SNo_extend1_SNo_ : forall x, SNo x -> SNo_ (ordsucc (SNoLev x)) (SNo_extend1 x).
admit.
Qed.

Theorem SNo_extend0_SNo : forall x, SNo x -> SNo (SNo_extend0 x).
admit.
Qed.

Theorem SNo_extend1_SNo : forall x, SNo x -> SNo (SNo_extend1 x).
admit.
Qed.

Theorem SNo_extend0_SNoLev : forall x, SNo x -> SNoLev (SNo_extend0 x) = ordsucc (SNoLev x).
admit.
Qed.

Theorem SNo_extend1_SNoLev : forall x, SNo x -> SNoLev (SNo_extend1 x) = ordsucc (SNoLev x).
admit.
Qed.

Theorem SNo_extend0_nIn : forall x, SNo x -> SNoLev x /:e SNo_extend0 x.
admit.
Qed.

Theorem SNo_extend1_In : forall x, SNo x -> SNoLev x :e SNo_extend1 x.
admit.
Qed.

Theorem SNo_extend0_SNoEq : forall x, SNo x -> SNoEq_ (SNoLev x) (SNo_extend0 x) x.
admit.
Qed.

Theorem SNo_extend1_SNoEq : forall x, SNo x -> SNoEq_ (SNoLev x) (SNo_extend1 x) x.
admit.
Qed.

Theorem SNoLev_0_eq_0 : forall x, SNo x -> SNoLev x = 0 -> x = 0.
admit.
Qed.

(** eps_ n is the Surreal Number 1/2^n, without needing to define division or exponents first **)
Definition eps_ : set -> set := fun n => {0} :\/: {(ordsucc m) ' | m :e n}.

Theorem eps_ordinal_In_eq_0 : forall n alpha, ordinal alpha -> alpha :e eps_ n -> alpha = 0.
admit.
Qed.

Theorem eps_0_1 : eps_ 0 = 1.
admit.
Qed.

Theorem SNo__eps_ : forall n :e omega, SNo_ (ordsucc n) (eps_ n).
admit.
Qed.

Theorem SNo_eps_ : forall n :e omega, SNo (eps_ n).
admit.
Qed.

Theorem SNo_eps_1 : SNo (eps_ 1).
admit.
Qed.

Theorem SNoLev_eps_ : forall n :e omega, SNoLev (eps_ n) = ordsucc n.
admit.
Qed.

Theorem SNo_eps_SNoS_omega : forall n :e omega, eps_ n :e SNoS_ omega.
admit.
Qed.

Theorem SNo_eps_decr : forall n :e omega, forall m :e n, eps_ n < eps_ m.
admit.
Qed.

Theorem SNo_eps_pos : forall n :e omega, 0 < eps_ n.
admit.
Qed.

Theorem SNo_pos_eps_Lt : forall n, nat_p n -> forall x :e SNoS_ (ordsucc n), 0 < x -> eps_ n < x.
admit.
Qed.

Theorem SNo_pos_eps_Le : forall n, nat_p n -> forall x :e SNoS_ (ordsucc (ordsucc n)), 0 < x -> eps_ n <= x.
admit.
Qed.

Theorem eps_SNo_eq : forall n, nat_p n -> forall x :e SNoS_ (ordsucc n), 0 < x -> SNoEq_ (SNoLev x) (eps_ n) x -> exists m :e n, x = eps_ m.
admit.
Qed.

Theorem eps_SNoCutP : forall n :e omega, SNoCutP {0} {eps_ m|m :e n}.
admit.
Qed.

Theorem eps_SNoCut : forall n :e omega, eps_ n = SNoCut {0} {eps_ m|m :e n}.
admit.
Qed.

End TaggedSets2.

Theorem SNo_etaE : forall z, SNo z ->
  forall p:prop,
     (forall L R, SNoCutP L R
       -> (forall x :e L, SNoLev x :e SNoLev z)
       -> (forall y :e R, SNoLev y :e SNoLev z)
       -> z = SNoCut L R
       -> p)
   -> p.
admit.
Qed.

(*** surreal induction ***)
Theorem SNo_ind : forall P:set -> prop,
  (forall L R, SNoCutP L R
   -> (forall x :e L, P x)
   -> (forall y :e R, P y)
   -> P (SNoCut L R))
 -> forall z, SNo z -> P z.
admit.
Qed.

(*** surreal recursion ***)
Section SurrealRecI.
Variable F:set -> (set -> set) -> set.
Let default : set := Eps_i (fun _ => True).
Let G : set -> (set -> set -> set) -> set -> set
  := fun alpha g =>
       If_ii
          (ordinal alpha)
          (fun z:set => if z :e SNoS_ (ordsucc alpha) then
                           F z (fun w => g (SNoLev w) w)
                        else
                           default)
          (fun z:set => default).
(* Parameter SNo_rec_i "352082c509ab97c1757375f37a2ac62ed806c7b39944c98161720a584364bfaf" "be45dfaed6c479503a967f3834400c4fd18a8a567c8887787251ed89579f7be3" *)
Definition SNo_rec_i : set -> set
 := fun z => In_rec_ii G (SNoLev z) z.
Hypothesis Fr: forall z, SNo z ->
   forall g h:set -> set, (forall w :e SNoS_ (SNoLev z), g w = h w)
     -> F z g = F z h.

Theorem SNo_rec_i_eq : forall z, SNo z -> SNo_rec_i z = F z SNo_rec_i.
admit.
Qed.

End SurrealRecI.
Section SurrealRecII.
Variable F:set -> (set -> (set -> set)) -> (set -> set).
Let default : (set -> set) := Descr_ii (fun _ => True).
Let G : set -> (set -> set -> (set -> set)) -> set -> (set -> set)
  := fun alpha g =>
       If_iii
          (ordinal alpha)
          (fun z:set => If_ii (z :e SNoS_ (ordsucc alpha))
                              (F z (fun w => g (SNoLev w) w))
                              default)
          (fun z:set => default).
(* Parameter SNo_rec_ii "030b1b3db48f720b8db18b1192717cad8f204fff5fff81201b9a2414f5036417" "e148e62186e718374accb69cda703e3440725cca8832aed55c0b32731f7401ab" *)
Definition SNo_rec_ii : set -> (set -> set)
 := fun z => In_rec_iii G (SNoLev z) z.
Hypothesis Fr: forall z, SNo z ->
   forall g h:set -> (set -> set), (forall w :e SNoS_ (SNoLev z), g w = h w)
     -> F z g = F z h.

Theorem SNo_rec_ii_eq : forall z, SNo z -> SNo_rec_ii z = F z SNo_rec_ii.
admit.
Qed.

End SurrealRecII.
Section SurrealRec2.
Variable F:set -> set -> (set -> set -> set) -> set.
Let G:set -> (set -> set -> set) -> set -> (set -> set) -> set
  := fun w f z g => F w z (fun x y => if x = w then g y else f x y).
Let H:set -> (set -> set -> set) -> set -> set
  := fun w f z => if SNo z then SNo_rec_i (G w f) z else Empty.
(* Parameter SNo_rec2 "9c6267051fa817eed39b404ea37e7913b3571fe071763da2ebc1baa56b4b77f5" "7d10ab58310ebefb7f8bf63883310aa10fc2535f53bb48db513a868bc02ec028" *)
Definition SNo_rec2 : set -> set -> set
  := SNo_rec_ii H.
Hypothesis Fr: forall w, SNo w -> forall z, SNo z ->
   forall g h:set -> set -> set,
        (forall x :e SNoS_ (SNoLev w), forall y, SNo y -> g x y = h x y)
     -> (forall y :e SNoS_ (SNoLev z), g w y = h w y)
     -> F w z g = F w z h.

Theorem SNo_rec2_G_prop : forall w, SNo w -> forall f k:set -> set -> set,
    (forall x :e SNoS_ (SNoLev w), f x = k x)
 -> forall z, SNo z ->
    forall g h:set -> set, (forall u :e SNoS_ (SNoLev z), g u = h u)
 -> G w f z g = G w k z h.
admit.
Qed.

Theorem SNo_rec2_eq_1 : forall w, SNo w -> forall f:set -> set -> set,
  forall z, SNo z ->
   SNo_rec_i (G w f) z = G w f z (SNo_rec_i (G w f)).
admit.
Qed.

Theorem SNo_rec2_eq : forall w, SNo w -> forall z, SNo z ->
   SNo_rec2 w z = F w z SNo_rec2.
admit.
Qed.

End SurrealRec2.

Theorem SNo_ordinal_ind : forall P:set -> prop,
  (forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, P x)
  ->
  (forall x, SNo x -> P x).
admit.
Qed.

Theorem SNo_ordinal_ind2 : forall P:set -> set -> prop,
  (forall alpha, ordinal alpha ->
   forall beta, ordinal beta ->
   forall x :e SNoS_ alpha, forall y :e SNoS_ beta, P x y)
  ->
  (forall x y, SNo x -> SNo y -> P x y).
admit.
Qed.

Theorem SNo_ordinal_ind3 : forall P:set -> set -> set -> prop,
  (forall alpha, ordinal alpha ->
   forall beta, ordinal beta ->
   forall gamma, ordinal gamma ->
   forall x :e SNoS_ alpha, forall y :e SNoS_ beta, forall z :e SNoS_ gamma, P x y z)
  ->
  (forall x y z, SNo x -> SNo y -> SNo z -> P x y z).
admit.
Qed.

Theorem SNoLev_ind : forall P:set -> prop,
  (forall x, SNo x -> (forall w :e SNoS_ (SNoLev x), P w) -> P x)
  ->
  (forall x, SNo x -> P x).
admit.
Qed.

Theorem SNoLev_ind2 : forall P:set -> set -> prop,
  (forall x y, SNo x -> SNo y
    -> (forall w :e SNoS_ (SNoLev x), P w y)
    -> (forall z :e SNoS_ (SNoLev y), P x z)
    -> (forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), P w z)
    -> P x y)
-> forall x y, SNo x -> SNo y -> P x y.
admit.
Qed.

Theorem SNoLev_ind3 : forall P:set -> set -> set -> prop,
  (forall x y z, SNo x -> SNo y -> SNo z
    -> (forall u :e SNoS_ (SNoLev x), P u y z)
    -> (forall v :e SNoS_ (SNoLev y), P x v z)
    -> (forall w :e SNoS_ (SNoLev z), P x y w)
    -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), P u v z)
    -> (forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), P u y w)
    -> (forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), P x v w)
    -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), P u v w)
    -> P x y z)
 -> forall x y z, SNo x -> SNo y -> SNo z -> P x y z.
admit.
Qed.

Theorem SNo_omega : SNo omega.
admit.
Qed.

Theorem SNoLt_0_1 : 0 < 1.
admit.
Qed.

Theorem SNoLt_0_2 : 0 < 2.
admit.
Qed.

Theorem SNoLt_1_2 : 1 < 2.
admit.
Qed.

Theorem restr_SNo_ : forall x, SNo x -> forall alpha :e SNoLev x, SNo_ alpha (x :/\: SNoElts_ alpha).
admit.
Qed.

Theorem restr_SNo : forall x, SNo x -> forall alpha :e SNoLev x, SNo (x :/\: SNoElts_ alpha).
admit.
Qed.

Theorem restr_SNoLev : forall x, SNo x -> forall alpha :e SNoLev x, SNoLev (x :/\: SNoElts_ alpha) = alpha.
admit.
Qed.

Theorem restr_SNoEq : forall x, SNo x -> forall alpha :e SNoLev x, SNoEq_ alpha (x :/\: SNoElts_ alpha) x.
admit.
Qed.

Theorem SNo_extend0_restr_eq : forall x, SNo x -> x = SNo_extend0 x :/\: SNoElts_ (SNoLev x).
admit.
Qed.

Theorem SNo_extend1_restr_eq : forall x, SNo x -> x = SNo_extend1 x :/\: SNoElts_ (SNoLev x).
admit.
Qed.

Opaque eps_ SNo_rec2 SNo_rec_ii SNo_rec_i SNoLev SNo.

Section SurrealMinus.
(* Parameter minus_SNo "6d39c64862ac40c95c6f5e4ed5f02bb019279bfb0cda8c9bbe0e1b813b1e876c" "268a6c1da15b8fe97d37be85147bc7767b27098cdae193faac127195e8824808" *)
Definition minus_SNo : set -> set
  := SNo_rec_i (fun x m => SNoCut {m z|z :e SNoR x} {m w|w :e SNoL x}).
Prefix - 358 := minus_SNo.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Theorem minus_SNo_eq : forall x, SNo x -> - x = SNoCut {- z|z :e SNoR x} {- w|w :e SNoL x}.
admit.
Qed.

Theorem minus_SNo_prop1 : forall x, SNo x -> SNo (- x) /\ (forall u :e SNoL x, - x < - u) /\ (forall u :e SNoR x, - u < - x) /\ SNoCutP {- z|z :e SNoR x} {- w|w :e SNoL x}.
admit.
Qed.

Theorem SNo_minus_SNo : forall x, SNo x -> SNo (- x).
admit.
Qed.

Theorem minus_SNo_Lt_contra : forall x y, SNo x -> SNo y -> x < y -> - y < - x.
admit.
Qed.

Theorem minus_SNo_Le_contra : forall x y, SNo x -> SNo y -> x <= y -> - y <= - x.
admit.
Qed.

Theorem minus_SNo_SNoCutP : forall x, SNo x -> SNoCutP {- z|z :e SNoR x} {- w|w :e SNoL x}.
admit.
Qed.

Theorem minus_SNo_SNoCutP_gen : forall L R, SNoCutP L R -> SNoCutP {- z|z :e R} {- w|w :e L}.
admit.
Qed.

Theorem minus_SNo_Lev_lem1 : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, SNoLev (- x) c= SNoLev x.
admit.
Qed.

Theorem minus_SNo_Lev_lem2 : forall x, SNo x -> SNoLev (- x) c= SNoLev x.
admit.
Qed.

Theorem minus_SNo_invol : forall x, SNo x -> - - x = x.
admit.
Qed.

Theorem minus_SNo_Lev : forall x, SNo x -> SNoLev (- x) = SNoLev x.
admit.
Qed.

Theorem minus_SNo_SNo_ : forall alpha, ordinal alpha -> forall x, SNo_ alpha x -> SNo_ alpha (- x).
admit.
Qed.

Theorem minus_SNo_SNoS_ : forall alpha, ordinal alpha -> forall x, x :e SNoS_ alpha -> - x :e SNoS_ alpha.
admit.
Qed.

Theorem minus_SNoCut_eq_lem : forall v, SNo v -> forall L R, SNoCutP L R -> v = SNoCut L R -> - v = SNoCut {- z|z :e R} {- w|w :e L}.
admit.
Qed.

Theorem minus_SNoCut_eq : forall L R, SNoCutP L R -> - SNoCut L R = SNoCut {- z|z :e R} {- w|w :e L}.
admit.
Qed.

Theorem minus_SNo_Lt_contra1 : forall x y, SNo x -> SNo y -> -x < y -> - y < x.
admit.
Qed.

Theorem minus_SNo_Lt_contra2 : forall x y, SNo x -> SNo y -> x < -y -> y < - x.
admit.
Qed.

Theorem mordinal_SNoLev_min_2 : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e ordsucc alpha -> - alpha <= z.
admit.
Qed.

Theorem minus_SNo_SNoS_omega : forall x :e SNoS_ omega, - x :e SNoS_ omega.
admit.
Qed.

Theorem SNoL_minus_SNoR: forall x, SNo x -> SNoL (- x) = {- w|w :e SNoR x}.
admit.
Qed.

End SurrealMinus.
Opaque minus_SNo.
Section SurrealAdd.
Prefix - 358 := minus_SNo.
(* Parameter add_SNo "29b9b279a7a5b776b777d842e678a4acaf3b85b17a0223605e4cc68025e9b2a7" "127d043261bd13d57aaeb99e7d2c02cae2bd0698c0d689b03e69f1ac89b3c2c6" *)
Definition add_SNo : set -> set -> set
  := SNo_rec2 (fun x y a => SNoCut ({a w y|w :e SNoL x} :\/: {a x w|w :e SNoL y}) ({a z y|z :e SNoR x} :\/: {a x z|z :e SNoR y})).
Infix + 360 right := add_SNo.

Theorem add_SNo_eq : forall x, SNo x -> forall y, SNo y ->
    x + y = SNoCut ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).
admit.
Qed.

Theorem add_SNo_prop1 : forall x y, SNo x -> SNo y ->
    SNo (x + y)
 /\ (forall u :e SNoL x, u + y < x + y)
 /\ (forall u :e SNoR x, x + y < u + y)
 /\ (forall u :e SNoL y, x + u < x + y)
 /\ (forall u :e SNoR y, x + y < x + u)
 /\ SNoCutP ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).
admit.
Qed.

Theorem SNo_add_SNo : forall x y, SNo x -> SNo y -> SNo (x + y).
admit.
Qed.

Theorem SNo_add_SNo_3 : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x + y + z).
admit.
Qed.

Theorem SNo_add_SNo_3c : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x + y + - z).
admit.
Qed.

Theorem SNo_add_SNo_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> SNo (x + y + z + w).
admit.
Qed.

Theorem add_SNo_Lt1 : forall x y z, SNo x -> SNo y -> SNo z -> x < z -> x + y < z + y.
admit.
Qed.

Theorem add_SNo_Le1 : forall x y z, SNo x -> SNo y -> SNo z -> x <= z -> x + y <= z + y.
admit.
Qed.

Theorem add_SNo_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> y < z -> x + y < x + z.
admit.
Qed.

Theorem add_SNo_Le2 : forall x y z, SNo x -> SNo y -> SNo z -> y <= z -> x + y <= x + z.
admit.
Qed.

Theorem add_SNo_Lt3a : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x < z -> y <= w -> x + y < z + w.
admit.
Qed.

Theorem add_SNo_Lt3b : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x <= z -> y < w -> x + y < z + w.
admit.
Qed.

Theorem add_SNo_Lt3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x < z -> y < w -> x + y < z + w.
admit.
Qed.

Theorem add_SNo_Le3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x <= z -> y <= w -> x + y <= z + w.
admit.
Qed.

Theorem add_SNo_SNoCutP : forall x y, SNo x -> SNo y -> SNoCutP ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).
admit.
Qed.

Theorem add_SNo_com : forall x y, SNo x -> SNo y -> x + y = y + x.
admit.
Qed.

Theorem add_SNo_0L : forall x, SNo x -> 0 + x = x.
admit.
Qed.

Theorem add_SNo_0R : forall x, SNo x -> x + 0 = x.
admit.
Qed.

Theorem add_SNo_minus_SNo_linv : forall x, SNo x -> -x+x = 0.
admit.
Qed.

Theorem add_SNo_minus_SNo_rinv : forall x, SNo x -> x + -x = 0.
admit.
Qed.

Theorem add_SNo_ordinal_SNoCutP : forall alpha, ordinal alpha -> forall beta, ordinal beta -> SNoCutP ({x + beta | x :e SNoS_ alpha} :\/: {alpha + x | x :e SNoS_ beta}) Empty.
admit.
Qed.

Theorem add_SNo_ordinal_eq : forall alpha, ordinal alpha -> forall beta, ordinal beta -> alpha + beta = SNoCut ({x + beta | x :e SNoS_ alpha} :\/: {alpha + x | x :e SNoS_ beta}) Empty.
admit.
Qed.

Theorem add_SNo_ordinal_ordinal : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordinal (alpha + beta).
admit.
Qed.

Theorem add_SNo_ordinal_SL : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordsucc alpha + beta = ordsucc (alpha + beta).
admit.
Qed.

Theorem add_SNo_ordinal_SR : forall alpha, ordinal alpha -> forall beta, ordinal beta -> alpha + ordsucc beta = ordsucc (alpha + beta).
admit.
Qed.

Theorem add_SNo_ordinal_InL : forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma :e alpha, gamma + beta :e alpha + beta.
admit.
Qed.

Theorem add_SNo_ordinal_InR : forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma :e beta, alpha + gamma :e alpha + beta.
admit.
Qed.

Theorem add_nat_add_SNo : forall n m :e omega, add_nat n m = n + m.
admit.
Qed.

Theorem add_SNo_In_omega : forall n m :e omega, n + m :e omega.
admit.
Qed.

Theorem add_SNo_1_1_2 : 1 + 1 = 2.
admit.
Qed.

Theorem add_SNo_SNoL_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoL (x + y), (exists v :e SNoL x, u <= v + y) \/ (exists v :e SNoL y, u <= x + v).
admit.
Qed.

Theorem add_SNo_SNoR_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoR (x + y), (exists v :e SNoR x, v + y <= u) \/ (exists v :e SNoR y, x + v <= u).
admit.
Qed.

Theorem add_SNo_assoc : forall x y z, SNo x -> SNo y -> SNo z -> x + (y + z) = (x + y) + z.
admit.
Qed.

Theorem add_SNo_minus_R2 : forall x y, SNo x -> SNo y -> (x + y) + - y = x.
admit.
Qed.

Theorem add_SNo_minus_R2' : forall x y, SNo x -> SNo y -> (x + - y) + y = x.
admit.
Qed.

Theorem add_SNo_minus_L2 : forall x y, SNo x -> SNo y -> - x + (x + y) = y.
admit.
Qed.

Theorem add_SNo_minus_L2' : forall x y, SNo x -> SNo y -> x + (- x + y) = y.
admit.
Qed.

Theorem add_SNo_cancel_L : forall x y z, SNo x -> SNo y -> SNo z -> x + y = x + z -> y = z.
admit.
Qed.

Theorem add_SNo_cancel_R : forall x y z, SNo x -> SNo y -> SNo z -> x + y = z + y -> x = z.
admit.
Qed.

Theorem minus_SNo_0 : - 0 = 0.
admit.
Qed.

Theorem minus_add_SNo_distr : forall x y, SNo x -> SNo y -> -(x+y) = (-x) + (-y).
admit.
Qed.

Theorem minus_add_SNo_distr_3 : forall x y z, SNo x -> SNo y -> SNo z -> -(x + y + z) = -x + - y + -z.
admit.
Qed.

Theorem add_SNo_Lev_bd : forall x y, SNo x -> SNo y -> SNoLev (x + y) c= SNoLev x + SNoLev y.
admit.
Qed.

Theorem add_SNo_SNoS_omega : forall x y :e SNoS_ omega, x + y :e SNoS_ omega.
admit.
Qed.

Theorem add_SNo_Lt1_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < z + y -> x < z.
admit.
Qed.

Theorem add_SNo_Lt2_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < x + z -> y < z.
admit.
Qed.

Theorem add_SNo_Le1_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y <= z + y -> x <= z.
admit.
Qed.

Theorem add_SNo_assoc_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> x + y + z + w = (x + y + z) + w.
admit.
Qed.

Theorem add_SNo_com_3_0_1 : forall x y z, SNo x -> SNo y -> SNo z
  -> x + y + z = y + x + z.
admit.
Qed.

Theorem add_SNo_com_3b_1_2 : forall x y z, SNo x -> SNo y -> SNo z
  -> (x + y) + z = (x + z) + y.
admit.
Qed.

Theorem add_SNo_com_4_inner_mid : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> (x + y) + (z + w) = (x + z) + (y + w).
admit.
Qed.

Theorem add_SNo_rotate_3_1 : forall x y z, SNo x -> SNo y -> SNo z ->
  x + y + z = z + x + y.
admit.
Qed.

Theorem add_SNo_rotate_4_1 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w ->
  x + y + z + w = w + x + y + z.
admit.
Qed.

Theorem add_SNo_rotate_5_1 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x + y + z + w + v = v + x + y + z + w.
admit.
Qed.

Theorem add_SNo_rotate_5_2 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x + y + z + w + v = w + v + x + y + z.
admit.
Qed.

Theorem add_SNo_minus_SNo_prop2 : forall x y, SNo x -> SNo y -> x + - x + y = y.
admit.
Qed.

Theorem add_SNo_minus_SNo_prop3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + z) + (- z + w) = x + y + w.
admit.
Qed.

Theorem add_SNo_minus_SNo_prop5 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + - z) + (z + w) = x + y + w.
admit.
Qed.

Theorem add_SNo_minus_Lt1 : forall x y z, SNo x -> SNo y -> SNo z -> x + - y < z -> x < z + y.
admit.
Qed.

Theorem add_SNo_minus_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> z < x + - y -> z + y < x.
admit.
Qed.

Theorem add_SNo_minus_Lt1b : forall x y z, SNo x -> SNo y -> SNo z -> x < z + y -> x + - y < z.
admit.
Qed.

Theorem add_SNo_minus_Lt2b : forall x y z, SNo x -> SNo y -> SNo z -> z + y < x -> z < x + - y.
admit.
Qed.

Theorem add_SNo_minus_Lt1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y < w + z -> x + y + - z < w.
admit.
Qed.

Theorem add_SNo_minus_Lt2b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> w + z < x + y -> w < x + y + - z.
admit.
Qed.

Theorem add_SNo_minus_Lt_lem : forall x y z u v w, SNo x -> SNo y -> SNo z -> SNo u -> SNo v -> SNo w ->
  x + y + w < u + v + z ->
  x + y + - z < u + v + - w.
admit.
Qed.

Theorem add_SNo_minus_Le2 : forall x y z, SNo x -> SNo y -> SNo z -> z <= x + - y -> z + y <= x.
admit.
Qed.

Theorem add_SNo_minus_Le2b : forall x y z, SNo x -> SNo y -> SNo z -> z + y <= x -> z <= x + - y.
admit.
Qed.

Theorem add_SNo_Lt_subprop2 : forall x y z w u v, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
  -> x + u < z + v
  -> y + v < w + u
  -> x + y < z + w.
admit.
Qed.

Theorem add_SNo_Lt_subprop3a : forall x y z w u a, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo a
  -> x + z < w + a
  -> y + a < u
  -> x + y + z < w + u.
admit.
Qed.

Theorem add_SNo_Lt_subprop3b : forall x y w u v a, SNo x -> SNo y -> SNo w -> SNo u -> SNo v -> SNo a
  -> x + a < w + v
  -> y < a + u
  -> x + y < w + u + v.
admit.
Qed.

Theorem add_SNo_Lt_subprop3c : forall x y z w u a b c, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo a -> SNo b -> SNo c
 -> x + a < b + c
 -> y + c < u
 -> b + z < w + a
 -> x + y + z < w + u.
admit.
Qed.

Theorem add_SNo_Lt_subprop3d : forall x y w u v a b c, SNo x -> SNo y -> SNo w -> SNo u -> SNo v -> SNo a -> SNo b -> SNo c
 -> x + a < b + v
 -> y < c + u
 -> b + c < w + a
 -> x + y < w + u + v.
admit.
Qed.

Theorem ordinal_ordsucc_SNo_eq : forall alpha, ordinal alpha -> ordsucc alpha = 1 + alpha.
admit.
Qed.

Theorem add_SNo_3a_2b: forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u
 -> (x + y + z) + (w + u) = (u + y + z) + (w + x).
admit.
Qed.

Theorem add_SNo_1_ordsucc : forall n :e omega, n + 1 = ordsucc n.
admit.
Qed.

Theorem add_SNo_eps_Lt : forall x, SNo x -> forall n :e omega, x < x + eps_ n.
admit.
Qed.

Theorem add_SNo_eps_Lt' : forall x y, SNo x -> SNo y -> forall n :e omega, x < y -> x < y + eps_ n.
admit.
Qed.

Theorem SNoLt_minus_pos : forall x y, SNo x -> SNo y -> x < y -> 0 < y + - x.
admit.
Qed.

Theorem add_SNo_omega_In_cases: forall m, forall n :e omega, forall k, nat_p k -> m :e n + k -> m :e n \/ m + - n :e k.
admit.
Qed.

Theorem add_SNo_Lt4 : forall x y z w u v, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v -> x < w -> y < u -> z < v -> x + y + z < w + u + v.
admit.
Qed.

Theorem add_SNo_3_3_3_Lt1 : forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u ->
  x + y < z + w -> x + y + u < z + w + u.
admit.
Qed.

Theorem add_SNo_3_2_3_Lt1 : forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u ->
  y + x < z + w -> x + u + y < z + w + u.
admit.
Qed.

Theorem add_SNo_minus_Lt12b3: forall x y z w u v,
    SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
 -> x + y + v < w + u + z
 -> x + y + - z < w + u + - v.
admit.
Qed.

Theorem add_SNo_minus_Le1b : forall x y z, SNo x -> SNo y -> SNo z -> x <= z + y -> x + - y <= z.
admit.
Qed.

Theorem add_SNo_minus_Le1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y <= w + z -> x + y + - z <= w.
admit.
Qed.

Theorem add_SNo_minus_Le12b3: forall x y z w u v,
    SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
 -> x + y + v <= w + u + z
 -> x + y + - z <= w + u + - v.
admit.
Qed.

End SurrealAdd.

Opaque add_SNo.

Section SurrealAbs.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
(* Parameter abs_SNo "9f9389c36823b2e0124a7fe367eb786d080772b5171a5d059b10c47361cef0ef" "34f6dccfd6f62ca020248cdfbd473fcb15d8d9c5c55d1ec7c5ab6284006ff40f" *)
Definition abs_SNo : set -> set := fun x => if 0 <= x then x else - x.

Theorem nonneg_abs_SNo : forall x, 0 <= x -> abs_SNo x = x.
admit.
Qed.

Theorem not_nonneg_abs_SNo : forall x, ~(0 <= x) -> abs_SNo x = - x.
admit.
Qed.

Theorem pos_abs_SNo : forall x, 0 < x -> abs_SNo x = x.
admit.
Qed.

Theorem neg_abs_SNo : forall x, SNo x -> x < 0 -> abs_SNo x = - x.
admit.
Qed.

Theorem SNo_abs_SNo : forall x, SNo x -> SNo (abs_SNo x).
admit.
Qed.

Theorem abs_SNo_minus: forall x, SNo x -> abs_SNo (- x) = abs_SNo x.
admit.
Qed.

Theorem abs_SNo_dist_swap: forall x y, SNo x -> SNo y -> abs_SNo (x + - y) = abs_SNo (y + - x).
admit.
Qed.

End SurrealAbs.

Opaque abs_SNo.

Section SurrealMul.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
(* Parameter mul_SNo "f56bf39b8eea93d7f63da529dedb477ae1ab1255c645c47d8915623f364f2d6b" "48d05483e628cb37379dd5d279684d471d85c642fe63533c3ad520b84b18df9d" *)
Definition mul_SNo : set -> set -> set
  := SNo_rec2
      (fun x y m =>
        SNoCut ({m (w 0) y + m x (w 1) + - m (w 0) (w 1)|w :e SNoL x :*: SNoL y}
                  :\/:
                {m (z 0) y + m x (z 1) + - m (z 0) (z 1)|z :e SNoR x :*: SNoR y})
               ({m (w 0) y + m x (w 1) + - m (w 0) (w 1)|w :e SNoL x :*: SNoR y}
                  :\/:
                {m (z 0) y + m x (z 1) + - m (z 0) (z 1)|z :e SNoR x :*: SNoL y})).

Infix * 355 right := mul_SNo.

Theorem mul_SNo_eq : forall x, SNo x -> forall y, SNo y ->
   x * y
      = SNoCut ({(w 0) * y + x * (w 1) + - (w 0) * (w 1)|w :e SNoL x :*: SNoL y}
                  :\/:
                {(z 0) * y + x * (z 1) + - (z 0) * (z 1)|z :e SNoR x :*: SNoR y})
               ({(w 0) * y + x * (w 1) + - (w 0) * (w 1)|w :e SNoL x :*: SNoR y}
                  :\/:
                {(z 0) * y + x * (z 1) + - (z 0) * (z 1)|z :e SNoR x :*: SNoL y}).
admit.
Qed.

Theorem mul_SNo_eq_2 : forall x y, SNo x -> SNo y ->
  forall p:prop,
    (forall L R,
         (forall u, u :e L ->
           (forall q:prop,
                (forall w0 :e SNoL x, forall w1 :e SNoL y, u = w0 * y + x * w1 + - w0 * w1 -> q)
             -> (forall z0 :e SNoR x, forall z1 :e SNoR y, u = z0 * y + x * z1 + - z0 * z1 -> q)
             -> q))
      -> (forall w0 :e SNoL x, forall w1 :e SNoL y, w0 * y + x * w1 + - w0 * w1 :e L)
      -> (forall z0 :e SNoR x, forall z1 :e SNoR y, z0 * y + x * z1 + - z0 * z1 :e L)
      -> (forall u, u :e R ->
           (forall q:prop,
                (forall w0 :e SNoL x, forall z1 :e SNoR y, u = w0 * y + x * z1 + - w0 * z1 -> q)
             -> (forall z0 :e SNoR x, forall w1 :e SNoL y, u = z0 * y + x * w1 + - z0 * w1 -> q)
             -> q))
      -> (forall w0 :e SNoL x, forall z1 :e SNoR y, w0 * y + x * z1 + - w0 * z1 :e R)
      -> (forall z0 :e SNoR x, forall w1 :e SNoL y, z0 * y + x * w1 + - z0 * w1 :e R)
      -> x * y = SNoCut L R
      -> p)
   -> p.
admit.
Qed.

Theorem mul_SNo_prop_1 : forall x, SNo x -> forall y, SNo y ->
 forall p:prop,
    (SNo (x * y)
  -> (forall u :e SNoL x, forall v :e SNoL y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoR x, forall v :e SNoR y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoL x, forall v :e SNoR y, x * y + u * v < u * y + x * v)
  -> (forall u :e SNoR x, forall v :e SNoL y, x * y + u * v < u * y + x * v)
  -> p)
 -> p.
admit.
Qed.

Theorem SNo_mul_SNo : forall x y, SNo x -> SNo y -> SNo (x * y).
admit.
Qed.

Theorem SNo_mul_SNo_lem : forall x y u v, SNo x -> SNo y -> SNo u -> SNo v -> SNo (u * y + x * v + - (u * v)).
admit.
Qed.

Theorem SNo_mul_SNo_3 : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x * y * z).
admit.
Qed.

Theorem mul_SNo_eq_3 : forall x y, SNo x -> SNo y ->
  forall p:prop,
    (forall L R, SNoCutP L R
       -> (forall u, u :e L ->
           (forall q:prop,
                (forall w0 :e SNoL x, forall w1 :e SNoL y, u = w0 * y + x * w1 + - w0 * w1 -> q)
             -> (forall z0 :e SNoR x, forall z1 :e SNoR y, u = z0 * y + x * z1 + - z0 * z1 -> q)
             -> q))
      -> (forall w0 :e SNoL x, forall w1 :e SNoL y, w0 * y + x * w1 + - w0 * w1 :e L)
      -> (forall z0 :e SNoR x, forall z1 :e SNoR y, z0 * y + x * z1 + - z0 * z1 :e L)
      -> (forall u, u :e R ->
           (forall q:prop,
                (forall w0 :e SNoL x, forall z1 :e SNoR y, u = w0 * y + x * z1 + - w0 * z1 -> q)
             -> (forall z0 :e SNoR x, forall w1 :e SNoL y, u = z0 * y + x * w1 + - z0 * w1 -> q)
             -> q))
      -> (forall w0 :e SNoL x, forall z1 :e SNoR y, w0 * y + x * z1 + - w0 * z1 :e R)
      -> (forall z0 :e SNoR x, forall w1 :e SNoL y, z0 * y + x * w1 + - z0 * w1 :e R)
      -> x * y = SNoCut L R
      -> p)
   -> p.
admit.
Qed.

Theorem mul_SNo_Lt : forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u < x -> v < y -> u * y + x * v < x * y + u * v.
admit.
Qed.

Theorem mul_SNo_Le : forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u <= x -> v <= y -> u * y + x * v <= x * y + u * v.
admit.
Qed.

Theorem mul_SNo_SNoL_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoL (x * y),
 (exists v :e SNoL x, exists w :e SNoL y, u + v * w <= v * y + x * w)
 \/
 (exists v :e SNoR x, exists w :e SNoR y, u + v * w <= v * y + x * w).
admit.
Qed.

Theorem mul_SNo_SNoL_interpolate_impred : forall x y, SNo x -> SNo y -> forall u :e SNoL (x * y),
 forall p:prop,
      (forall v :e SNoL x, forall w :e SNoL y, u + v * w <= v * y + x * w -> p)
   -> (forall v :e SNoR x, forall w :e SNoR y, u + v * w <= v * y + x * w -> p)
   -> p.
admit.
Qed.  

Theorem mul_SNo_SNoR_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoR (x * y),
 (exists v :e SNoL x, exists w :e SNoR y, v * y + x * w <= u + v * w)
 \/
 (exists v :e SNoR x, exists w :e SNoL y, v * y + x * w <= u + v * w).
admit.
Qed.

Theorem mul_SNo_SNoR_interpolate_impred : forall x y, SNo x -> SNo y -> forall u :e SNoR (x * y),
 forall p:prop,
     (forall v :e SNoL x, forall w :e SNoR y, v * y + x * w <= u + v * w -> p)
  -> (forall v :e SNoR x, forall w :e SNoL y, v * y + x * w <= u + v * w -> p)
  -> p.
admit.
Qed.

(** This could be useful for proving L c= L', L = L', R c= R' or R = R'
    when corresponding conditions hold. **)
Theorem mul_SNo_Subq_lem : forall x y X Y Z W,
  forall U U',
      (forall u, u :e U ->
         (forall q:prop,
                (forall w0 :e X, forall w1 :e Y, u = w0 * y + x * w1 + - w0 * w1 -> q)
             -> (forall z0 :e Z, forall z1 :e W, u = z0 * y + x * z1 + - z0 * z1 -> q)
             -> q))
   -> (forall w0 :e X, forall w1 :e Y, w0 * y + x * w1 + - w0 * w1 :e U')
   -> (forall w0 :e Z, forall w1 :e W, w0 * y + x * w1 + - w0 * w1 :e U')
   -> U c= U'.
admit.
Qed.

(** Part of Conway Chapter 2 Theorem 7 **)
Theorem mul_SNo_zeroR : forall x, SNo x -> x * 0 = 0.
admit.
Qed.

Theorem mul_SNo_oneR : forall x, SNo x -> x * 1 = x.
admit.
Qed.

Theorem mul_SNo_com : forall x y, SNo x -> SNo y -> x * y = y * x.
admit.
Qed.

Theorem mul_SNo_minus_distrL : forall x y, SNo x -> SNo y -> (- x) * y = - x * y.
admit.
Qed.

Theorem mul_SNo_minus_distrR: forall x y, SNo x -> SNo y -> x * (- y) = - (x * y).
admit.
Qed.

Theorem mul_SNo_distrR : forall x y z, SNo x -> SNo y -> SNo z
  -> (x + y) * z = x * z + y * z.
admit.
Qed.

Theorem mul_SNo_distrL : forall x y z, SNo x -> SNo y -> SNo z
  -> x * (y + z) = x * y + x * z.
admit.
Qed.

Section mul_SNo_assoc_lems.
Variable M:set -> set -> set.
Infix * 355 right := M.
Hypothesis SNo_M : forall x y, SNo x -> SNo y -> SNo (x * y).
Hypothesis DL: forall x y z, SNo x -> SNo y -> SNo z -> x * (y + z) = x * y + x * z.
Hypothesis DR: forall x y z, SNo x -> SNo y -> SNo z -> (x + y) * z = x * z + y * z.
Hypothesis IL: forall x y, SNo x -> SNo y -> forall u :e SNoL (x * y),
 forall p:prop,
      (forall v :e SNoL x, forall w :e SNoL y, u + v * w <= v * y + x * w -> p)
   -> (forall v :e SNoR x, forall w :e SNoR y, u + v * w <= v * y + x * w -> p)
   -> p.
Hypothesis IR: forall x y, SNo x -> SNo y -> forall u :e SNoR (x * y),
 forall p:prop,
     (forall v :e SNoL x, forall w :e SNoR y, v * y + x * w <= u + v * w -> p)
  -> (forall v :e SNoR x, forall w :e SNoL y, v * y + x * w <= u + v * w -> p)
  -> p.
Hypothesis M_Lt: forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u < x -> v < y -> u * y + x * v < x * y + u * v.
Hypothesis M_Le: forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u <= x -> v <= y -> u * y + x * v <= x * y + u * v.

Theorem mul_SNo_assoc_lem1 : forall x y z, SNo x -> SNo y -> SNo z
 -> (forall u :e SNoS_ (SNoLev x), u * (y * z) = (u * y) * z)
 -> (forall v :e SNoS_ (SNoLev y), x * (v * z) = (x * v) * z)
 -> (forall w :e SNoS_ (SNoLev z), x * (y * w) = (x * y) * w)
 -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), u * (v * z) = (u * v) * z)
 -> (forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), u * (y * w) = (u * y) * w)
 -> (forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), x * (v * w) = (x * v) * w)
 -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), u * (v * w) = (u * v) * w)
 -> forall L,
    (forall u :e L,
     forall q:prop,
         (forall v :e SNoL x, forall w :e SNoL (y * z), u = v * (y * z) + x * w + - v * w -> q)
      -> (forall v :e SNoR x, forall w :e SNoR (y * z), u = v * (y * z) + x * w + - v * w -> q)
      -> q)
 -> forall u :e L, u < (x * y) * z.
admit.
Qed.

Theorem mul_SNo_assoc_lem2 : forall x y z, SNo x -> SNo y -> SNo z
 -> (forall u :e SNoS_ (SNoLev x), u * (y * z) = (u * y) * z)
 -> (forall v :e SNoS_ (SNoLev y), x * (v * z) = (x * v) * z)
 -> (forall w :e SNoS_ (SNoLev z), x * (y * w) = (x * y) * w)
 -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), u * (v * z) = (u * v) * z)
 -> (forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), u * (y * w) = (u * y) * w)
 -> (forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), x * (v * w) = (x * v) * w)
 -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), u * (v * w) = (u * v) * w)
 -> forall R,
    (forall u :e R,
     forall q:prop,
         (forall v :e SNoL x, forall w :e SNoR (y * z), u = v * (y * z) + x * w + - v * w -> q)
      -> (forall v :e SNoR x, forall w :e SNoL (y * z), u = v * (y * z) + x * w + - v * w -> q)
      -> q)
 -> forall u :e R, (x * y) * z < u.
admit.
Qed.

End mul_SNo_assoc_lems.

Theorem mul_SNo_assoc : forall x y z, SNo x -> SNo y -> SNo z
  -> x * (y * z) = (x * y) * z.
admit.
Qed.

Theorem mul_nat_mul_SNo : forall n m :e omega, mul_nat n m = n * m.
admit.
Qed.

Theorem mul_SNo_In_omega : forall n m :e omega, n * m :e omega.
admit.
Qed.

Theorem mul_SNo_zeroL : forall x, SNo x -> 0 * x = 0.
admit.
Qed.

Theorem mul_SNo_oneL : forall x, SNo x -> 1 * x = x.
admit.
Qed.

Theorem mul_SNo_rotate_3_1 : forall x y z, SNo x -> SNo y -> SNo z ->
  x * y * z = z * x * y.
admit.
Qed.

Theorem pos_mul_SNo_Lt : forall x y z, SNo x -> 0 < x -> SNo y -> SNo z -> y < z -> x * y < x * z.
admit.
Qed.

Theorem nonneg_mul_SNo_Le : forall x y z, SNo x -> 0 <= x -> SNo y -> SNo z -> y <= z -> x * y <= x * z.
admit.
Qed.

Theorem neg_mul_SNo_Lt : forall x y z, SNo x -> x < 0 -> SNo y -> SNo z -> z < y -> x * y < x * z.
admit.
Qed.

Theorem pos_mul_SNo_Lt' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < z -> x < y -> x * z < y * z.
admit.
Qed.

Theorem mul_SNo_Lt1_pos_Lt : forall x y, SNo x -> SNo y -> x < 1 -> 0 < y -> x * y < y.
admit.
Qed.

Theorem nonneg_mul_SNo_Le' : forall x y z, SNo x -> SNo y -> SNo z -> 0 <= z -> x <= y -> x * z <= y * z.
admit.
Qed.

Theorem mul_SNo_Le1_nonneg_Le : forall x y, SNo x -> SNo y -> x <= 1 -> 0 <= y -> x * y <= y.
admit.
Qed.

Theorem pos_mul_SNo_Lt2 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> 0 < x -> 0 < y -> x < z -> y < w -> x * y < z * w.
admit.
Qed.

Theorem nonneg_mul_SNo_Le2 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> 0 <= x -> 0 <= y -> x <= z -> y <= w -> x * y <= z * w.
admit.
Qed.

Theorem mul_SNo_pos_pos: forall x y, SNo x -> SNo y -> 0 < x -> 0 < y -> 0 < x * y.
admit.
Qed.

Theorem mul_SNo_pos_neg: forall x y, SNo x -> SNo y -> 0 < x -> y < 0 -> x * y < 0.
admit.
Qed.

Theorem mul_SNo_neg_pos: forall x y, SNo x -> SNo y -> x < 0 -> 0 < y -> x * y < 0.
admit.
Qed.

Theorem mul_SNo_neg_neg: forall x y, SNo x -> SNo y -> x < 0 -> y < 0 -> 0 < x * y.
admit.
Qed.

Theorem mul_SNo_nonneg_nonneg: forall x y, SNo x -> SNo y -> 0 <= x -> 0 <= y -> 0 <= x * y.
admit.
Qed.

Theorem mul_SNo_nonpos_pos: forall x y, SNo x -> SNo y -> x <= 0 -> 0 < y -> x * y <= 0.
admit.
Qed.

Theorem mul_SNo_nonpos_neg: forall x y, SNo x -> SNo y -> x <= 0 -> y < 0 -> 0 <= x * y.
admit.
Qed.

Theorem nonpos_mul_SNo_Le : forall x y z, SNo x -> x <= 0 -> SNo y -> SNo z -> z <= y -> x * y <= x * z.
admit.
Qed.

Theorem SNo_zero_or_sqr_pos : forall x, SNo x -> x = 0 \/ 0 < x * x.
admit.
Qed.

Theorem SNo_pos_sqr_uniq: forall x y, SNo x -> SNo y -> 0 < x -> 0 < y -> x * x = y * y -> x = y.
admit.
Qed.

Theorem SNo_nonneg_sqr_uniq: forall x y, SNo x -> SNo y -> 0 <= x -> 0 <= y -> x * x = y * y -> x = y.
admit.
Qed.

Theorem SNo_foil: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y) * (z + w) = x * z + x * w + y * z + y * w.
admit.
Qed.

Theorem mul_SNo_minus_minus: forall x y, SNo x -> SNo y -> (- x) * (- y) = x * y.
admit.
Qed.

Theorem mul_SNo_com_3_0_1 : forall x y z, SNo x -> SNo y -> SNo z
  -> x * y * z = y * x * z.
admit.
Qed.

Theorem mul_SNo_com_3b_1_2 : forall x y z, SNo x -> SNo y -> SNo z
  -> (x * y) * z = (x * z) * y.
admit.
Qed.

Theorem mul_SNo_com_4_inner_mid : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> (x * y) * (z * w) = (x * z) * (y * w).
admit.
Qed.

Theorem SNo_foil_mm: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + - y) * (z + - w) = x * z + - x * w + - y * z + y * w.
admit.
Qed.

Theorem mul_SNo_nonzero_cancel: forall x y z, SNo x -> x <> 0 -> SNo y -> SNo z -> x * y = x * z -> y = z.
admit.
Qed.

Theorem mul_SNoCutP_lem : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> SNoCutP ({w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ly}
              :\/:
             {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ry})
            ({w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ry}
              :\/:
             {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ly})
 /\ x * y
  = SNoCut ({w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ly}
             :\/:
            {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ry})
           ({w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ry}
             :\/:
            {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ly})
 /\ forall q:prop,
     (forall LxLy' RxRy' LxRy' RxLy',
         (forall u :e LxLy', forall p:prop, (forall w :e Lx, forall w' :e Ly, SNo w -> SNo w' -> w < x -> w' < y -> u = w * y + x * w' + - w * w' -> p) -> p)
      -> (forall w :e Lx, forall w' :e Ly, w * y + x * w' + - w * w' :e LxLy')
      -> (forall u :e RxRy', forall p:prop, (forall z :e Rx, forall z' :e Ry, SNo z -> SNo z' -> x < z -> y < z' -> u = z * y + x * z' + - z * z' -> p) -> p)
      -> (forall z :e Rx, forall z' :e Ry, z * y + x * z' + - z * z' :e RxRy')
      -> (forall u :e LxRy', forall p:prop, (forall w :e Lx, forall z :e Ry, SNo w -> SNo z -> w < x -> y < z -> u = w * y + x * z + - w * z -> p) -> p)
      -> (forall w :e Lx, forall z :e Ry, w * y + x * z + - w * z :e LxRy')
      -> (forall u :e RxLy', forall p:prop, (forall z :e Rx, forall w :e Ly, SNo z -> SNo w -> x < z -> w < y -> u = z * y + x * w + - z * w -> p) -> p)
      -> (forall z :e Rx, forall w :e Ly, z * y + x * w + - z * w :e RxLy')
      -> SNoCutP (LxLy' :\/: RxRy') (LxRy' :\/: RxLy')
      -> x * y = SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy')
      -> q)
    -> q.
admit.
Qed.

Theorem mul_SNoCut_abs : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> forall q:prop,
     (forall LxLy' RxRy' LxRy' RxLy',
         (forall u :e LxLy', forall p:prop, (forall w :e Lx, forall w' :e Ly, SNo w -> SNo w' -> w < x -> w' < y -> u = w * y + x * w' + - w * w' -> p) -> p)
      -> (forall w :e Lx, forall w' :e Ly, w * y + x * w' + - w * w' :e LxLy')
      -> (forall u :e RxRy', forall p:prop, (forall z :e Rx, forall z' :e Ry, SNo z -> SNo z' -> x < z -> y < z' -> u = z * y + x * z' + - z * z' -> p) -> p)
      -> (forall z :e Rx, forall z' :e Ry, z * y + x * z' + - z * z' :e RxRy')
      -> (forall u :e LxRy', forall p:prop, (forall w :e Lx, forall z :e Ry, SNo w -> SNo z -> w < x -> y < z -> u = w * y + x * z + - w * z -> p) -> p)
      -> (forall w :e Lx, forall z :e Ry, w * y + x * z + - w * z :e LxRy')
      -> (forall u :e RxLy', forall p:prop, (forall z :e Rx, forall w :e Ly, SNo z -> SNo w -> x < z -> w < y -> u = z * y + x * w + - z * w -> p) -> p)
      -> (forall z :e Rx, forall w :e Ly, z * y + x * w + - z * w :e RxLy')
      -> SNoCutP (LxLy' :\/: RxRy') (LxRy' :\/: RxLy')
      -> x * y = SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy')
      -> q)
    -> q.
admit.
Qed.

Theorem mul_SNo_SNoCut_SNoL_interpolate : forall Lx Rx Ly Ry,
    SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> forall x y, x = SNoCut Lx Rx -> y = SNoCut Ly Ry
 -> forall u :e SNoL (x * y),
 (exists v :e Lx, exists w :e Ly, u + v * w <= v * y + x * w)
 \/
 (exists v :e Rx, exists w :e Ry, u + v * w <= v * y + x * w).
admit.
Qed.

Theorem mul_SNo_SNoCut_SNoL_interpolate_impred : forall Lx Rx Ly Ry,
    SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> forall x y, x = SNoCut Lx Rx -> y = SNoCut Ly Ry
 -> forall u :e SNoL (x * y),
    forall p:prop,
        (forall v :e Lx, forall w :e Ly, u + v * w <= v * y + x * w -> p)
     -> (forall v :e Rx, forall w :e Ry, u + v * w <= v * y + x * w -> p)
     -> p.
admit.
Qed.

Theorem mul_SNo_SNoCut_SNoR_interpolate : forall Lx Rx Ly Ry,
    SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> forall x y, x = SNoCut Lx Rx -> y = SNoCut Ly Ry
 -> forall u :e SNoR (x * y),
 (exists v :e Lx, exists w :e Ry, v * y + x * w <= u + v * w)
 \/
 (exists v :e Rx, exists w :e Ly, v * y + x * w <= u + v * w).
admit.
Qed.

Theorem mul_SNo_SNoCut_SNoR_interpolate_impred : forall Lx Rx Ly Ry,
    SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> forall x y, x = SNoCut Lx Rx -> y = SNoCut Ly Ry
 -> forall u :e SNoR (x * y),
    forall p:prop,
        (forall v :e Lx, forall w :e Ry, v * y + x * w <= u + v * w -> p)
     -> (forall v :e Rx, forall w :e Ly, v * y + x * w <= u + v * w -> p)
     -> p.
admit.
Qed.

Theorem nonpos_nonneg_0 : forall m n :e omega, m = - n -> m = 0 /\ n = 0.
admit.
Qed.

Theorem mul_minus_SNo_distrR: forall x y, SNo x -> SNo y -> x * (- y) = - (x * y).
admit.
Qed.

End SurrealMul.

Opaque mul_SNo.

Section Int.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

Definition int : set := omega :\/: {- n|n :e omega}.

Theorem int_SNo_cases : forall p:set -> prop,
    (forall n :e omega, p n)
 -> (forall n :e omega, p (- n))
 -> forall x :e int, p x.
admit.
Qed.

Theorem int_3_cases: forall n :e int, forall p:prop,
    (forall m :e omega, n = - ordsucc m -> p)
 -> (n = 0 -> p)
 -> (forall m :e omega, n = ordsucc m -> p)
 -> p.
admit.
Qed.

Theorem int_SNo : forall x :e int, SNo x.
admit.
Qed.

Theorem Subq_omega_int : omega c= int.
admit.
Qed.

Theorem int_minus_SNo_omega : forall n :e omega, - n :e int.
admit.
Qed.

Theorem int_add_SNo_lem: forall n :e omega, forall m, nat_p m -> - n + m :e int.
admit.
Qed.

Theorem int_add_SNo: forall x y :e int, x + y :e int.
admit.
Qed.

Theorem int_minus_SNo: forall x :e int, - x :e int.
admit.
Qed.

Theorem int_mul_SNo: forall x y :e int, x * y :e int.
admit.
Qed.

Theorem nonneg_int_nat_p: forall n :e int, 0 <= n -> nat_p n.
admit.
Qed.

End Int.

Section BezoutAndGCD.

Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.

Theorem quotient_remainder_nat: forall n :e omega :\: {0}, forall m, nat_p m -> exists q :e omega, exists r :e n, m = q * n + r.
admit.
Qed.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix < 490 := SNoLt.
Infix <= 490 := SNoLe.

Theorem mul_SNo_nonpos_nonneg: forall x y, SNo x -> SNo y -> x <= 0 -> 0 <= y -> x * y <= 0.
admit.
Qed.

Theorem ordinal_0_In_ordsucc: forall alpha, ordinal alpha -> 0 :e ordsucc alpha.
admit.
Qed.

Theorem ordinal_ordsucc_pos: forall alpha, ordinal alpha -> 0 < ordsucc alpha.
admit.
Qed.

Theorem quotient_remainder_int: forall n :e omega :\: {0}, forall m :e int, exists q :e int, exists r :e n, m = q * n + r.
admit.
Qed.

Definition divides_int : set -> set -> prop := fun m n => m :e int /\ n :e int /\ exists k :e int, m * k = n.

Theorem divides_int_ref: forall n :e int, divides_int n n.
admit.
Qed.

Theorem divides_int_0: forall n :e int, divides_int n 0.
admit.
Qed.

Theorem divides_int_add_SNo: forall m n k, divides_int m n -> divides_int m k -> divides_int m (n + k).
admit.
Qed.

Theorem divides_int_mul_SNo: forall m n m' n', divides_int m m' -> divides_int n n' -> divides_int (m * n) (m' * n').
admit.
Qed.

Theorem divides_nat_divides_int: forall m n, divides_nat m n -> divides_int m n.
admit.
Qed.

Theorem divides_int_divides_nat: forall m n :e omega, divides_int m n -> divides_nat m n.
admit.
Qed.

Theorem divides_int_minus_SNo: forall m n, divides_int m n -> divides_int m (- n).
admit.
Qed.

Theorem divides_int_mul_SNo_L: forall m n, forall k :e int, divides_int m n -> divides_int m (n * k).
admit.
Qed.

Theorem divides_int_mul_SNo_R: forall m n, forall k :e int, divides_int m n -> divides_int m (k * n).
admit.
Qed.

Theorem divides_int_1: forall n :e int, divides_int 1 n.
admit.
Qed.

Theorem divides_int_pos_Le: forall m n, divides_int m n -> 0 < n -> m <= n.
admit.
Qed.

Definition gcd_reln : set -> set -> set -> prop := fun m n d => divides_int d m /\ divides_int d n /\ forall d', divides_int d' m -> divides_int d' n -> d' <= d.

Theorem gcd_reln_uniq: forall a b c d, gcd_reln a b c -> gcd_reln a b d -> c = d.
admit.
Qed.

Definition int_lin_comb : set -> set -> set -> prop := fun a b c => a :e int /\ b :e int /\ c :e int /\ exists m n :e int, m * a + n * b = c.

Theorem int_lin_comb_I: forall a b c :e int, (exists m n :e int, m * a + n * b = c) -> int_lin_comb a b c.
admit.
Qed.

Theorem int_lin_comb_E: forall a b c, int_lin_comb a b c ->
  forall p:prop,
       (a :e int -> b :e int -> c :e int -> forall m n :e int, m * a + n * b = c -> p)
    -> p.
admit.
Qed.

Theorem int_lin_comb_E1: forall a b c, int_lin_comb a b c -> a :e int.
admit.
Qed.

Theorem int_lin_comb_E2: forall a b c, int_lin_comb a b c -> b :e int.
admit.
Qed.

Theorem int_lin_comb_E3: forall a b c, int_lin_comb a b c -> c :e int.
admit.
Qed.

Theorem int_lin_comb_E4: forall a b c, int_lin_comb a b c ->
  forall p:prop,
       (forall m n :e int, m * a + n * b = c -> p)
    -> p.
admit.
Qed.

Theorem least_pos_int_lin_comb_ex: forall a b :e int, ~(a = 0 /\ b = 0) -> exists c, int_lin_comb a b c /\ 0 < c /\ forall c', int_lin_comb a b c' -> 0 < c' -> c <= c'.
admit.
Qed.

Theorem int_lin_comb_sym: forall a b d,
     int_lin_comb a b d
  -> int_lin_comb b a d.
admit.
Qed.
  
Theorem least_pos_int_lin_comb_divides_int: forall a b d,
     int_lin_comb a b d
  -> 0 < d
  -> (forall c, int_lin_comb a b c -> 0 < c -> d <= c)
  -> divides_int d a.
admit.
Qed.

Theorem least_pos_int_lin_comb_gcd: forall a b d,
     int_lin_comb a b d
  -> 0 < d
  -> (forall c, int_lin_comb a b c -> 0 < c -> d <= c)
  -> gcd_reln a b d.
admit.
Qed.

Theorem BezoutThm: forall a b :e int, ~(a = 0 /\ b = 0) ->
  forall d, gcd_reln a b d <-> int_lin_comb a b d /\ 0 < d /\ forall d', int_lin_comb a b d' -> 0 < d' -> d <= d'.
admit.
Qed.

Theorem gcd_id: forall m :e omega :\: {0}, gcd_reln m m m.
admit.
Qed.

Theorem gcd_0: forall m :e omega :\: {0}, gcd_reln 0 m m.
admit.
Qed.

Theorem gcd_sym: forall m n d, gcd_reln m n d -> gcd_reln n m d.
admit.
Qed.

Theorem gcd_minus: forall m n d, gcd_reln m n d -> gcd_reln m (- n) d.
admit.
Qed.

Theorem euclidean_algorithm_prop_1: forall m n d, n :e int -> gcd_reln m (n + - m) d -> gcd_reln m n d.
admit.
Qed.

Theorem euclidean_algorithm:
     (forall m :e omega :\: {0}, gcd_reln m m m)
  /\ (forall m :e omega :\: {0}, gcd_reln 0 m m)
  /\ (forall m :e omega :\: {0}, gcd_reln m 0 m)
  /\ (forall m n :e omega, m < n
          -> forall d, gcd_reln m (n + - m) d
                    -> gcd_reln m n d)
  /\ (forall m n :e omega, n < m
          -> forall d, gcd_reln n m d
                    -> gcd_reln m n d)
  /\ (forall m :e omega, forall n :e int, n < 0
          -> forall d, gcd_reln m (- n) d
                    -> gcd_reln m n d)
  /\ (forall m n :e int, m < 0
          -> forall d, gcd_reln (- m) n d
                    -> gcd_reln m n d).
admit.
Qed.

Theorem Euclid_lemma: forall p, prime_nat p -> forall a b :e int, divides_int p (a * b) -> divides_int p a \/ divides_int p b.
admit.
Qed.

End BezoutAndGCD.

Section PrimeFactorization.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix < 490 := SNoLt.
Infix <= 490 := SNoLe.

Theorem prime_not_divides_int_1: forall p, prime_nat p -> ~divides_int p 1.
admit.
Qed.

Definition Pi_SNo : (set -> set) -> set -> set := fun f n =>
  nat_primrec 1 (fun i r => r * f i) n.

Theorem Pi_SNo_0: forall f:set -> set, Pi_SNo f 0 = 1.
admit.
Qed.

Theorem Pi_SNo_S: forall f:set -> set, forall n, nat_p n -> Pi_SNo f (ordsucc n) = Pi_SNo f n * f n.
admit.
Qed.

Theorem Pi_SNo_In_omega: forall f:set -> set,
 forall n, nat_p n ->
     (forall i :e n, f i :e omega)
  -> Pi_SNo f n :e omega.
admit.
Qed.

Theorem Pi_SNo_In_int: forall f:set -> set,
 forall n, nat_p n ->
     (forall i :e n, f i :e int)
  -> Pi_SNo f n :e int.
admit.
Qed.

Theorem divides_int_prime_nat_eq: forall p q, prime_nat p -> prime_nat q -> divides_int p q -> p = q.
admit.
Qed.

Theorem Euclid_lemma_Pi_SNo: forall f:set->set,
  forall p, prime_nat p ->
  forall n, nat_p n ->
      (forall i :e n, f i :e int)
   -> divides_int p (Pi_SNo f n)
   -> exists i :e n, divides_int p (f i).
admit.
Qed.

Theorem divides_nat_mul_SNo_R: forall m n :e omega, divides_nat m (m * n).
admit.
Qed.

Theorem divides_nat_mul_SNo_L: forall m n :e omega, divides_nat n (m * n).
admit.
Qed.

Theorem Pi_SNo_divides: forall f:set->set,
  forall n, nat_p n ->
      (forall i :e n, f i :e omega)
   -> (forall i :e n, divides_nat (f i) (Pi_SNo f n)).
admit.
Qed.

Definition nonincrfinseq : (set -> prop) -> set -> (set -> set) -> prop := fun A n f => forall i :e n, A (f i) /\ forall j :e i, f i <= f j.

Theorem Pi_SNo_eq: forall f g:set->set,
  forall m, nat_p m
   -> (forall i :e m, f i = g i)
   -> Pi_SNo f m = Pi_SNo g m.
admit.
Qed.

Theorem prime_factorization_ex_uniq: forall n, nat_p n -> 0 :e n ->
  exists k :e omega, exists f:set -> set, nonincrfinseq prime_nat k f /\ Pi_SNo f k = n
    /\ forall k' :e omega, forall f':set -> set, nonincrfinseq prime_nat k' f' -> Pi_SNo f' k' = n
         -> k' = k /\ forall i :e k, f' i = f i.
admit.
Qed.

End PrimeFactorization.

Section SurrealExp.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Definition exp_SNo_nat : set->set->set := fun n m:set => nat_primrec 1 (fun _ r => n * r) m.
Infix ^ 342 right := exp_SNo_nat.

Theorem exp_SNo_nat_0 : forall x, SNo x -> x ^ 0 = 1.
admit.
Qed.

Theorem exp_SNo_nat_S : forall x, SNo x -> forall n, nat_p n -> x ^ (ordsucc n) = x * x ^ n.
admit.
Qed.

Theorem exp_SNo_nat_1: forall x, SNo x -> x ^ 1 = x.
admit.
Qed.

Theorem SNo_exp_SNo_nat : forall x, SNo x -> forall n, nat_p n -> SNo (x ^ n).
admit.
Qed.

Theorem nat_exp_SNo_nat : forall x, nat_p x -> forall n, nat_p n -> nat_p (x ^ n).
admit.
Qed.

Theorem eps_ordsucc_half_add : forall n, nat_p n -> eps_ (ordsucc n) + eps_ (ordsucc n) = eps_ n.
admit.
Qed.

Theorem eps_1_half_eq1 : eps_ 1 + eps_ 1 = 1.
admit.
Qed.

Theorem eps_1_half_eq2 : 2 * eps_ 1 = 1.
admit.
Qed.

Theorem double_eps_1 : forall x y z, SNo x -> SNo y -> SNo z -> x + x = y + z -> x = eps_ 1 * (y + z).
admit.
Qed.

Theorem exp_SNo_1_bd: forall x, SNo x -> 1 <= x -> forall n, nat_p n -> 1 <= x ^ n.
admit.
Qed.

Theorem exp_SNo_2_bd: forall n, nat_p n -> n < 2 ^ n.
admit.
Qed.

Theorem mul_SNo_eps_power_2: forall n, nat_p n -> eps_ n * 2 ^ n = 1.
admit.
Qed.

Theorem eps_bd_1 : forall n :e omega, eps_ n <= 1.
admit.
Qed.

Theorem mul_SNo_eps_power_2': forall n, nat_p n -> 2 ^ n * eps_ n = 1.
admit.
Qed.

Theorem exp_SNo_nat_mul_add : forall x, SNo x -> forall m, nat_p m -> forall n, nat_p n -> x ^ m * x ^ n = x ^ (m + n).
admit.
Qed.

Theorem exp_SNo_nat_mul_add' : forall x, SNo x -> forall m n :e omega, x ^ m * x ^ n = x ^ (m + n).
admit.
Qed.

Theorem exp_SNo_nat_pos : forall x, SNo x -> 0 < x -> forall n, nat_p n -> 0 < x ^ n.
admit.
Qed.

Theorem mul_SNo_eps_eps_add_SNo: forall m n :e omega, eps_ m * eps_ n = eps_ (m + n).
admit.
Qed.

Theorem SNoS_omega_Lev_equip : forall n, nat_p n -> equip {x :e SNoS_ omega|SNoLev x = n} (2 ^ n).
admit.
Qed.

Theorem SNoS_finite : forall n :e omega, finite (SNoS_ n).
admit.
Qed.

Theorem SNoS_omega_SNoL_finite : forall x :e SNoS_ omega, finite (SNoL x).
admit.
Qed.

Theorem SNoS_omega_SNoR_finite : forall x :e SNoS_ omega, finite (SNoR x).
admit.
Qed.

End SurrealExp.

Opaque exp_SNo_nat.

Section SNoMaxMin.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.
Definition SNo_max_of : set -> set -> prop := fun X x => x :e X /\ SNo x /\ forall y :e X, SNo y -> y <= x.
Definition SNo_min_of : set -> set -> prop := fun X x => x :e X /\ SNo x /\ forall y :e X, SNo y -> x <= y.

Theorem minus_SNo_max_min : forall X y, (forall x :e X, SNo x) -> SNo_max_of X y -> SNo_min_of {- x|x :e X} (- y).
admit.
Qed.

Theorem minus_SNo_max_min' : forall X y, (forall x :e X, SNo x) -> SNo_max_of {- x|x :e X} y -> SNo_min_of X (- y).
admit.
Qed.

Theorem minus_SNo_min_max : forall X y, (forall x :e X, SNo x) -> SNo_min_of X y -> SNo_max_of {- x|x :e X} (- y).
admit.
Qed.

Theorem double_SNo_max_1 : forall x y, SNo x -> SNo_max_of (SNoL x) y -> forall z, SNo z -> x < z -> y + z < x + x -> exists w :e SNoR z, y + w = x + x.
admit.
Qed.

Theorem double_SNo_min_1 : forall x y, SNo x -> SNo_min_of (SNoR x) y -> forall z, SNo z -> z < x -> x + x < y + z -> exists w :e SNoL z, y + w = x + x.
admit.
Qed.

Theorem finite_max_exists : forall X, (forall x :e X, SNo x) -> finite X -> X <> 0 -> exists x, SNo_max_of X x.
admit.
Qed.

Theorem finite_min_exists : forall X, (forall x :e X, SNo x) -> finite X -> X <> 0 -> exists x, SNo_min_of X x.
admit.
Qed.

Theorem SNoS_omega_SNoL_max_exists : forall x :e SNoS_ omega, SNoL x = 0 \/ exists y, SNo_max_of (SNoL x) y.
admit.
Qed.

Theorem SNoS_omega_SNoR_min_exists : forall x :e SNoS_ omega, SNoR x = 0 \/ exists y, SNo_min_of (SNoR x) y.
admit.
Qed.

End SNoMaxMin.

Section DiadicRationals.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.
Infix ^ 342 right := exp_SNo_nat.

Theorem nonneg_diadic_rational_p_SNoS_omega: forall k :e omega, forall n, nat_p n -> eps_ k * n :e SNoS_ omega.
admit.
Qed.

Definition diadic_rational_p : set -> prop := fun x => exists k :e omega, exists m :e int, x = eps_ k * m.

Theorem diadic_rational_p_SNoS_omega: forall x, diadic_rational_p x -> x :e SNoS_ omega.
admit.
Qed.

Theorem int_diadic_rational_p : forall m :e int, diadic_rational_p m.
admit.
Qed.

Theorem omega_diadic_rational_p : forall m :e omega, diadic_rational_p m.
admit.
Qed.

Theorem eps_diadic_rational_p : forall k :e omega, diadic_rational_p (eps_ k).
admit.
Qed.

Theorem minus_SNo_diadic_rational_p : forall x, diadic_rational_p x -> diadic_rational_p (- x).
admit.
Qed.

Theorem mul_SNo_diadic_rational_p : forall x y, diadic_rational_p x -> diadic_rational_p y -> diadic_rational_p (x * y).
admit.
Qed.

Theorem add_SNo_diadic_rational_p : forall x y, diadic_rational_p x -> diadic_rational_p y -> diadic_rational_p (x + y).
admit.
Qed.

Theorem SNoS_omega_diadic_rational_p_lem: forall n, nat_p n -> forall x, SNo x -> SNoLev x = n -> diadic_rational_p x.
admit.
Qed.

Theorem SNoS_omega_diadic_rational_p: forall x :e SNoS_ omega, diadic_rational_p x.
admit.
Qed.

Theorem mul_SNo_SNoS_omega : forall x y :e SNoS_ omega, x * y :e SNoS_ omega.
admit.
Qed.

End DiadicRationals.

Opaque int.

Section SurrealDiv.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.
Infix ^ 342 right := exp_SNo_nat.
Definition SNoL_pos : set -> set := fun x => {w :e SNoL x|0 < w}.

Theorem SNo_recip_pos_pos: forall x xi, SNo x -> SNo xi -> 0 < x -> x * xi = 1 -> 0 < xi.
admit.
Qed.

Theorem SNo_recip_lem1: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoL_pos x -> SNo x'i -> x' * x'i = 1 -> SNo y -> x * y < 1 -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> 1 < x * y'.
admit.
Qed.

Theorem SNo_recip_lem2: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoL_pos x -> SNo x'i -> x' * x'i = 1 -> SNo y -> 1 < x * y -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> x * y' < 1.
admit.
Qed.

Theorem SNo_recip_lem3: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoR x -> SNo x'i -> x' * x'i = 1 -> SNo y -> x * y < 1 -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> x * y' < 1.
admit.
Qed.

Theorem SNo_recip_lem4: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoR x -> SNo x'i -> x' * x'i = 1 -> SNo y -> 1 < x * y -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> 1 < x * y'.
admit.
Qed.

Definition SNo_recipauxset : set -> set -> set -> (set -> set) -> set := fun Y x X g => \/_ y :e Y, {(1 + (x' + - x) * y) * g x'|x' :e X}.

Theorem SNo_recipauxset_I: forall Y x X, forall g:set -> set,
 forall y :e Y, forall x' :e X, (1 + (x' + - x) * y) * g x' :e SNo_recipauxset Y x X g.
admit.
Qed.

Theorem SNo_recipauxset_E : forall Y x X, forall g:set -> set, forall z :e SNo_recipauxset Y x X g, forall p:prop, (forall y :e Y, forall x' :e X, z = (1 + (x' + - x) * y) * g x' -> p) -> p.
admit.
Qed.

Theorem SNo_recipauxset_ext: forall Y x X, forall g h:set -> set, (forall x' :e X, g x' = h x') -> SNo_recipauxset Y x X g = SNo_recipauxset Y x X h.
admit.
Qed.

Definition SNo_recipaux : set -> (set -> set) -> set -> set :=
 fun x g =>
  nat_primrec ({0},0)
   (fun k p => (p 0 :\/: SNo_recipauxset (p 0) x (SNoR x) g
                    :\/: SNo_recipauxset (p 1) x (SNoL_pos x) g,
                p 1 :\/: SNo_recipauxset (p 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (p 1) x (SNoR x) g)).

Theorem SNo_recipaux_0: forall x, forall g:set -> set, SNo_recipaux x g 0 = ({0},0).
admit.
Qed.

Theorem SNo_recipaux_S: forall x, forall g:set -> set, forall n, nat_p n ->
   SNo_recipaux x g (ordsucc n)
 = (SNo_recipaux x g n 0 :\/: SNo_recipauxset (SNo_recipaux x g n 0) x (SNoR x) g
        :\/: SNo_recipauxset (SNo_recipaux x g n 1) x (SNoL_pos x) g,
    SNo_recipaux x g n 1 :\/: SNo_recipauxset (SNo_recipaux x g n 0) x (SNoL_pos x) g
        :\/: SNo_recipauxset (SNo_recipaux x g n 1) x (SNoR x) g).
admit.
Qed.

Theorem SNo_recipaux_lem1: forall x, SNo x -> 0 < x ->
 forall g:set -> set,
    (forall x' :e SNoS_ (SNoLev x), 0 < x' -> SNo (g x') /\ x' * g x' = 1)
 -> forall k, nat_p k ->
         (forall y :e SNo_recipaux x g k 0, SNo y /\ x * y < 1)
      /\ (forall y :e SNo_recipaux x g k 1, SNo y /\ 1 < x * y).
admit.
Qed.

Theorem SNo_recipaux_lem2: forall x, SNo x -> 0 < x ->
 forall g:set -> set,
    (forall x' :e SNoS_ (SNoLev x), 0 < x' -> SNo (g x') /\ x' * g x' = 1)
 -> SNoCutP (\/_ k :e omega, SNo_recipaux x g k 0) (\/_ k :e omega, SNo_recipaux x g k 1).
admit.
Qed.

Theorem SNo_recipaux_ext: forall x, SNo x -> forall g h:set -> set, (forall x' :e SNoS_ (SNoLev x), g x' = h x') -> forall k, nat_p k -> SNo_recipaux x g k = SNo_recipaux x h k.
admit.
Qed.

Section recip_SNo_pos.
Let G : set -> (set -> set) -> set := fun x g => SNoCut (\/_ k :e omega, SNo_recipaux x g k 0) (\/_ k :e omega, SNo_recipaux x g k 1).
Definition recip_SNo_pos : set -> set := SNo_rec_i G.

Theorem recip_SNo_pos_eq: forall x, SNo x -> recip_SNo_pos x = G x recip_SNo_pos.
admit.
Qed.

Theorem recip_SNo_pos_prop1: forall x, SNo x -> 0 < x -> SNo (recip_SNo_pos x) /\ x * recip_SNo_pos x = 1.
admit.
Qed.

Theorem SNo_recip_SNo_pos: forall x, SNo x -> 0 < x -> SNo (recip_SNo_pos x).
admit.
Qed.

Theorem recip_SNo_pos_invR: forall x, SNo x -> 0 < x -> x * recip_SNo_pos x = 1.
admit.
Qed.

Theorem recip_SNo_pos_is_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo_pos x.
admit.
Qed.

Theorem recip_SNo_pos_invol: forall x, SNo x -> 0 < x -> recip_SNo_pos (recip_SNo_pos x) = x.
admit.
Qed.

Theorem recip_SNo_pos_eps_: forall n, nat_p n -> recip_SNo_pos (eps_ n) = 2 ^ n.
admit.
Qed.

Theorem recip_SNo_pos_pow_2: forall n, nat_p n -> recip_SNo_pos (2 ^ n) = eps_ n.
admit.
Qed.

Theorem recip_SNo_pos_2: recip_SNo_pos 2 = eps_ 1.
admit.
Qed.

End recip_SNo_pos.
Definition recip_SNo : set -> set := fun x => if 0 < x then recip_SNo_pos x else if x < 0 then - recip_SNo_pos (- x) else 0.

Theorem recip_SNo_poscase: forall x, 0 < x -> recip_SNo x = recip_SNo_pos x.
admit.
Qed.

Theorem recip_SNo_negcase: forall x, SNo x -> x < 0 -> recip_SNo x = - recip_SNo_pos (- x).
admit.
Qed.

Theorem recip_SNo_0: recip_SNo 0 = 0.
admit.
Qed.

Theorem SNo_recip_SNo: forall x, SNo x -> SNo (recip_SNo x).
admit.
Qed.

Theorem recip_SNo_invR: forall x, SNo x -> x <> 0 -> x * recip_SNo x = 1.
admit.
Qed.

Theorem recip_SNo_invL: forall x, SNo x -> x <> 0 -> recip_SNo x * x = 1.
admit.
Qed.

Theorem mul_SNo_nonzero_cancel_L: forall x y z, SNo x -> x <> 0 -> SNo y -> SNo z -> x * y = x * z -> y = z.
admit.
Qed.

Theorem recip_SNo_pow_2 : forall n, nat_p n -> recip_SNo (2 ^ n) = eps_ n.
admit.
Qed.

Theorem recip_SNo_of_pos_is_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo x.
admit.
Qed.

Definition div_SNo : set -> set -> set := fun x y => x * recip_SNo y.

Infix :/: 353 := div_SNo.

Theorem SNo_div_SNo: forall x y, SNo x -> SNo y -> SNo (x :/: y).
admit.
Qed.

Theorem div_SNo_0_num: forall x, SNo x -> 0 :/: x = 0.
admit.
Qed.

Theorem div_SNo_0_denum: forall x, SNo x -> x :/: 0 = 0.
admit.
Qed.

Theorem mul_div_SNo_invL: forall x y, SNo x -> SNo y -> y <> 0 -> (x :/: y) * y = x.
admit.
Qed.

Theorem mul_div_SNo_invR: forall x y, SNo x -> SNo y -> y <> 0 -> y * (x :/: y) = x.
admit.
Qed.

Theorem mul_div_SNo_R: forall x y z, SNo x -> SNo y -> SNo z -> (x :/: y) * z = (x * z) :/: y.
admit.
Qed.

Theorem mul_div_SNo_L: forall x y z, SNo x -> SNo y -> SNo z -> z * (x :/: y) = (z * x) :/: y.
admit.
Qed.

Theorem div_mul_SNo_invL: forall x y, SNo x -> SNo y -> y <> 0 -> (x * y) :/: y = x.
admit.
Qed.

Theorem div_div_SNo: forall x y z, SNo x -> SNo y -> SNo z -> (x :/: y) :/: z = x :/: (y * z).
admit.
Qed.

Theorem mul_div_SNo_both: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x :/: y) * (z :/: w) = (x * z) :/: (y * w).
admit.
Qed.

Theorem recip_SNo_pos_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo_pos x.
admit.
Qed.

Theorem div_SNo_pos_pos: forall x y, SNo x -> SNo y -> 0 < x -> 0 < y -> 0 < x :/: y.
admit.
Qed.

Theorem div_SNo_neg_pos: forall x y, SNo x -> SNo y -> x < 0 -> 0 < y -> x :/: y < 0.
admit.
Qed.

Theorem div_SNo_pos_LtL : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> x < z * y -> x :/: y < z.
admit.
Qed.

Theorem div_SNo_pos_LtR : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> z * y < x -> z < x :/: y.
admit.
Qed.

Theorem div_SNo_pos_LtL' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> x :/: y < z -> x < z * y.
admit.
Qed.

Theorem div_SNo_pos_LtR' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> z < x :/: y -> z * y < x.
admit.
Qed.

Theorem mul_div_SNo_nonzero_eq: forall x y z, SNo x -> SNo y -> SNo z -> y <> 0 -> x = y * z -> x :/: y = z.
admit.
Qed.

End SurrealDiv.

Opaque recip_SNo_pos recip_SNo.

Section Reals.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Theorem SNoS_omega_drat_intvl : forall x :e SNoS_ omega,
  forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
admit.
Qed.

Theorem SNoS_ordsucc_omega_bdd_above : forall x :e SNoS_ (ordsucc omega), x < omega -> exists N :e omega, x < N.
admit.
Qed.

Theorem SNoS_ordsucc_omega_bdd_below : forall x :e SNoS_ (ordsucc omega), - omega < x -> exists N :e omega, - N < x.
admit.
Qed.

Theorem SNoS_ordsucc_omega_bdd_drat_intvl : forall x :e SNoS_ (ordsucc omega),
    - omega < x -> x < omega
 -> forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
admit.
Qed.

Definition real : set := {x :e SNoS_ (ordsucc omega)| x <> omega /\ x <> - omega /\ (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)}.

Theorem real_I : forall x :e SNoS_ (ordsucc omega),
    x <> omega
 -> x <> - omega
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> x :e real.
admit.
Qed.

Theorem real_E : forall x :e real,
 forall p:prop,
      (SNo x
    -> SNoLev x :e ordsucc omega
    -> x :e SNoS_ (ordsucc omega)
    -> - omega < x
    -> x < omega
    -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
    -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
    -> p)
   -> p.
admit.
Qed.

Theorem real_SNo : forall x :e real, SNo x.
admit.
Qed.

Theorem real_SNoS_omega_prop : forall x :e real, forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x.
admit.
Qed.

Theorem SNoS_omega_real : SNoS_ omega c= real.
admit.
Qed.

Theorem real_0 : 0 :e real.
admit.
Qed.

Theorem real_1 : 1 :e real.
admit.
Qed.

Theorem SNoLev_In_real_SNoS_omega : forall x :e real, forall w, SNo w -> SNoLev w :e SNoLev x -> w :e SNoS_ omega.
admit.
Qed.

Theorem real_SNoCut_SNoS_omega: forall L R c= SNoS_ omega, SNoCutP L R
 -> L <> 0
 -> R <> 0
 -> (forall w :e L, exists w' :e L, w < w')
 -> (forall z :e R, exists z' :e R, z' < z)
 -> SNoCut L R :e real.
admit.
Qed.

Theorem real_SNoCut: forall L R c= real, SNoCutP L R
 -> L <> 0
 -> R <> 0
 -> (forall w :e L, exists w' :e L, w < w')
 -> (forall z :e R, exists z' :e R, z' < z)
 -> SNoCut L R :e real.
admit.
Qed.

Theorem minus_SNo_prereal_1 : forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - - x) < eps_ k) -> q = - x).
admit.
Qed.

Theorem minus_SNo_prereal_2 : forall x, SNo x ->
    (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < - x /\ - x < q + eps_ k).
admit.
Qed.

Theorem SNo_prereal_incr_lower_pos: forall x, SNo x -> 0 < x
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> forall k :e omega,
     forall p:prop,
         (forall q :e SNoS_ omega, 0 < q -> q < x -> x < q + eps_ k -> p)
      -> p.
admit.
Qed.

Theorem real_minus_SNo : forall x :e real, - x :e real.
admit.
Qed.

Theorem SNo_prereal_incr_lower_approx: forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> exists f :e SNoS_ omega :^: omega,
       forall n :e omega, f n < x /\ x < f n + eps_ n
                       /\ forall i :e n, f i < f n.
admit.
Qed.

Theorem SNo_prereal_decr_upper_approx: forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> exists g :e SNoS_ omega :^: omega,
       forall n :e omega, g n + - eps_ n < x /\ x < g n
                       /\ forall i :e n, g n < g i.
admit.
Qed.

Theorem SNoCutP_SNoCut_lim : forall lambda, ordinal lambda
 -> (forall alpha :e lambda, ordsucc alpha :e lambda)
 -> forall L R c= SNoS_ lambda, SNoCutP L R
 -> SNoLev (SNoCut L R) :e ordsucc lambda.
admit.
Qed.

Theorem SNoCutP_SNoCut_omega : forall L R c= SNoS_ omega, SNoCutP L R
 -> SNoLev (SNoCut L R) :e ordsucc omega.
admit.
Qed.

Theorem SNo_approx_real_lem:
  forall f g :e SNoS_ omega :^: omega,
     (forall n m :e omega, f n < g m)
  -> forall p:prop,
         (SNoCutP {f n|n :e omega} {g n|n :e omega}
       -> SNo (SNoCut {f n|n :e omega} {g n|n :e omega})
       -> SNoLev (SNoCut {f n|n :e omega} {g n|n :e omega}) :e ordsucc omega
       -> SNoCut {f n|n :e omega} {g n|n :e omega} :e SNoS_ (ordsucc omega)
       -> (forall n :e omega, f n < SNoCut {f n|n :e omega} {g n|n :e omega})
       -> (forall n :e omega, SNoCut {f n|n :e omega} {g n|n :e omega} < g n)
       -> p)
      -> p.
admit.
Qed.

Theorem SNo_approx_real: forall x, SNo x ->
 forall f g :e SNoS_ omega :^: omega,
     (forall n :e omega, f n < x)
  -> (forall n :e omega, x < f n + eps_ n)
  -> (forall n :e omega, forall i :e n, f i < f n)
  -> (forall n :e omega, x < g n)
  -> (forall n :e omega, forall i :e n, g n < g i)
  -> x = SNoCut {f n|n :e omega} {g n|n :e omega}
  -> x :e real.
admit.
Qed.

Theorem SNo_approx_real_rep : forall x :e real,
 forall p:prop,
     (forall f g :e SNoS_ omega :^: omega,
           (forall n :e omega, f n < x)
        -> (forall n :e omega, x < f n + eps_ n)
        -> (forall n :e omega, forall i :e n, f i < f n)
        -> (forall n :e omega, g n + - eps_ n < x)
        -> (forall n :e omega, x < g n)
        -> (forall n :e omega, forall i :e n, g n < g i)
        -> SNoCutP {f n|n :e omega} {g n|n :e omega}
        -> x = SNoCut {f n|n :e omega} {g n|n :e omega}
        -> p)
  -> p.
admit.
Qed.

Theorem real_add_SNo : forall x y :e real, x + y :e real.
admit.
Qed.

Theorem SNoS_ordsucc_omega_bdd_eps_pos : forall x :e SNoS_ (ordsucc omega), 0 < x -> x < omega -> exists N :e omega, eps_ N * x < 1.
admit.
Qed.

Theorem real_mul_SNo_pos : forall x y :e real, 0 < x -> 0 < y -> x * y :e real.
admit.
Qed.

Theorem real_mul_SNo : forall x y :e real, x * y :e real.
admit.
Qed.

Theorem nonneg_real_nat_interval: forall x :e real, 0 <= x -> exists n :e omega, n <= x /\ x < ordsucc n.
admit.
Qed.

Theorem pos_real_left_approx_double: forall x :e real, 0 < x
 -> x <> 2 -> (forall m :e omega, x <> eps_ m)
 -> exists w :e SNoL_pos x, x < 2 * w.
admit.
Qed.

Theorem real_recip_SNo_lem1: forall x, SNo x -> x :e real -> 0 < x ->
    recip_SNo_pos x :e real
 /\ forall k, nat_p k ->
         (SNo_recipaux x recip_SNo_pos k 0 c= real)
      /\ (SNo_recipaux x recip_SNo_pos k 1 c= real).
admit.
Qed.

Theorem real_recip_SNo_pos: forall x :e real, 0 < x -> recip_SNo_pos x :e real.
admit.
Qed.

Theorem real_recip_SNo: forall x :e real, recip_SNo x :e real.
admit.
Qed.

Theorem real_div_SNo: forall x y :e real, x :/: y :e real.
admit.
Qed.

End Reals.

Opaque real.

Section even_odd.

Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.

Theorem nat_le2_cases: forall m, nat_p m -> m c= 2 -> m = 0 \/ m = 1 \/ m = 2.
admit.
Qed.

Theorem prime_nat_2_lem: forall m, nat_p m -> forall n, nat_p n -> m * n = 2 -> m = 1 \/ m = 2.
admit.
Qed.

Theorem prime_nat_2: prime_nat 2.
admit.
Qed.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

Theorem not_eq_2m_2n1: forall m n :e int, 2 * m <> 2 * n + 1.
admit.
Qed.

End even_odd.

Section form100_22b.

Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

Theorem atleastp_SNoS_ordsucc_omega_Power_omega: atleastp (SNoS_ (ordsucc omega)) (Power omega).
admit.
Qed.

Theorem Repl_finite: forall f:set -> set, forall X, finite X -> finite {f x|x :e X}.
admit.
Qed.

Theorem infinite_bigger: forall X c= omega, infinite X -> forall m :e omega, exists n :e X, m :e n.
admit.
Qed.

Theorem equip_real_Power_omega: equip real (Power omega).
admit.
Qed.

Theorem form100_22_real_uncountable_atleastp: ~atleastp real omega.
admit.
Qed.

Theorem form100_22_real_uncountable_equip: ~equip real omega.
admit.
Qed.

Theorem form100_22_real_uncountable: atleastp omega real /\ ~equip real omega.
admit.
Qed.

End form100_22b.

Section rational.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix :/: 353 := div_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Definition rational : set := {x :e real | exists m :e int, exists n :e omega :\: {0}, x = m :/: n}.

End rational.

Section form100_3.

(** The Denumerability of the Rational Numbers **)

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.
Infix ^ 342 right := exp_SNo_nat.

Theorem Subq_int_SNoS_omega: int c= SNoS_ omega.
admit.
Qed.

Theorem Subq_SNoS_omega_rational: SNoS_ omega c= rational.
admit.
Qed.

Theorem Subq_rational_real: rational c= real.
admit.
Qed.

Theorem rational_minus_SNo: forall q :e rational, - q :e rational.
admit.
Qed.

Definition nat_pair : set -> set -> set := fun m n => 2 ^ m * (2 * n + 1).

Theorem nat_pair_In_omega: forall m n :e omega, nat_pair m n :e omega.
admit.
Qed.

Theorem nat_pair_0: forall m n m' n' :e omega, nat_pair m n = nat_pair m' n' -> m = m'.
admit.
Qed.

Theorem nat_pair_1: forall m n m' n' :e omega, nat_pair m n = nat_pair m' n' -> n = n'.
admit.
Qed.

Theorem form100_3: equip omega rational.
admit.
Qed.

End form100_3.

Section SurrealSqrt.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.
Infix ^ 342 right := exp_SNo_nat.
Definition SNoL_nonneg : set -> set := fun x => {w :e SNoL x|0 <= w}.

Theorem SNoL_nonneg_0: SNoL_nonneg 0 = 0.
admit.
Qed.

Theorem SNoL_nonneg_1: SNoL_nonneg 1 = 1.
admit.
Qed.

Definition SNo_sqrtauxset : set -> set -> set -> set := fun Y Z x => \/_ y :e Y, {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}.

Theorem SNo_sqrtauxset_I : forall Y Z x,
 forall y :e Y, forall z :e Z, 0 < y + z -> (x + y * z) :/: (y + z) :e SNo_sqrtauxset Y Z x.
admit.
Qed.

Theorem SNo_sqrtauxset_E : forall Y Z x,
 forall u :e SNo_sqrtauxset Y Z x, forall p:prop,
     (forall y :e Y, forall z :e Z, 0 < y + z -> u = (x + y * z) :/: (y + z) -> p)
  -> p.
admit.
Qed.

Theorem SNo_sqrtauxset_0: forall Z x, SNo_sqrtauxset 0 Z x = 0.
admit.
Qed.

Theorem SNo_sqrtauxset_0': forall Y x, SNo_sqrtauxset Y 0 x = 0.
admit.
Qed.

Definition SNo_sqrtaux : set -> (set -> set) -> set -> set :=
 fun x g =>
  nat_primrec ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x})
   (fun k p => (p 0 :\/: SNo_sqrtauxset (p 0) (p 1) x,
                p 1 :\/: SNo_sqrtauxset (p 0) (p 0) x
                    :\/: SNo_sqrtauxset (p 1) (p 1) x)).

Theorem SNo_sqrtaux_0: forall x, forall g:set -> set, SNo_sqrtaux x g 0 = ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x}).
admit.
Qed.

Theorem SNo_sqrtaux_S: forall x, forall g:set -> set, forall n, nat_p n
 -> SNo_sqrtaux x g (ordsucc n)
  = (SNo_sqrtaux x g n 0
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 0) (SNo_sqrtaux x g n 1) x,
     SNo_sqrtaux x g n 1
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 0) (SNo_sqrtaux x g n 0) x
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 1) (SNo_sqrtaux x g n 1) x).
admit.
Qed.

Theorem SNo_sqrtaux_mon_lem: forall x, forall g:set -> set,
  forall m, nat_p m -> forall n, nat_p n
   -> SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g (add_nat m n) 0
   /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g (add_nat m n) 1.
admit.
Qed.

Theorem SNo_sqrtaux_mon: forall x, forall g:set -> set,
  forall m, nat_p m -> forall n, nat_p n -> m c= n
   -> SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g n 0
   /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g n 1.
admit.
Qed.

Theorem SNo_sqrtaux_ext: forall x, SNo x -> forall g h:set -> set, (forall x' :e SNoS_ (SNoLev x), g x' = h x') -> forall k, nat_p k -> SNo_sqrtaux x g k = SNo_sqrtaux x h k.
admit.
Qed.

Section sqrt_SNo_nonneg.
Let G : set -> (set -> set) -> set := fun x g => SNoCut (\/_ k :e omega, SNo_sqrtaux x g k 0) (\/_ k :e omega, SNo_sqrtaux x g k 1).
Definition sqrt_SNo_nonneg : set -> set := SNo_rec_i G.

Theorem sqrt_SNo_nonneg_eq: forall x, SNo x -> sqrt_SNo_nonneg x = G x sqrt_SNo_nonneg.
admit.
Qed.

Theorem sqrt_SNo_nonneg_prop1a: forall x, SNo x -> 0 <= x ->
    (forall w :e SNoS_ (SNoLev x), 0 <= w -> SNo (sqrt_SNo_nonneg w) /\ 0 <= sqrt_SNo_nonneg w /\ sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w)
 -> forall k, nat_p k ->
              (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y).
admit.
Qed.

Theorem sqrt_SNo_nonneg_prop1b: forall x, SNo x -> 0 <= x
 -> (forall k, nat_p k ->
              (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y))
 -> SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1).
admit.
Qed.

Theorem sqrt_SNo_nonneg_prop1c: forall x, SNo x -> 0 <= x ->
    SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1)
 -> (forall z :e (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1), forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p)
 -> 0 <= G x sqrt_SNo_nonneg.
admit.
Qed.

Theorem sqrt_SNo_nonneg_prop1d: forall x, SNo x -> 0 <= x
  -> (forall w :e SNoS_ (SNoLev x), 0 <= w -> SNo (sqrt_SNo_nonneg w) /\ 0 <= sqrt_SNo_nonneg w /\ sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w)
  -> SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1)
  -> 0 <= G x sqrt_SNo_nonneg
  -> G x sqrt_SNo_nonneg * G x sqrt_SNo_nonneg < x
  -> False.
admit.
Qed.

Theorem sqrt_SNo_nonneg_prop1e: forall x, SNo x -> 0 <= x
  -> (forall w :e SNoS_ (SNoLev x), 0 <= w -> SNo (sqrt_SNo_nonneg w) /\ 0 <= sqrt_SNo_nonneg w /\ sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w)
  -> SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1)
  -> 0 <= G x sqrt_SNo_nonneg
  -> x < G x sqrt_SNo_nonneg * G x sqrt_SNo_nonneg
  -> False.
admit.
Qed.

Theorem sqrt_SNo_nonneg_prop1: forall x, SNo x -> 0 <= x -> SNo (sqrt_SNo_nonneg x) /\ 0 <= sqrt_SNo_nonneg x /\ sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
admit.
Qed.

End sqrt_SNo_nonneg.

Theorem SNo_sqrtaux_0_1_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
      (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x)
   /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y).
admit.
Qed.

Theorem SNo_sqrtaux_0_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
  forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x.
admit.
Qed.

Theorem SNo_sqrtaux_1_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
  forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y.
admit.
Qed.

Theorem SNo_sqrt_SNo_SNoCutP: forall x, SNo x -> 0 <= x ->
  SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0)
          (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1).
admit.
Qed.

Theorem SNo_sqrt_SNo_nonneg: forall x, SNo x -> 0 <= x -> SNo (sqrt_SNo_nonneg x).
admit.
Qed.

Theorem sqrt_SNo_nonneg_nonneg: forall x, SNo x -> 0 <= x -> 0 <= sqrt_SNo_nonneg x.
admit.
Qed.

Theorem sqrt_SNo_nonneg_sqr: forall x, SNo x -> 0 <= x -> sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
admit.
Qed.

Theorem sqrt_SNo_nonneg_0 : sqrt_SNo_nonneg 0 = 0.
admit.
Qed.

Theorem sqrt_SNo_nonneg_1 : sqrt_SNo_nonneg 1 = 1.
admit.
Qed.

Theorem sqrt_SNo_nonneg_0inL0: forall x, SNo x -> 0 <= x -> 0 :e SNoLev x -> 0 :e SNo_sqrtaux x sqrt_SNo_nonneg 0 0.
admit.
Qed.

Theorem sqrt_SNo_nonneg_Lnonempty: forall x, SNo x -> 0 <= x -> 0 :e SNoLev x -> (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) <> 0.
admit.
Qed.

Theorem sqrt_SNo_nonneg_Rnonempty: forall x, SNo x -> 0 <= x -> 1 :e SNoLev x -> (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1) <> 0.
admit.
Qed.

Theorem SNo_sqrtauxset_real: forall Y Z x, Y c= real -> Z c= real -> x :e real -> SNo_sqrtauxset Y Z x c= real.
admit.
Qed.

Theorem SNo_sqrtauxset_real_nonneg: forall Y Z x, Y c= {w :e real|0 <= w} -> Z c= {z :e real|0 <= z} -> x :e real -> 0 <= x -> SNo_sqrtauxset Y Z x c= {w :e real|0 <= w}.
admit.
Qed.

Theorem sqrt_SNo_nonneg_SNoS_omega: forall x :e SNoS_ omega, 0 <= x -> sqrt_SNo_nonneg x :e real.
admit.
Qed.

Theorem sqrt_SNo_nonneg_real: forall x :e real, 0 <= x -> sqrt_SNo_nonneg x :e real.
admit.
Qed.

End SurrealSqrt.
Opaque sqrt_SNo_nonneg.

Section form100_1.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.

Theorem divides_int_div_SNo_int: forall m n, divides_int m n -> n :/: m :e int.
admit.
Qed.

(** If m times m = 2 times n times n for naturals m and n, then n = 0. **)
Theorem form100_1_lem1 : forall m, nat_p m -> forall n, nat_p n -> m * m = 2 * n * n -> n = 0.
admit.
Qed.

(** There are no nonzero naturals m and n such that m times m = 2 times n times n. **)
Theorem form100_1_lem2 : forall m :e omega, forall n :e omega :\: 1, m * m <> 2 * n * n.
admit.
Qed.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.

Theorem sqrt_2_irrational: sqrt_SNo_nonneg 2 :e real :\: rational.
admit.
Qed.

End form100_1.

Section Topology.

(** from §12 Topological Spaces: definition of topology on X **)
Definition topology_on : set -> set -> prop := fun X T =>
  T c= Power X
/\ Empty :e T
/\ X :e T
/\ (forall UFam :e Power T, Union UFam :e T)
/\ (forall U :e T, forall V :e T, U :/\: V :e T).

(** from §12: definition of open sets in a topology **)
Definition open_in : set -> set -> set -> prop := fun X T U =>
  topology_on X T /\ U :e T.

(** from §12: closed set as complement of open set **)
Definition closed_in : set -> set -> set -> prop := fun X T C =>
  topology_on X T /\ exists U :e T, C = X :\: U.

(** from §12: complement of open set is closed **)
Theorem closed_of_open_complement : forall X T U:set,
  topology_on X T -> U :e T -> closed_in X T (X :\: U).
let X T U.
assume Htop: topology_on X T.
assume HU: U :e T.
prove topology_on X T /\ exists U0 :e T, X :\: U = X :\: U0.
apply andI.
- exact Htop.
- witness U.
  apply andI.
  - exact HU.
  - reflexivity.
Qed.

(** from §12: “finer than” / “coarser than” topologies **)
Definition finer_than : set -> set -> prop := fun T' T => T c= T'.

Definition coarser_than : set -> set -> prop := fun T' T => T' c= T.

 
(** from §12 Example 2: discrete topology **)
Definition discrete_topology : set -> set := fun X => Power X.

(** from §12: indiscrete/trivial topology **)
Definition indiscrete_topology : set -> set := fun X => {Empty, X}.

(** from §12 Example 3: finite complement topology **)
Definition finite_complement_topology : set -> set :=
  fun X => {U :e Power X | finite (X :\: U) \/ U = X}.

(** helper: placeholder for countable sets **)
Definition countable : set -> prop := fun _ => True.

(** from §12 Example 4: countable complement topology **)
Definition countable_complement_topology : set -> set :=
  fun X => {U :e Power X | countable (X :\: U) \/ U = X}.

(** from §12: discrete topology is a topology **)
Theorem discrete_topology_on : forall X, topology_on X (discrete_topology X).
admit.
Qed.

(** from §12: indiscrete topology is a topology **)
Theorem indiscrete_topology_on : forall X, topology_on X (indiscrete_topology X).
admit.
Qed.

(** from §12 Example 3: finite complement topology is a topology **)
Theorem finite_complement_topology_on : forall X, topology_on X (finite_complement_topology X).
admit.
Qed.

(** from §12: finer_than reflexive **)
Theorem finer_than_refl : forall T:set, finer_than T T.
let T.
exact (Subq_ref T).
Qed.

(** from §12: finer_than transitive **)
Theorem finer_than_trans : forall A B C:set, finer_than B A -> finer_than C B -> finer_than C A.
let A B C.
assume H1: finer_than B A.
assume H2: finer_than C B.
exact (Subq_tra A B C H1 H2).
Qed.

(** from §12: equivalence of finer/coarser phrasing **)
Theorem finer_coarser_dual : forall T T':set, finer_than T' T -> coarser_than T T'.
let T T'.
assume H.
exact H.
Qed.

(** from §12: comparability of topologies **)
Definition comparable_topologies : set -> set -> prop := fun T1 T2 =>
  finer_than T1 T2 \/ finer_than T2 T1.

(** from §12: equality of topologies **)
Definition topology_eq : set -> set -> set -> prop := fun X T1 T2 =>
  topology_on X T1 /\ topology_on X T2 /\ T1 = T2.

(** from §12: symmetry of topology equality **)
Theorem topology_eq_sym : forall X T1 T2:set, topology_eq X T1 T2 -> topology_eq X T2 T1.
admit.
Qed.

(** from §12: transitivity of topology equality **)
Theorem topology_eq_trans : forall X T1 T2 T3:set, topology_eq X T1 T2 -> topology_eq X T2 T3 -> topology_eq X T1 T3.
admit.
Qed.

(** from §12: reflexivity of topology equality **)
Theorem topology_eq_refl : forall X T:set, topology_on X T -> topology_eq X T T.
admit.
Qed.

(** from §12: strict fineness/coarseness **)
Definition strictly_finer_than : set -> set -> prop := fun T' T => finer_than T' T /\ ~finer_than T T'.

Definition strictly_coarser_than : set -> set -> prop := fun T' T => coarser_than T' T /\ ~coarser_than T T'.

(** from §12 examples: auxiliary aliases **)
Definition discrete_topology_alt : set -> set := discrete_topology.
Definition trivial_topology : set -> set := indiscrete_topology.

(** from §12: finer_than between topologies on same X **)
Definition finer_than_topology : set -> set -> set -> prop := fun X T' T =>
  topology_on X T' /\ topology_on X T /\ finer_than T' T.

(** from §12: finer/coarser equivalence **)
Theorem finer_than_def : forall T T':set, finer_than T' T <-> coarser_than T T'.
admit.
Qed.

(** from §12: discrete topology is the finest **)
Theorem discrete_topology_finest : forall X T:set,
  topology_on X T -> finer_than (discrete_topology X) T.
admit.
Qed.

(** from §12: indiscrete topology is the coarsest **)
Theorem indiscrete_topology_coarsest : forall X T:set,
  topology_on X T -> coarser_than (indiscrete_topology X) T.
admit.
Qed.

(** from §12: every subset is open in discrete topology **)
Theorem discrete_open_all : forall X U:set, U :e discrete_topology X.
admit.
Qed.

(** from §12: opens in indiscrete topology are Empty or X **)
Theorem indiscrete_open_iff : forall X U:set,
  U :e indiscrete_topology X <-> (U = Empty \/ U = X).
admit.
Qed.

(** from §12 Example 3: finite complement openness criterion **)
Theorem finite_complement_topology_open_criterion : forall X U:set,
  open_in X (finite_complement_topology X) U ->
  finite (X :\: U) \/ U = X.
admit.
Qed.

(** from §12 Example 3: Empty is open in finite complement topology **)
Theorem finite_complement_topology_contains_empty : forall X:set,
  Empty :e finite_complement_topology X.
admit.
Qed.

(** from §12 Example 3: X is open in finite complement topology **)
Theorem finite_complement_topology_contains_full : forall X:set,
  X :e finite_complement_topology X.
admit.
Qed.

(** from §12 Example 4: openness via countable complement **) 
Theorem countable_complement_topology_open_iff : forall X U:set,
  open_in X (countable_complement_topology X) U ->
  countable (X :\: U) \/ U = X.
admit.
Qed.

(** from §12 Example 4: Empty is open in countable complement topology **)
Theorem countable_complement_topology_contains_empty : forall X:set,
  Empty :e countable_complement_topology X.
admit.
Qed.

(** from §12 Example 4: X is open in countable complement topology **) 
Theorem countable_complement_topology_contains_full : forall X:set,
  X :e countable_complement_topology X.
admit.
Qed.

(** from §12 Example comparison: countable vs finite complement **)
Theorem countable_complement_finer_than_finite_complement : forall X:set,
  finer_than (countable_complement_topology X) (finite_complement_topology X).
admit.
Qed.

(** from §12 examples: finite complement coarser than discrete **)
Theorem finite_complement_coarser_than_discrete : forall X:set,
  coarser_than (finite_complement_topology X) (discrete_topology X).
admit.
Qed.

(** from §12 examples: indiscrete coarser than countable complement **) 
Theorem indiscrete_coarser_than_countable_complement : forall X:set,
  coarser_than (indiscrete_topology X) (countable_complement_topology X).
admit.
Qed.

(** from §12: fineness via set inclusion of topologies **)
Definition finer_than_topology_by_inclusion : set -> set -> set -> prop := fun X T' T =>
  topology_on X T' /\ topology_on X T /\ T c= T'.

Theorem finer_than_topology_by_inclusion_eq : forall X T' T:set,
  finer_than_topology X T' T <-> finer_than_topology_by_inclusion X T' T.
admit.
Qed.

(** from §12 axiom: arbitrary unions of opens are open **)
Theorem lemma_union_of_topology_family_open : forall X T UFam:set,
  topology_on X T ->
  UFam :e Power T ->
  Union UFam :e T.
admit.
Qed.

(** from §12 axiom: finite intersections of opens are open **)
Theorem lemma_intersection_two_open : forall X T U V:set,
  topology_on X T ->
  U :e T -> V :e T ->
  U :/\: V :e T.
admit.
Qed.

(** from §12: alternative naming for topological space **)
Definition topological_space : set -> set -> prop := topology_on.

Definition open_set_family : set -> set -> set := fun _ T => T.

Definition open_set : set -> set -> set -> prop := fun X T U => topology_on X T /\ U :e T.

(** from §13 Definition: basis for a topology **) 
Definition basis_on : set -> set -> prop := fun X B =>
  B c= Power X
  /\ (forall x :e X, exists b :e B, x :e b)
  /\ (forall b1 :e B, forall b2 :e B, forall x:set,
        x :e b1 -> x :e b2 ->
        exists b3 :e B, x :e b3 /\ b3 c= b1 :/\: b2).

(** from §13 Definition: topology generated by a basis **) 
Definition generated_topology : set -> set -> set := fun X B =>
  {U :e Power X | forall x :e U, exists b :e B, x :e b /\ b c= U}.

(** from §13: generated family is a topology **) 
Theorem lemma_topology_from_basis : forall X B:set,
  basis_on X B ->
  topology_on X (generated_topology X B).
admit.
Qed.

(** from §13: basis elements belong to generated topology **) 
Theorem generated_topology_contains_basis : forall X B:set,
  basis_on X B -> forall b:set, b :e B -> b :e generated_topology X B.
admit.
Qed.

(** from §13: shorthand for basis generating topology **) 
Definition basis_generates : set -> set -> set -> prop := fun X B T =>
  basis_on X B /\ generated_topology X B = T.

(** from §13: shorthand that a family refines all opens **) 
Definition basis_refines : set -> set -> set -> prop := fun X B T =>
  topology_on X T /\ (forall U :e T, forall x :e U, exists b :e B, x :e b /\ b c= U).

(** from §13: generated topology characterization **) 
Theorem lemma_generated_topology_characterization : forall X B:set,
  basis_on X B ->
  generated_topology X B
  = {U :e Power X | forall x :e U, exists b :e B, x :e b /\ b c= U}.
admit.
Qed.

(** from §13 Lemma 13.1: open sets are unions of basis elements **) 
Theorem open_sets_as_unions_of_basis : forall X B:set,
  basis_on X B ->
  forall U:set, open_in X (generated_topology X B) U ->
    exists Fam :e Power B, Union Fam = U.
admit.
Qed.

(** from §13 Lemma 13.1 converse direction **) 
Theorem basis_generates_open_sets : forall X B:set,
  basis_on X B ->
  forall U:set, (exists Fam :e Power B, Union Fam = U) ->
    open_in X (generated_topology X B) U.
admit.
Qed.

(** from §13 Lemma 13.1 corollary **) 
Theorem open_as_union_of_basis_elements : forall X B:set,
  basis_on X B ->
  forall U:set, open_in X (generated_topology X B) U ->
    U = Union {b :e B|b c= U}.
admit.
Qed.

(** from §13 Lemma 13.2: extracting a basis from an open refinement condition **) 
Theorem basis_refines_topology : forall X T C:set,
  topology_on X T ->
  (forall U :e T, forall x :e U, exists Cx :e C, x :e Cx /\ Cx c= U) ->
  basis_on X C /\ generated_topology X C = T.
admit.
Qed.

(** from §13 Lemma 13.2 (alias): open refinement family yields a basis **) 
Theorem lemma13_2_basis_from_open_subcollection : forall X T C:set,
  topology_on X T ->
  (forall c :e C, c :e T) ->
  (forall U :e T, forall x :e U, exists c :e C, x :e c /\ c c= U) ->
  basis_on X C /\ generated_topology X C = T.
admit.
Qed.

(** from §13: criterion for fineness via bases **) 
Theorem finer_via_basis : forall X B B':set,
  basis_on X B -> basis_on X B' ->
  (forall x :e X, forall b:set, b :e B -> x :e b ->
      exists b':set, b' :e B' /\ x :e b' /\ b' c= b) ->
  finer_than (generated_topology X B') (generated_topology X B).
admit.
Qed.

(** from §13 Lemma 13.3: basis inclusion criterion for fineness **) 
Theorem basis_finer_equiv_condition : forall X B B':set,
  basis_on X B -> basis_on X B' ->
  (forall x :e X, forall b :e B, x :e b -> exists b' :e B', x :e b' /\ b' c= b) <->
  finer_than (generated_topology X B') (generated_topology X B).
admit.
Qed.

(** from §13 Lemma 13.3 (direction): generated topology is minimal containing basis **) 
Theorem generated_topology_finer : forall X B T:set,
  basis_on X B -> topology_on X T ->
  (forall b :e B, b :e T) ->
  finer_than T (generated_topology X B).
admit.
Qed.

(** from §13 Lemma 13.3 (direction): generated topology is smallest with given basis **) 
Theorem topology_generated_by_basis_is_smallest : forall X B T:set,
  basis_on X B -> topology_on X T ->
  (forall b :e B, b :e T) ->
  finer_than T (generated_topology X B).
admit.
Qed.

(** from §13 Lemma 13.4: generated topology equals unions of basis elements **) 
Theorem union_of_basis_equals_open : forall X B:set,
  basis_on X B ->
  generated_topology X B = {Union Fam|Fam :e Power B}.
admit.
Qed.

(** from §13 Example 3: singleton basis **) 
Definition singleton_basis : set -> set := fun X => {{x}|x :e X}.

(** from §13 Example 3: singleton collection forms a basis **) 
Theorem singleton_basis_is_basis : forall X:set, basis_on X (singleton_basis X).
admit.
Qed.

(** from §13 Example 3: topology generated by singletons is discrete **) 
Theorem generated_topology_singletons_discrete : forall X:set,
  generated_topology X (singleton_basis X) = discrete_topology X.
admit.
Qed.

(** from §13 Example 4: circular vs rectangular region bases (abstract placeholders) **) 
Definition EuclidPlane : set := Empty.
Definition circular_regions : set := Empty.
Definition rectangular_regions : set := Empty.

Theorem circular_regions_basis_plane : basis_on EuclidPlane circular_regions.
admit.
Qed.

Theorem rectangular_regions_basis_plane : basis_on EuclidPlane rectangular_regions.
admit.
Qed.

Theorem circular_rectangular_same_topology_plane :
  generated_topology EuclidPlane circular_regions = generated_topology EuclidPlane rectangular_regions.
admit.
Qed.

(** from §13: refinement of basis yields finer topology **) 
Theorem lemma_finer_if_basis_refines : forall X B B':set,
  basis_on X B -> basis_refines X B' (generated_topology X B) ->
  finer_than (generated_topology X B) (generated_topology X B').
admit.
Qed.

(** from §13 Definition: subbasis and its generated topology **) 
Definition subbasis_on : set -> set -> prop := fun X S => S c= Power X.

(** from §13: finite intersections of subbasis elements (placeholder set of finite intersections) **) 
Definition finite_intersections_of : set -> set := fun _ => Empty.

(** from §13: basis obtained from a subbasis by finite intersections **) 
Definition basis_of_subbasis : set -> set -> set := fun _ S => {b :e finite_intersections_of S|True}.

(** from §13: topology generated by a subbasis **) 
Definition generated_topology_from_subbasis : set -> set -> set :=
  fun X S => generated_topology X (basis_of_subbasis X S).

(** from §13: finite intersections of a subbasis form a basis **) 
Theorem finite_intersections_basis_of_subbasis : forall X S:set,
  subbasis_on X S -> basis_on X (basis_of_subbasis X S).
admit.
Qed.

(** from §13: topology generated by a subbasis is a topology **) 
Theorem topology_from_subbasis_is_topology : forall X S:set,
  subbasis_on X S -> topology_on X (generated_topology_from_subbasis X S).
admit.
Qed.

(** from §13: generated topology from subbasis is minimal among topologies containing S **) 
Theorem topology_generated_by_basis_is_minimal : forall X S T:set,
  subbasis_on X S -> topology_on X T -> S c= T ->
  finer_than T (generated_topology_from_subbasis X S).
admit.
Qed.

(** from §13 Exercise 1: local openness implies set is open **) 
Theorem ex13_1_local_open_subset : forall X T A:set,
  topology_on X T ->
  (forall x :e A, exists U :e T, x :e U /\ U c= A) ->
  open_in X T A.
admit.
Qed.

(** from §13 Exercise 2: comparison of nine topologies on {a,b,c} **) 
Definition abc_set : set := UPair Empty Empty.
Definition top_abc_1 : set := Empty.
Definition top_abc_2 : set := Empty.
Definition top_abc_3 : set := Empty.
Definition top_abc_4 : set := Empty.
Definition top_abc_5 : set := Empty.
Definition top_abc_6 : set := Empty.
Definition top_abc_7 : set := Empty.
Definition top_abc_8 : set := Empty.
Definition top_abc_9 : set := Empty.

Theorem ex13_2_compare_nine_topologies :
  topology_on abc_set top_abc_1 /\ topology_on abc_set top_abc_2 /\
  topology_on abc_set top_abc_3 /\ topology_on abc_set top_abc_4 /\
  topology_on abc_set top_abc_5 /\ topology_on abc_set top_abc_6 /\
  topology_on abc_set top_abc_7 /\ topology_on abc_set top_abc_8 /\
  topology_on abc_set top_abc_9 /\
  exists finer_pairs:set, True.
admit.
Qed.

(** helper for §13 exercises: intersection of a family of topologies (placeholder) **) 
Definition Intersection_Fam : set -> set := fun _ => Empty.

(** from §13 Exercise 3: infinite-complement collection **) 
Definition infinite_complement_family : set -> set :=
  fun X => {U :e Power X | infinite (X :\: U) \/ U = Empty \/ U = X}.

Theorem ex13_3a_Tc_topology : forall X:set, topology_on X (countable_complement_topology X).
admit.
Qed.

Theorem ex13_3b_Tinfty_not_topology : forall X:set,
  ~topology_on X (infinite_complement_family X).
admit.
Qed.

(** from §13 Exercise 4(a): intersection of topologies **) 
Theorem ex13_4a_intersection_topology : forall X Fam:set,
  (forall T :e Fam, topology_on X T) ->
  topology_on X (Intersection_Fam Fam).
admit.
Qed.

(** from §13 Exercise 4(b): smallest/largest topology containing a family **) 
Theorem ex13_4b_smallest_largest : forall X Fam:set,
  exists Tmin, topology_on X Tmin /\ (forall T :e Fam, T c= Tmin) /\
    (forall T', topology_on X T' /\ (forall T :e Fam, T c= T') -> Tmin c= T') /\
  exists Tmax, topology_on X Tmax /\ (forall T :e Fam, Tmax c= T) /\
    (forall T', topology_on X T' /\ (forall T :e Fam, T' c= T) -> T' c= Tmax).
admit.
Qed.

(** from §13 Exercise 4(c): specific smallest/largest topology on {a,b,c} **) 
Theorem ex13_4c_specific_topologies :
  exists Tsmall Tall:set, topology_on abc_set Tsmall /\ topology_on abc_set Tall.
admit.
Qed.

(** from §13 Exercise 5: topology generated by a basis is intersection of topologies containing it **) 
Theorem ex13_5_basis_intersection : forall X A:set,
  basis_on X A ->
  generated_topology X A =
    Intersection_Fam {T :e Power (Power X)|topology_on X T /\ A c= T}.
admit.
Qed.

(** from §13 Exercise 6: incomparability of two real line topologies **) 
Definition R_lower_limit_topology : set := Empty.
Definition R_K_topology : set := Empty.

Theorem ex13_6_Rl_RK_not_comparable :
  ~finer_than R_lower_limit_topology R_K_topology /\
  ~finer_than R_K_topology R_lower_limit_topology.
admit.
Qed.

(** from §13 Exercise 7: containment relations among five ℝ topologies **) 
Definition R_standard_topology : set := Empty.
Definition R_finite_complement_topology : set := Empty.
Definition R_upper_limit_topology : set := Empty.
Definition R_ray_topology : set := Empty.

Theorem ex13_7_R_topology_containments :
  finer_than R_upper_limit_topology R_standard_topology /\
  finer_than R_K_topology R_standard_topology /\
  finer_than R_standard_topology R_finite_complement_topology /\
  finer_than R_standard_topology R_ray_topology.
admit.
Qed.

(** from §13 Exercise 8(a): rational open intervals generate standard topology on ℝ **) 
Definition R : set := Empty.
Definition rational_open_intervals_basis : set := Empty.

Theorem ex13_8a_rational_intervals_basis_standard :
  basis_on R rational_open_intervals_basis /\
  generated_topology R rational_open_intervals_basis = R_standard_topology.
admit.
Qed.

(** from §13 Exercise 8(b): half-open rational intervals generate a different topology **) 
Definition rational_halfopen_intervals_basis : set := Empty.

Theorem ex13_8b_halfopen_rational_basis_topology :
  basis_on R rational_halfopen_intervals_basis /\
  generated_topology R rational_halfopen_intervals_basis <> R_lower_limit_topology.
admit.
Qed.
