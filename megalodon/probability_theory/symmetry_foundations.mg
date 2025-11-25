Definition IsCommutative : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y :e S, op x y = op y x.

Definition IsAssociative : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y z :e S, op x (op y z) = op (op x y) z.

Definition IsClosedOp : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y :e S, op x y :e S.

Definition IsSymmetricOp : set -> (set -> set -> set) -> prop :=
  fun S op => IsClosedOp S op /\ IsCommutative S op /\ IsAssociative S op.

Theorem IsCommutativeI : forall S : set, forall op : (set -> set -> set), (forall x y :e S, op x y = op y x) -> IsCommutative S op.
exact (fun S op H => H).
Qed.

Theorem IsAssociativeI : forall S : set, forall op : (set -> set -> set), (forall x y z :e S, op x (op y z) = op (op x y) z) -> IsAssociative S op.
exact (fun S op H => H).
Qed.

(* Proof that Real Addition is Symmetric *)

Theorem real_plus_is_symmetric : IsSymmetricOp real add_SNo.
prove IsClosedOp real add_SNo /\ IsCommutative real add_SNo /\ IsAssociative real add_SNo.
apply andI.
- apply andI.
  + prove IsClosedOp real add_SNo.
    exact real_add_SNo.
  + apply IsCommutativeI.
    prove forall x y :e real, x + y = y + x.
    let x y. assume Hx: x :e real. assume Hy: y :e real.
    apply add_SNo_com x y.
    * exact real_SNo x Hx.
    * exact real_SNo y Hy.
- apply IsAssociativeI.
  prove forall x y z :e real, x + (y + z) = (x + y) + z.
  let x y z. assume Hx: x :e real. assume Hy: y :e real. assume Hz: z :e real.
  apply add_SNo_assoc x y z.
  + exact real_SNo x Hx.
  + exact real_SNo y Hy.
  + exact real_SNo z Hz.
Qed.

(* Isomorphic Operations *)

Definition IsomorphicOp : set -> (set -> set -> set) -> set -> (set -> set -> set) -> (set -> set) -> prop :=
  fun S1 op1 S2 op2 f =>
    (forall x :e S1, f x :e S2)
    /\ (forall y :e S2, exists x :e S1, f x = y)
    /\ (forall x y :e S1, f x = f y -> x = y)
    /\ (forall x y :e S1, f (op1 x y) = op2 (f x) (f y)).

Theorem isomorphism_preserves_associativity :
  forall S1 op1 S2 op2 f,
    IsClosedOp S1 op1 ->
    IsomorphicOp S1 op1 S2 op2 f ->
    IsAssociative S2 op2 ->
    IsAssociative S1 op1.
let S1 op1 S2 op2 f.
assume Hcl: IsClosedOp S1 op1.
assume Hiso: IsomorphicOp S1 op1 S2 op2 f.
assume Hassoc2: IsAssociative S2 op2.
apply IsAssociativeI.
prove forall x y z :e S1, op1 x (op1 y z) = op1 (op1 x y) z.
let x y z. assume Hx: x :e S1. assume Hy: y :e S1. assume Hz: z :e S1.

(* Extract properties of f *)
claim Hinj: forall a b :e S1, f a = f b -> a = b.
  exact andEL (forall x y :e S1, f x = f y -> x = y) (forall x y :e S1, f (op1 x y) = op2 (f x) (f y)) (andER (forall y :e S2, exists x :e S1, f x = y) ((forall x y :e S1, f x = f y -> x = y) /\ (forall x y :e S1, f (op1 x y) = op2 (f x) (f y))) (andER (forall x :e S1, f x :e S2) ((forall y :e S2, exists x :e S1, f x = y) /\ ((forall x y :e S1, f x = f y -> x = y) /\ (forall x y :e S1, f (op1 x y) = op2 (f x) (f y)))) Hiso)).

claim Hhom: forall a b :e S1, f (op1 a b) = op2 (f a) (f b).
  exact andER (forall x y :e S1, f x = f y -> x = y) (forall x y :e S1, f (op1 x y) = op2 (f x) (f y)) (andER (forall y :e S2, exists x :e S1, f x = y) ((forall x y :e S1, f x = f y -> x = y) /\ (forall x y :e S1, f (op1 x y) = op2 (f x) (f y))) (andER (forall x :e S1, f x :e S2) ((forall y :e S2, exists x :e S1, f x = y) /\ ((forall x y :e S1, f x = f y -> x = y) /\ (forall x y :e S1, f (op1 x y) = op2 (f x) (f y)))) Hiso)).

claim Hmap: forall a :e S1, f a :e S2.
  exact andEL (forall x :e S1, f x :e S2) ((forall y :e S2, exists x :e S1, f x = y) /\ ((forall x y :e S1, f x = f y -> x = y) /\ (forall x y :e S1, f (op1 x y) = op2 (f x) (f y)))) Hiso.

(* Facts about elements in S1 *)
claim Hxy: op1 x y :e S1. exact Hcl x Hx y Hy.
claim Hyz: op1 y z :e S1. exact Hcl y Hy z Hz.
claim Hxy_z: op1 (op1 x y) z :e S1. exact Hcl (op1 x y) Hxy z Hz.
claim Hx_yz: op1 x (op1 y z) :e S1. exact Hcl x Hx (op1 y z) Hyz.

(* Facts about images in S2 *)
claim Hfx: f x :e S2. exact Hmap x Hx.
claim Hfy: f y :e S2. exact Hmap y Hy.
claim Hfz: f z :e S2. exact Hmap z Hz.

(* Compute f(LHS) *)
claim EqL: f (op1 x (op1 y z)) = op2 (f x) (op2 (f y) (f z)).
  apply eq_tra (f (op1 x (op1 y z))) (op2 (f x) (f (op1 y z))) (op2 (f x) (op2 (f y) (f z))).
  - exact Hhom x (op1 y z) Hx Hyz.
  - apply opeq2 (f (op1 y z)) (op2 (f y) (f z)) (f x).
    exact Hhom y z Hy Hz.

(* Compute f(RHS) *)
claim EqR: f (op1 (op1 x y) z) = op2 (op2 (f x) (f y)) (f z).
  apply eq_tra (f (op1 (op1 x y) z)) (op2 (f (op1 x y)) (f z)) (op2 (op2 (f x) (f y)) (f z)).
  - exact Hhom (op1 x y) z Hxy Hz.
  - apply opeq1 (f (op1 x y)) (op2 (f x) (f y)) (f z).
    exact Hhom x y Hx Hy.

(* Associativity in S2 *)
claim EqAssoc: op2 (f x) (op2 (f y) (f z)) = op2 (op2 (f x) (f y)) (f z).
  exact Hassoc2 (f x) Hfx (f y) Hfy (f z) Hfz.

(* f(LHS) = f(RHS) *)
claim EqF: f (op1 x (op1 y z)) = f (op1 (op1 x y) z).
  apply eq_tra (f (op1 x (op1 y z))) (op2 (f x) (op2 (f y) (f z))) (f (op1 (op1 x y) z)).
  - exact EqL.
  - apply eq_tra (op2 (f x) (op2 (f y) (f z))) (op2 (op2 (f x) (f y)) (f z)) (f (op1 (op1 x y) z)).
    + exact EqAssoc.
    + symmetry. exact EqR.

(* Injectivity *)
apply Hinj (op1 x (op1 y z)) (op1 (op1 x y) z) Hx_yz Hxy_z EqF.
Qed.
