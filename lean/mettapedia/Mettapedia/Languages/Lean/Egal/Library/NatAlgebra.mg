(** Algebraic laws derived from the natural recursor equations. The section
    hypotheses become parameters of the theorems; concrete interpretations
    supply their generated typing and equation proofs. **)

Section NatAlgebra.

Variable addOp : set -> set -> set.
Hypothesis AddType : forall x y :e Lean_Nat, addOp x y :e Lean_Nat.
Hypothesis AddZero : forall x :e Lean_Nat, addOp x Lean_Nat_zero_node = x.
Hypothesis AddSucc : forall x y :e Lean_Nat,
  addOp x (Lean_Nat_succ_node y) = Lean_Nat_succ_node (addOp x y).

Theorem NatAlgebra_add_zeroL : forall x :e Lean_Nat, addOp Lean_Nat_zero_node x = x.
apply Lean_Nat_ind.
- exact AddZero Lean_Nat_zero_node Lean_Nat_zero_typed.
- let x. assume Hx: x :e Lean_Nat.
  assume IH: addOp Lean_Nat_zero_node x = x.
  rewrite AddSucc Lean_Nat_zero_node Lean_Nat_zero_typed x Hx.
  rewrite IH. reflexivity.
Qed.

Theorem NatAlgebra_add_succL : forall x y :e Lean_Nat,
  addOp (Lean_Nat_succ_node x) y = Lean_Nat_succ_node (addOp x y).
let x. assume Hx: x :e Lean_Nat.
apply Lean_Nat_ind.
- rewrite AddZero (Lean_Nat_succ_node x) (Lean_Nat_succ_typed x Hx).
  rewrite AddZero x Hx. reflexivity.
- let y. assume Hy: y :e Lean_Nat.
  assume IH: addOp (Lean_Nat_succ_node x) y = Lean_Nat_succ_node (addOp x y).
  rewrite AddSucc (Lean_Nat_succ_node x) (Lean_Nat_succ_typed x Hx) y Hy.
  rewrite AddSucc x Hx y Hy.
  rewrite IH. reflexivity.
Qed.

Theorem NatAlgebra_add_assoc : forall x y z :e Lean_Nat,
  addOp (addOp x y) z = addOp x (addOp y z).
let x. assume Hx: x :e Lean_Nat. let y. assume Hy: y :e Lean_Nat.
apply Lean_Nat_ind.
- rewrite AddZero y Hy.
  rewrite AddZero (addOp x y) (AddType x Hx y Hy). reflexivity.
- let z. assume Hz: z :e Lean_Nat.
  assume IH: addOp (addOp x y) z = addOp x (addOp y z).
  rewrite AddSucc y Hy z Hz.
  rewrite AddSucc (addOp x y) (AddType x Hx y Hy) z Hz.
  rewrite AddSucc x Hx (addOp y z) (AddType y Hy z Hz).
  rewrite IH. reflexivity.
Qed.

Theorem NatAlgebra_add_comm : forall x y :e Lean_Nat, addOp x y = addOp y x.
let x. assume Hx: x :e Lean_Nat.
apply Lean_Nat_ind.
- rewrite AddZero x Hx. rewrite NatAlgebra_add_zeroL x Hx. reflexivity.
- let y. assume Hy: y :e Lean_Nat. assume IH: addOp x y = addOp y x.
  rewrite AddSucc x Hx y Hy.
  rewrite NatAlgebra_add_succL y Hy x Hx.
  rewrite IH. reflexivity.
Qed.

Theorem NatAlgebra_add_oneR : forall x :e Lean_Nat,
  addOp x (Lean_Nat_succ_node Lean_Nat_zero_node) = Lean_Nat_succ_node x.
let x. assume Hx: x :e Lean_Nat.
rewrite AddSucc x Hx Lean_Nat_zero_node Lean_Nat_zero_typed.
rewrite AddZero x Hx. reflexivity.
Qed.

Theorem NatAlgebra_add_swap : forall x y z :e Lean_Nat,
  addOp (addOp x y) z = addOp (addOp x z) y.
let x. assume Hx: x :e Lean_Nat. let y. assume Hy: y :e Lean_Nat.
let z. assume Hz: z :e Lean_Nat.
rewrite NatAlgebra_add_assoc x Hx y Hy z Hz.
rewrite NatAlgebra_add_comm y Hy z Hz.
rewrite <- NatAlgebra_add_assoc x Hx z Hz y Hy. reflexivity.
Qed.

Variable mulOp : set -> set -> set.
Hypothesis MulType : forall x y :e Lean_Nat, mulOp x y :e Lean_Nat.
Hypothesis MulZero : forall x :e Lean_Nat, mulOp x Lean_Nat_zero_node = Lean_Nat_zero_node.
Hypothesis MulSucc : forall x y :e Lean_Nat,
  mulOp x (Lean_Nat_succ_node y) = addOp (mulOp x y) x.

Theorem NatAlgebra_mul_zeroL : forall x :e Lean_Nat,
  mulOp Lean_Nat_zero_node x = Lean_Nat_zero_node.
apply Lean_Nat_ind.
- exact MulZero Lean_Nat_zero_node Lean_Nat_zero_typed.
- let x. assume Hx: x :e Lean_Nat.
  assume IH: mulOp Lean_Nat_zero_node x = Lean_Nat_zero_node.
  rewrite MulSucc Lean_Nat_zero_node Lean_Nat_zero_typed x Hx.
  rewrite IH. exact AddZero Lean_Nat_zero_node Lean_Nat_zero_typed.
Qed.

Theorem NatAlgebra_mul_addR : forall x y z :e Lean_Nat,
  mulOp x (addOp y z) = addOp (mulOp x y) (mulOp x z).
let x. assume Hx: x :e Lean_Nat. let y. assume Hy: y :e Lean_Nat.
apply Lean_Nat_ind.
- rewrite AddZero y Hy. rewrite MulZero x Hx.
  rewrite AddZero (mulOp x y) (MulType x Hx y Hy). reflexivity.
- let z. assume Hz: z :e Lean_Nat.
  assume IH: mulOp x (addOp y z) = addOp (mulOp x y) (mulOp x z).
  rewrite AddSucc y Hy z Hz.
  rewrite MulSucc x Hx z Hz.
  rewrite MulSucc x Hx (addOp y z) (AddType y Hy z Hz).
  rewrite IH.
  exact NatAlgebra_add_assoc (mulOp x y) (MulType x Hx y Hy)
    (mulOp x z) (MulType x Hx z Hz) x Hx.
Qed.

Theorem NatAlgebra_mul_assoc : forall x y z :e Lean_Nat,
  mulOp (mulOp x y) z = mulOp x (mulOp y z).
let x. assume Hx: x :e Lean_Nat. let y. assume Hy: y :e Lean_Nat.
apply Lean_Nat_ind.
- rewrite MulZero y Hy. rewrite MulZero x Hx.
  rewrite MulZero (mulOp x y) (MulType x Hx y Hy). reflexivity.
- let z. assume Hz: z :e Lean_Nat.
  assume IH: mulOp (mulOp x y) z = mulOp x (mulOp y z).
  rewrite MulSucc y Hy z Hz.
  rewrite MulSucc (mulOp x y) (MulType x Hx y Hy) z Hz.
  rewrite NatAlgebra_mul_addR x Hx (mulOp y z) (MulType y Hy z Hz) y Hy.
  rewrite IH. reflexivity.
Qed.

Theorem NatAlgebra_mul_oneR : forall x :e Lean_Nat,
  mulOp x (Lean_Nat_succ_node Lean_Nat_zero_node) = x.
let x. assume Hx: x :e Lean_Nat.
rewrite MulSucc x Hx Lean_Nat_zero_node Lean_Nat_zero_typed.
rewrite MulZero x Hx. exact NatAlgebra_add_zeroL x Hx.
Qed.

Theorem NatAlgebra_mul_oneL : forall x :e Lean_Nat,
  mulOp (Lean_Nat_succ_node Lean_Nat_zero_node) x = x.
apply Lean_Nat_ind.
- exact MulZero (Lean_Nat_succ_node Lean_Nat_zero_node)
    (Lean_Nat_succ_typed Lean_Nat_zero_node Lean_Nat_zero_typed).
- let x. assume Hx: x :e Lean_Nat.
  assume IH: mulOp (Lean_Nat_succ_node Lean_Nat_zero_node) x = x.
  rewrite MulSucc (Lean_Nat_succ_node Lean_Nat_zero_node)
    (Lean_Nat_succ_typed Lean_Nat_zero_node Lean_Nat_zero_typed) x Hx.
  rewrite IH. exact NatAlgebra_add_oneR x Hx.
Qed.

Theorem NatAlgebra_mul_succL : forall x y :e Lean_Nat,
  mulOp (Lean_Nat_succ_node x) y = addOp (mulOp x y) y.
let x. assume Hx: x :e Lean_Nat.
apply Lean_Nat_ind.
- rewrite MulZero (Lean_Nat_succ_node x) (Lean_Nat_succ_typed x Hx).
  rewrite MulZero x Hx. rewrite AddZero Lean_Nat_zero_node Lean_Nat_zero_typed. reflexivity.
- let y. assume Hy: y :e Lean_Nat.
  assume IH: mulOp (Lean_Nat_succ_node x) y = addOp (mulOp x y) y.
  rewrite MulSucc (Lean_Nat_succ_node x) (Lean_Nat_succ_typed x Hx) y Hy.
  rewrite MulSucc x Hx y Hy. rewrite IH.
  rewrite AddSucc (addOp (mulOp x y) y) (AddType (mulOp x y) (MulType x Hx y Hy) y Hy) x Hx.
  rewrite AddSucc (addOp (mulOp x y) x) (AddType (mulOp x y) (MulType x Hx y Hy) x Hx) y Hy.
  rewrite NatAlgebra_add_swap (mulOp x y) (MulType x Hx y Hy) y Hy x Hx. reflexivity.
Qed.

Theorem NatAlgebra_additive :
  Lean_AddCommMonoidOf Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat addOp) Lean_Nat_zero_node
    (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) :e Lean_AddCommMonoid Lean_Nat.
claim AApp: forall x y :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat addOp) x y = addOp x y.
{ exact Lean_BinaryMap_apply Lean_Nat Lean_Nat addOp. }
claim MApp: forall n x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) n x = mulOp n x.
{ exact Lean_BinaryMap_apply Lean_Nat Lean_Nat mulOp. }
claim AAssoc: forall x y z :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat addOp) ((Lean_BinaryMap Lean_Nat Lean_Nat addOp) x y) z =
  (Lean_BinaryMap Lean_Nat Lean_Nat addOp) x ((Lean_BinaryMap Lean_Nat Lean_Nat addOp) y z).
{ let x. assume Hx: x :e Lean_Nat. let y. assume Hy: y :e Lean_Nat.
  let z. assume Hz: z :e Lean_Nat.
  rewrite AApp x Hx y Hy. rewrite AApp y Hy z Hz.
  rewrite AApp (addOp x y) (AddType x Hx y Hy) z Hz.
  rewrite AApp x Hx (addOp y z) (AddType y Hy z Hz).
  exact NatAlgebra_add_assoc x Hx y Hy z Hz. }
claim ALeft: forall x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat addOp) Lean_Nat_zero_node x = x.
{ let x. assume Hx: x :e Lean_Nat.
  rewrite AApp Lean_Nat_zero_node Lean_Nat_zero_typed x Hx. exact NatAlgebra_add_zeroL x Hx. }
claim ARight: forall x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat addOp) x Lean_Nat_zero_node = x.
{ let x. assume Hx: x :e Lean_Nat.
  rewrite AApp x Hx Lean_Nat_zero_node Lean_Nat_zero_typed. exact AddZero x Hx. }
claim MZero: forall x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) (LeanNum 0) x = Lean_Nat_zero_node.
{ let x. assume Hx: x :e Lean_Nat.
  rewrite MApp (LeanNum 0) (LeanNum_In 0 nat_0) x Hx.
  rewrite LeanNum_0. exact NatAlgebra_mul_zeroL x Hx. }
claim MSucc: forall n x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) (Lean_Nat_succ_node n) x =
  (Lean_BinaryMap Lean_Nat Lean_Nat addOp) ((Lean_BinaryMap Lean_Nat Lean_Nat mulOp) n x) x.
{ let n. assume Hn: n :e Lean_Nat. let x. assume Hx: x :e Lean_Nat.
  rewrite MApp (Lean_Nat_succ_node n) (Lean_Nat_succ_typed n Hn) x Hx.
  rewrite MApp n Hn x Hx. rewrite AApp (mulOp n x) (MulType n Hn x Hx) x Hx.
  exact NatAlgebra_mul_succL n Hn x Hx. }
claim Parent: Lean_AddMonoidOf Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat addOp)
  Lean_Nat_zero_node (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) :e Lean_AddMonoid Lean_Nat.
{ exact Lean_AddMonoidOf_typed Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat addOp)
    (Lean_BinaryMap_typed Lean_Nat Lean_Nat Lean_Nat addOp AddType)
    Lean_Nat_zero_node Lean_Nat_zero_typed (Lean_BinaryMap Lean_Nat Lean_Nat mulOp)
    (Lean_BinaryMap_typed Lean_Nat Lean_Nat Lean_Nat mulOp MulType) AAssoc ALeft ARight MZero MSucc. }
claim AComm: forall x y :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat addOp) x y = (Lean_BinaryMap Lean_Nat Lean_Nat addOp) y x.
{ let x. assume Hx: x :e Lean_Nat. let y. assume Hy: y :e Lean_Nat.
  rewrite AApp x Hx y Hy. rewrite AApp y Hy x Hx. exact NatAlgebra_add_comm x Hx y Hy. }
exact Lean_AddCommMonoidOf_typed Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat addOp)
  Lean_Nat_zero_node (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) Parent AComm.
Qed.

Variable powOp : set -> set -> set.
Hypothesis PowType : forall x n :e Lean_Nat, powOp x n :e Lean_Nat.
Hypothesis PowZero : forall x :e Lean_Nat,
  powOp x (LeanNum 0) = Lean_Nat_succ_node Lean_Nat_zero_node.
Hypothesis PowSucc : forall x n :e Lean_Nat,
  powOp x (Lean_Nat_succ_node n) = mulOp (powOp x n) x.

Theorem NatAlgebra_monoid :
  Lean_MonoidOf Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat mulOp)
    (Lean_Nat_succ_node Lean_Nat_zero_node)
    (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => powOp x n)) :e Lean_Monoid Lean_Nat.
claim MApp: forall x y :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) x y = mulOp x y.
{ exact Lean_BinaryMap_apply Lean_Nat Lean_Nat mulOp. }
claim PApp: forall n x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => powOp x n)) n x = powOp x n.
{ exact Lean_BinaryMap_apply Lean_Nat Lean_Nat (fun n x => powOp x n). }
claim MAssoc: forall x y z :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) ((Lean_BinaryMap Lean_Nat Lean_Nat mulOp) x y) z =
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) x ((Lean_BinaryMap Lean_Nat Lean_Nat mulOp) y z).
{ let x. assume Hx: x :e Lean_Nat. let y. assume Hy: y :e Lean_Nat.
  let z. assume Hz: z :e Lean_Nat.
  rewrite MApp x Hx y Hy. rewrite MApp y Hy z Hz.
  rewrite MApp (mulOp x y) (MulType x Hx y Hy) z Hz.
  rewrite MApp x Hx (mulOp y z) (MulType y Hy z Hz).
  exact NatAlgebra_mul_assoc x Hx y Hy z Hz. }
claim MLeft: forall x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) (Lean_Nat_succ_node Lean_Nat_zero_node) x = x.
{ let x. assume Hx: x :e Lean_Nat.
  rewrite MApp (Lean_Nat_succ_node Lean_Nat_zero_node)
    (Lean_Nat_succ_typed Lean_Nat_zero_node Lean_Nat_zero_typed) x Hx.
  exact NatAlgebra_mul_oneL x Hx. }
claim MRight: forall x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp) x (Lean_Nat_succ_node Lean_Nat_zero_node) = x.
{ let x. assume Hx: x :e Lean_Nat.
  rewrite MApp x Hx (Lean_Nat_succ_node Lean_Nat_zero_node)
    (Lean_Nat_succ_typed Lean_Nat_zero_node Lean_Nat_zero_typed).
  exact NatAlgebra_mul_oneR x Hx. }
claim PZero: forall x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => powOp x n)) (LeanNum 0) x =
    Lean_Nat_succ_node Lean_Nat_zero_node.
{ let x. assume Hx: x :e Lean_Nat.
  rewrite PApp (LeanNum 0) (LeanNum_In 0 nat_0) x Hx. exact PowZero x Hx. }
claim PSucc: forall n x :e Lean_Nat,
  (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => powOp x n)) (Lean_Nat_succ_node n) x =
  (Lean_BinaryMap Lean_Nat Lean_Nat mulOp)
    ((Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => powOp x n)) n x) x.
{ let n. assume Hn: n :e Lean_Nat. let x. assume Hx: x :e Lean_Nat.
  rewrite PApp (Lean_Nat_succ_node n) (Lean_Nat_succ_typed n Hn) x Hx.
  rewrite PApp n Hn x Hx.
  rewrite MApp (powOp x n) (PowType x Hx n Hn) x Hx.
  exact PowSucc x Hx n Hn. }
exact Lean_MonoidOf_typed Lean_Nat (Lean_BinaryMap Lean_Nat Lean_Nat mulOp)
  (Lean_BinaryMap_typed Lean_Nat Lean_Nat Lean_Nat mulOp MulType)
  (Lean_Nat_succ_node Lean_Nat_zero_node)
  (Lean_Nat_succ_typed Lean_Nat_zero_node Lean_Nat_zero_typed)
  (Lean_BinaryMap Lean_Nat Lean_Nat (fun n x => powOp x n))
  (Lean_BinaryMap_typed Lean_Nat Lean_Nat Lean_Nat (fun n x => powOp x n)
    (fun n Hn x Hx => PowType x Hx n Hn)) MAssoc MLeft MRight PZero PSucc.
Qed.

End NatAlgebra.
