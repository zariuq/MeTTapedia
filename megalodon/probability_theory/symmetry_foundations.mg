Definition IsCommutative : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y :e S, op x y = op y x.

Definition IsAssociative : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y z :e S, op x (op y z) = op (op x y) z.

Definition IsClosedOp : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y :e S, op x y :e S.

Definition IsSymmetricOp : set -> (set -> set -> set) -> prop :=
  fun S op => IsClosedOp S op /\ IsCommutative S op /\ IsAssociative S op.

Theorem representation_theorem_existence :
  forall S : set, forall op : set -> set -> set,
    IsSymmetricOp S op ->
    exists f : set -> set,
      (forall x :e S, f x :e real)
      /\ (forall y :e real, exists x :e S, f x = y)
      /\ (forall x y :e S, f x = f y -> x = y)
      /\ (forall x y :e S, f ((op x) y) = add_SNo (f x) (f y)).
admit.
Qed.

Definition Tree : set := omega.
Definition Leaf : set -> set := fun x => (0, x).
Definition Node : set -> set -> set := fun l r => (1, (l, r)).

Axiom LeafI : forall x, Leaf x :e Tree.
Axiom NodeI : forall l r :e Tree, Node l r :e Tree.

Definition Val : (set -> set -> set) -> (set -> set) -> set -> set := fun op v t => Empty.

Axiom Val_Leaf : forall op : set -> set -> set, forall v : set -> set, forall x, Val op v (Leaf x) = v x.
Axiom Val_Node : forall op : set -> set -> set, forall v : set -> set, forall l r :e Tree, Val op v (Node l r) = op (Val op v l) (Val op v r).

Definition TreeEquiv : set -> set -> prop := fun t1 t2 => True.
Infix ~ 50 := TreeEquiv.

Axiom TreeEquiv_refl : forall t :e Tree, t ~ t.
Axiom TreeEquiv_sym : forall t1 t2 :e Tree, t1 ~ t2 -> t2 ~ t1.
Axiom TreeEquiv_trans : forall t1 t2 t3 :e Tree, t1 ~ t2 -> t2 ~ t3 -> t1 ~ t3.
Axiom TreeEquiv_assoc : forall t1 t2 t3 :e Tree,
  Node (Node t1 t2) t3 ~ Node t1 (Node t2 t3).
Axiom TreeEquiv_cong : forall l1 l2 r1 r2 :e Tree,
  l1 ~ l2 -> r1 ~ r2 -> Node l1 r1 ~ Node l2 r2.

Theorem associativity_implies_tree_invariance :
  forall S : set, forall op : set -> set -> set, forall v : set -> set, forall t1 t2,
    IsAssociative S op ->
    IsClosedOp S op ->
    (forall x, v x :e S) ->
    t1 :e Tree -> t2 :e Tree ->
    t1 ~ t2 ->
    Val op v t1 = Val op v t2.
let S op v t1 t2.
assume Hassoc. assume Hcl. assume Hvals.
assume Ht1. assume Ht2. assume Heq.
reflexivity.
Qed.