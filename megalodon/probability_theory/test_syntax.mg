Definition IsClosedOp : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y :e S, op x y :e S.

Definition IsCommutative : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y :e S, op x y = op y x.

Definition IsAssociative : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y z :e S, op x (op y z) = op (op x y) z.

Definition TestDef : set -> (set -> set -> set) -> prop :=
  fun S op => IsClosedOp S op /\ IsCommutative S op /\ IsAssociative S op.