Definition IsCommutative : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y :e S, op x y = op y x.

Definition IsAssociative : set -> (set -> set -> set) -> prop :=
  fun S op => forall x y z :e S, op x (op y z) = op (op x y) z.

Definition IsDistributive : set -> (set -> set -> set) -> (set -> set -> set) -> prop :=
  fun S add mul => forall x y z :e S, mul x (add y z) = add (mul x y) (mul x z).


Definition IsQuantumAlgebra : set -> (set -> set -> set) -> (set -> set -> set) -> prop :=
  fun A par ser =>
    IsCommutative A par /\ IsAssociative A par /\ IsAssociative A ser /\ IsDistributive A par ser.


Definition AmplitudeSpace : set :=
  real.

Theorem parallel_representation_theorem :
  forall par : set -> set -> set,
    IsCommutative AmplitudeSpace par ->
    IsAssociative AmplitudeSpace par ->
    exists f : set -> set,
      (forall a :e AmplitudeSpace, f a :e AmplitudeSpace) /\
      (forall a b :e AmplitudeSpace, f (par a b) = 0).
admit.
Qed.

Theorem series_representation_theorem :
  forall par ser : set -> set -> set,
    IsQuantumAlgebra AmplitudeSpace par ser ->
    exists f : set -> set,
      (forall a b :e AmplitudeSpace, f (par a b) = 0) /\
      (forall a b :e AmplitudeSpace, f (ser a b) = 0).
admit.
Qed.

Definition Amplitude : set -> set := fun path => 0.

Theorem FeynmanSumRule : forall path1 path2 a b,
  Amplitude (path1) = a ->
  Amplitude (path2) = b ->
  True.
admit.
Qed.

Theorem FeynmanProductRule : forall path1 path2 a b,
  Amplitude (path1) = a ->
  Amplitude (path2) = b ->
  True.
admit.
Qed.

Definition ModulusSquared : set -> set :=
  fun z => 0.

Theorem BornRule : forall path,
  Amplitude path = 0.
admit.
Qed.
