Definition IsPartialOrder : set -> (set -> set -> prop) -> prop :=
  fun E R =>
    (forall x :e E, R x x) /\
    (forall x y :e E, R x y -> R y x -> x = y) /\
    (forall x y z :e E, R x y -> R y z -> R x z).

Definition IsCausalSet : set -> (set -> set -> prop) -> prop :=
  fun E R => IsPartialOrder E R.

Definition IsChain : set -> (set -> set -> prop) -> set -> prop :=
  fun E R C => C c= E /\ (forall x y :e C, R x y \/ R y x).

Definition IsAntichain : set -> (set -> set -> prop) -> set -> prop :=
  fun E R A => A c= E /\ (forall x y :e A, R x y -> x = y).

Definition IsFreeParticle : set -> (set -> set -> prop) -> set -> prop :=
  fun E R P => IsChain E R P.

Definition SpacetimeInterval : set -> set -> set :=
  fun e1 e2 => 0.

Definition LightConeOrder : set -> set -> prop :=
  fun e1 e2 => SpacetimeInterval e1 e2 = 0.

Theorem causal_set_representation :
  forall E : set, forall R : set -> set -> prop,
    IsCausalSet E R ->
    exists f : set -> set,
      (forall e :e E, f e :e real)
      /\ (forall e1 e2 :e E, R e1 e2 <-> LightConeOrder (f e1) (f e2)).
admit.
Qed.
