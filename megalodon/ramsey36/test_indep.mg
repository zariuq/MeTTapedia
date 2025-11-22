Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Theorem indep_witness_from_neg : forall V:set, forall R:set -> set -> prop, forall k:set,
  ~no_k_indep V R k ->
  exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
let V. let R: set -> set -> prop. let k.
assume Hnot: ~no_k_indep V R k.
prove exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
apply dneg (exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
assume Hcontra: ~(exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
apply Hnot.
prove no_k_indep V R k.
prove forall S, S c= V -> equip k S -> ~is_indep_set V R S.
let S. assume HSV: S c= V. assume HSeq: equip k S.
assume Hindep: is_indep_set V R S.
apply Hcontra.
witness S.
apply and3I (S c= V) (equip k S) (forall x :e S, forall y :e S, x <> y -> ~R x y).
- exact HSV.
- exact HSeq.
- prove forall x :e S, forall y :e S, x <> y -> ~R x y.
  exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~R x y) Hindep.
Qed.
