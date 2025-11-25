Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Axiom counterexample_R : set -> set -> prop.

Axiom counterexample_S5 : set.

Axiom counterexample_V13 : set.

Axiom counterexample_sym : forall x y, counterexample_R x y -> counterexample_R y x.

Axiom counterexample_tf : triangle_free 18 counterexample_R.

Axiom counterexample_no6 : no_k_indep 18 counterexample_R 6.

Axiom counterexample_S5_card : equip 5 counterexample_S5.

Axiom counterexample_V13_card : equip 13 counterexample_V13.

Axiom counterexample_S5_sub : counterexample_S5 c= 18.

Axiom counterexample_V13_sub : counterexample_V13 c= 18.

Axiom counterexample_S5_indep : is_indep_set 18 counterexample_R counterexample_S5.

Axiom counterexample_disjoint : forall x :e counterexample_S5, forall y :e counterexample_V13, x <> y.

Axiom counterexample_degree : forall v :e counterexample_S5,
  exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~counterexample_R v t) /\ v /:e T.

Axiom counterexample_coverage : forall w :e counterexample_V13, exists v :e counterexample_S5, counterexample_R v w.

Theorem intersection_nonempty_false :
  ~(forall R:set -> set -> prop,
    forall S5 V13:set,
    (forall x y, R x y -> R y x) ->
    triangle_free 18 R ->
    no_k_indep 18 R 6 ->
    equip 5 S5 ->
    equip 13 V13 ->
    S5 c= 18 ->
    V13 c= 18 ->
    is_indep_set 18 R S5 ->
    (forall x :e S5, forall y :e V13, x <> y) ->
    (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) ->
    exists w :e V13, forall v :e S5, ~R v w).
prove ~(forall R:set -> set -> prop,
         forall S5 V13:set,
         (forall x y, R x y -> R y x) ->
         triangle_free 18 R ->
         no_k_indep 18 R 6 ->
         equip 5 S5 ->
         equip 13 V13 ->
         S5 c= 18 ->
         V13 c= 18 ->
         is_indep_set 18 R S5 ->
         (forall x :e S5, forall y :e V13, x <> y) ->
         (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) ->
         exists w :e V13, forall v :e S5, ~R v w).
assume Hlemma: forall R:set -> set -> prop,
                forall S5 V13:set,
                (forall x y, R x y -> R y x) ->
                triangle_free 18 R ->
                no_k_indep 18 R 6 ->
                equip 5 S5 ->
                equip 13 V13 ->
                S5 c= 18 ->
                V13 c= 18 ->
                is_indep_set 18 R S5 ->
                (forall x :e S5, forall y :e V13, x <> y) ->
                (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) ->
                exists w :e V13, forall v :e S5, ~R v w.
prove False.
claim Hconclusion: exists w :e counterexample_V13, forall v :e counterexample_S5, ~counterexample_R v w.
  exact Hlemma counterexample_R counterexample_S5 counterexample_V13
        counterexample_sym counterexample_tf counterexample_no6
        counterexample_S5_card counterexample_V13_card
        counterexample_S5_sub counterexample_V13_sub
        counterexample_S5_indep counterexample_disjoint
        counterexample_degree.
apply Hconclusion.
let w.
assume Hw: w :e counterexample_V13 /\ (forall v :e counterexample_S5, ~counterexample_R v w).
claim HwV13: w :e counterexample_V13.
  exact andEL (w :e counterexample_V13) (forall v :e counterexample_S5, ~counterexample_R v w) Hw.
claim Hno_edges: forall v :e counterexample_S5, ~counterexample_R v w.
  exact andER (w :e counterexample_V13) (forall v :e counterexample_S5, ~counterexample_R v w) Hw.
claim Hex_neighbor: exists v :e counterexample_S5, counterexample_R v w.
  exact counterexample_coverage w HwV13.
apply Hex_neighbor.
let v.
assume Hv: v :e counterexample_S5 /\ counterexample_R v w.
claim HvS5: v :e counterexample_S5.
  exact andEL (v :e counterexample_S5) (counterexample_R v w) Hv.
claim HRvw: counterexample_R v w.
  exact andER (v :e counterexample_S5) (counterexample_R v w) Hv.
exact Hno_edges v HvS5 HRvw.
Qed.
