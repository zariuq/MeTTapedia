Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Axiom counterexample_exists :
  exists R:set -> set -> prop, exists S5:set, exists V13:set,
    (forall x y, R x y -> R y x) /\
    triangle_free 18 R /\
    no_k_indep 18 R 6 /\
    equip 5 S5 /\
    equip 13 V13 /\
    S5 c= 18 /\
    V13 c= 18 /\
    is_indep_set 18 R S5 /\
    (forall x :e S5, forall y :e V13, x <> y) /\
    (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) /\
    (forall w :e V13, exists v :e S5, R v w).

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
apply counterexample_exists.
let R.
assume HexS5V13: exists S5:set, exists V13:set,
    (forall x y, R x y -> R y x) /\
    triangle_free 18 R /\
    no_k_indep 18 R 6 /\
    equip 5 S5 /\
    equip 13 V13 /\
    S5 c= 18 /\
    V13 c= 18 /\
    is_indep_set 18 R S5 /\
    (forall x :e S5, forall y :e V13, x <> y) /\
    (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) /\
    (forall w :e V13, exists v :e S5, R v w).
apply HexS5V13.
let S5.
assume HexV13: exists V13:set,
    (forall x y, R x y -> R y x) /\
    triangle_free 18 R /\
    no_k_indep 18 R 6 /\
    equip 5 S5 /\
    equip 13 V13 /\
    S5 c= 18 /\
    V13 c= 18 /\
    is_indep_set 18 R S5 /\
    (forall x :e S5, forall y :e V13, x <> y) /\
    (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) /\
    (forall w :e V13, exists v :e S5, R v w).
apply HexV13.
let V13.
assume Hcounter: (forall x y, R x y -> R y x) /\
    triangle_free 18 R /\
    no_k_indep 18 R 6 /\
    equip 5 S5 /\
    equip 13 V13 /\
    S5 c= 18 /\
    V13 c= 18 /\
    is_indep_set 18 R S5 /\
    (forall x :e S5, forall y :e V13, x <> y) /\
    (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) /\
    (forall w :e V13, exists v :e S5, R v w).
prove False.
claim Hsym: forall x y, R x y -> R y x.
  Admitted.
claim Htf: triangle_free 18 R.
  Admitted.
claim Hno6: no_k_indep 18 R 6.
  Admitted.
claim HS5_card: equip 5 S5.
  Admitted.
claim HV13_card: equip 13 V13.
  Admitted.
claim HS5_sub: S5 c= 18.
  Admitted.
claim HV13_sub: V13 c= 18.
  Admitted.
claim HS5_indep: is_indep_set 18 R S5.
  Admitted.
claim Hdisjoint: forall x :e S5, forall y :e V13, x <> y.
  Admitted.
claim Hdegree: forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
  Admitted.
claim Hcoverage: forall w :e V13, exists v :e S5, R v w.
  Admitted.
claim Hconclusion: exists w :e V13, forall v :e S5, ~R v w.
  exact Hlemma R S5 V13 Hsym Htf Hno6 HS5_card HV13_card HS5_sub HV13_sub HS5_indep Hdisjoint Hdegree.
apply Hconclusion.
let w.
assume Hw: w :e V13 /\ (forall v :e S5, ~R v w).
claim HwV13: w :e V13.
  Admitted.
claim Hno_edges: forall v :e S5, ~R v w.
  Admitted.
claim Hex_neighbor: exists v :e S5, R v w.
  exact Hcoverage w HwV13.
apply Hex_neighbor.
let v.
assume Hv: v :e S5 /\ R v w.
claim HvS5: v :e S5.
  Admitted.
claim HRvw: R v w.
  Admitted.
exact Hno_edges v HvS5 HRvw.
