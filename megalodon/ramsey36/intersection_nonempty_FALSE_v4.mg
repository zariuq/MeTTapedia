Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Axiom and10E : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10:prop, forall p:prop,
  (P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ P7 /\ P8 /\ P9 /\ P10) ->
  (P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P7 -> P8 -> P9 -> P10 -> p) -> p.

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
claim Hconj10: (forall x y, R x y -> R y x) /\
    (triangle_free 18 R /\
     no_k_indep 18 R 6 /\
     equip 5 S5 /\
     equip 13 V13 /\
     S5 c= 18 /\
     V13 c= 18 /\
     is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T)) /\
    (forall w :e V13, exists v :e S5, R v w).
  exact Hcounter.
claim Hsym: forall x y, R x y -> R y x.
  exact andEL (forall x y, R x y -> R y x) _ Hconj10.
claim Hconj9: (triangle_free 18 R /\
     no_k_indep 18 R 6 /\
     equip 5 S5 /\
     equip 13 V13 /\
     S5 c= 18 /\
     V13 c= 18 /\
     is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T)) /\
    (forall w :e V13, exists v :e S5, R v w).
  exact andER (forall x y, R x y -> R y x) _ Hconj10.
claim Hconj8: triangle_free 18 R /\
     no_k_indep 18 R 6 /\
     equip 5 S5 /\
     equip 13 V13 /\
     S5 c= 18 /\
     V13 c= 18 /\
     is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T).
  exact andEL _ (forall w :e V13, exists v :e S5, R v w) Hconj9.
claim Hcoverage: forall w :e V13, exists v :e S5, R v w.
  exact andER _ (forall w :e V13, exists v :e S5, R v w) Hconj9.
claim Htf: triangle_free 18 R.
  exact andEL (triangle_free 18 R) _ Hconj8.
claim Hconj7: no_k_indep 18 R 6 /\
     equip 5 S5 /\
     equip 13 V13 /\
     S5 c= 18 /\
     V13 c= 18 /\
     is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T).
  exact andER (triangle_free 18 R) _ Hconj8.
claim Hno6: no_k_indep 18 R 6.
  exact andEL (no_k_indep 18 R 6) _ Hconj7.
claim Hconj6: equip 5 S5 /\
     equip 13 V13 /\
     S5 c= 18 /\
     V13 c= 18 /\
     is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T).
  exact andER (no_k_indep 18 R 6) _ Hconj7.
claim HS5_card: equip 5 S5.
  exact andEL (equip 5 S5) _ Hconj6.
claim Hconj5: equip 13 V13 /\
     S5 c= 18 /\
     V13 c= 18 /\
     is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T).
  exact andER (equip 5 S5) _ Hconj6.
claim HV13_card: equip 13 V13.
  exact andEL (equip 13 V13) _ Hconj5.
claim Hconj4: S5 c= 18 /\
     V13 c= 18 /\
     is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T).
  exact andER (equip 13 V13) _ Hconj5.
claim HS5_sub: S5 c= 18.
  exact andEL (S5 c= 18) _ Hconj4.
claim Hconj3: V13 c= 18 /\
     is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T).
  exact andER (S5 c= 18) _ Hconj4.
claim HV13_sub: V13 c= 18.
  exact andEL (V13 c= 18) _ Hconj3.
claim Hconj2: is_indep_set 18 R S5 /\
     (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T).
  exact andER (V13 c= 18) _ Hconj3.
claim HS5_indep: is_indep_set 18 R S5.
  exact andEL (is_indep_set 18 R S5) _ Hconj2.
claim Hconj1: (forall x :e S5, forall y :e V13, x <> y) /\
     (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T).
  exact andER (is_indep_set 18 R S5) _ Hconj2.
claim Hdisjoint: forall x :e S5, forall y :e V13, x <> y.
  exact andEL (forall x :e S5, forall y :e V13, x <> y) _ Hconj1.
claim Hdegree: forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
  exact andER (forall x :e S5, forall y :e V13, x <> y) _ Hconj1.
claim Hconclusion: exists w :e V13, forall v :e S5, ~R v w.
  exact Hlemma R S5 V13 Hsym Htf Hno6 HS5_card HV13_card HS5_sub HV13_sub HS5_indep Hdisjoint Hdegree.
apply Hconclusion.
let w.
assume Hw: w :e V13 /\ (forall v :e S5, ~R v w).
claim HwV13: w :e V13.
  exact andEL (w :e V13) (forall v :e S5, ~R v w) Hw.
claim Hno_edges: forall v :e S5, ~R v w.
  exact andER (w :e V13) (forall v :e S5, ~R v w) Hw.
claim Hex_neighbor: exists v :e S5, R v w.
  exact Hcoverage w HwV13.
apply Hex_neighbor.
let v.
assume Hv: v :e S5 /\ R v w.
claim HvS5: v :e S5.
  exact andEL (v :e S5) (R v w) Hv.
claim HRvw: R v w.
  exact andER (v :e S5) (R v w) Hv.
exact Hno_edges v HvS5 HRvw.
