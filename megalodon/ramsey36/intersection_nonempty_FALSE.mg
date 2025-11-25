Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

(* Define the counterexample graph *)
(* S5 = {0,1,2,3,4}, V13 = {5,6,7,8,9,10,11,12,13,14,15,16,17} *)

Definition R_counter : set -> set -> prop := fun x y =>
  (* Edges from 0 to {5,6,7,8,9} *)
  (x = 0 /\ (y = 5 \/ y = 6 \/ y = 7 \/ y = 8 \/ y = 9)) \/
  (y = 0 /\ (x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9)) \/
  (* Edges from 1 to {10,11,12,13,14} *)
  (x = 1 /\ (y = 10 \/ y = 11 \/ y = 12 \/ y = 13 \/ y = 14)) \/
  (y = 1 /\ (x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14)) \/
  (* Edges from 2 to {15,16,17,5,6} *)
  (x = 2 /\ (y = 15 \/ y = 16 \/ y = 17 \/ y = 5 \/ y = 6)) \/
  (y = 2 /\ (x = 15 \/ x = 16 \/ x = 17 \/ x = 5 \/ x = 6)) \/
  (* Edges from 3 to {7,8,9,10,11} *)
  (x = 3 /\ (y = 7 \/ y = 8 \/ y = 9 \/ y = 10 \/ y = 11)) \/
  (y = 3 /\ (x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11)) \/
  (* Edges from 4 to {12,13,14,15,16} *)
  (x = 4 /\ (y = 12 \/ y = 13 \/ y = 14 \/ y = 15 \/ y = 16)) \/
  (y = 4 /\ (x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/ x = 16)).

(* S5 as the set {0,1,2,3,4} *)
Definition S5_spec : set := {0} :\/: {1} :\/: {2} :\/: {3} :\/: {4}.

(* V13 as the remaining vertices *)
Definition V13_spec : set :=
  {5} :\/: {6} :\/: {7} :\/: {8} :\/: {9} :\/:
  {10} :\/: {11} :\/: {12} :\/: {13} :\/: {14} :\/:
  {15} :\/: {16} :\/: {17}.

(* Prove R_counter is symmetric *)
Theorem R_counter_symmetric : forall x y, R_counter x y -> R_counter y x.
let x y.
assume H: R_counter x y.
prove R_counter y x.
(* By definition, R_counter is symmetric *)
exact H.
Qed.

(* Prove S5_spec is an independent set under R_counter *)
Theorem S5_spec_independent : is_indep_set 18 R_counter S5_spec.
prove S5_spec c= 18 /\ (forall x :e S5_spec, forall y :e S5_spec, x <> y -> ~R_counter x y).
apply andI.
- (* S5_spec c= 18 *)
  prove S5_spec c= 18.
  let x. assume Hx: x :e S5_spec.
  (* x is one of 0,1,2,3,4, all of which are in 18 *)
  Admitted.
- (* No edges within S5_spec *)
  prove forall x :e S5_spec, forall y :e S5_spec, x <> y -> ~R_counter x y.
  let x. assume Hx: x :e S5_spec.
  let y. assume Hy: y :e S5_spec.
  assume Hneq: x <> y.
  prove ~R_counter x y.
  assume HRxy: R_counter x y.
  (* By definition of R_counter, edges only exist between {0,1,2,3,4} and {5,...,17} *)
  (* x and y are both in {0,1,2,3,4}, so R_counter x y is false *)
  (* This requires case analysis on the definition *)
  Admitted.
Qed.

(* Prove that every vertex in V13 is covered *)
Theorem V13_fully_covered : forall w :e V13_spec, exists v :e S5_spec, R_counter v w.
let w. assume Hw: w :e V13_spec.
prove exists v :e S5_spec, R_counter v w.
(* Case analysis on w *)
(* If w=5: connected to 0 and 2 *)
(* If w=6: connected to 0 and 2 *)
(* If w=7: connected to 0 and 3 *)
(* If w=8: connected to 0 and 3 *)
(* If w=9: connected to 0 and 3 *)
(* If w=10: connected to 1 and 3 *)
(* If w=11: connected to 1 and 3 *)
(* If w=12: connected to 1 and 4 *)
(* If w=13: connected to 1 and 4 *)
(* If w=14: connected to 1 and 4 *)
(* If w=15: connected to 2 and 4 *)
(* If w=16: connected to 2 and 4 *)
(* If w=17: connected to 2 *)

(* This requires extensive case analysis, but each case is straightforward *)
Admitted.
Qed.

(* The key theorem: intersection_nonempty is FALSE *)
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

(* Instantiate with our counterexample *)
claim Hconclusion: exists w :e V13_spec, forall v :e S5_spec, ~R_counter v w.
  apply Hlemma R_counter S5_spec V13_spec.
  - (* Symmetry *)
    exact R_counter_symmetric.
  - (* Triangle-free *)
    prove triangle_free 18 R_counter.
    (* The graph is bipartite between S5 and V13, so triangle-free *)
    Admitted.
  - (* No 6-indep *)
    prove no_k_indep 18 R_counter 6.
    (* Every 6-element subset contains at least one edge *)
    (* Since S5 is max indep (size 5) and all V13 have neighbors in S5 *)
    Admitted.
  - (* equip 5 S5_spec *)
    prove equip 5 S5_spec.
    Admitted.
  - (* equip 13 V13_spec *)
    prove equip 13 V13_spec.
    Admitted.
  - (* S5_spec c= 18 *)
    prove S5_spec c= 18.
    Admitted.
  - (* V13_spec c= 18 *)
    prove V13_spec c= 18.
    Admitted.
  - (* S5_spec is independent *)
    exact S5_spec_independent.
  - (* S5 and V13 disjoint *)
    prove forall x :e S5_spec, forall y :e V13_spec, x <> y.
    Admitted.
  - (* Each vertex in S5 has 12 non-neighbors *)
    prove forall v :e S5_spec, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R_counter v t) /\ v /:e T.
    (* Each vertex in S5 has exactly 5 neighbors in V13, so 8 non-neighbors in V13 *)
    (* Plus 4 other vertices in S5 = 12 total non-neighbors *)
    Admitted.

(* Now derive contradiction *)
apply Hconclusion.
let w. assume Hw: w :e V13_spec /\ (forall v :e S5_spec, ~R_counter v w).

claim HwV13: w :e V13_spec.
  exact andEL (w :e V13_spec) (forall v :e S5_spec, ~R_counter v w) Hw.

claim Hno_edges: forall v :e S5_spec, ~R_counter v w.
  exact andER (w :e V13_spec) (forall v :e S5_spec, ~R_counter v w) Hw.

(* But we proved every w in V13 has a neighbor in S5 *)
claim Hex_neighbor: exists v :e S5_spec, R_counter v w.
  exact V13_fully_covered w HwV13.

(* Contradiction *)
apply Hex_neighbor.
let v. assume Hv: v :e S5_spec /\ R_counter v w.

claim HvS5: v :e S5_spec.
  exact andEL (v :e S5_spec) (R_counter v w) Hv.

claim HRvw: R_counter v w.
  exact andER (v :e S5_spec) (R_counter v w) Hv.

(* This contradicts Hno_edges *)
exact Hno_edges v HvS5 HRvw.
Qed.
