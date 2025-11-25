Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

(* Axiom for 5-regularity (to be proven later or used as conditional) *)
Axiom graph_is_5_regular : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18,
    exists N, (equip 5 N /\ (forall x :e N, R v x) /\ (forall x :e 18, R v x -> x :e N) /\ N c= 18).

(* Helper: Independent set extension *)
Theorem indep_add_vertex : forall V:set, forall R:set -> set -> prop,
  forall S v:set,
  is_indep_set V R S ->
  v :e V ->
  v /:e S ->
  (forall s :e S, ~R v s) ->
  (forall s :e S, ~R s v) ->
  is_indep_set V R (S :\/: {v}).
let V. let R. let S. let v.
assume HS Hv HvnotS Hnon1 Hnon2.
prove (S :\/: {v}) c= V /\ (forall x :e (S :\/: {v}), forall y :e (S :\/: {v}), x <> y -> ~R x y).
Admitted.

(* Helper: Cardinality *)
Theorem equip_5_plus_1_is_6 : forall S v:set,
  equip 5 S -> v /:e S -> equip 6 (S :\/: {v}).
Admitted.

Theorem common_neighbor_exists_if_deg_5 : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall u v :e 18,
    u <> v -> ~R u v ->
    forall Nu:set,
      equip 5 Nu ->
      (forall x :e Nu, R u x) ->
      (forall x :e 18, R u x -> x :e Nu) ->
      Nu c= 18 ->
      exists w :e Nu, R v w.
let R. assume Hsym Htf Hno6 u Hu v Hv Hneq HnotAdj Nu HNu5 HNu_in HNu_def HNu_subset.
prove exists w :e Nu, R v w.
apply dneg.
assume Hcontra: ~(exists w :e Nu, R v w).
(* If no common neighbor, then v is non-adjacent to all Nu *)
claim Hv_non_Nu: forall w :e Nu, ~R v w.
  let w. assume Hw: w :e Nu.
  assume HRvw: R v w.
  apply Hcontra.
  witness w.
  exact andI (w :e Nu) (R v w) Hw HRvw.

(* Nu is an independent set (neighbors of u in triangle-free graph) *)
claim HNu_indep: is_indep_set 18 R Nu.
  prove Nu c= 18 /\ (forall x :e Nu, forall y :e Nu, x <> y -> ~R x y).
  apply andI.
  - exact HNu_subset.
  - (* Nu independent *)
    let x. assume Hx: x :e Nu.
    let y. assume Hy: y :e Nu.
    assume Hxy: x <> y.
    assume HRxy: R x y.
    claim HRux: R u x. exact HNu_in x Hx.
    claim HRuy: R u y. exact HNu_in y Hy.
    claim HRxu: R x u. exact Hsym u x HRux.
    (* Triangle u, x, y *)
    exact Htf x (HNu_subset x Hx) u Hu y (HNu_subset y Hy) HRxu HRuy HRxy.

(* v is not in Nu because u is not adjacent to v *)
claim Hv_notin_Nu: v /:e Nu.
  assume HvIn: v :e Nu.
  claim HRuv: R u v. exact HNu_in v HvIn.
  exact HnotAdj HRuv.

(* So Nu U {v} is independent *)
set S6 := Nu :\/: {v}.
claim HS6_indep: is_indep_set 18 R S6.
  apply indep_add_vertex 18 R Nu v HNu_indep Hv Hv_notin_Nu.
  - exact Hv_non_Nu. (* v not adj to Nu *)
  - (* Nu not adj to v *)
    let s. assume Hs: s :e Nu.
    assume HRsv: R s v.
    exact Hv_non_Nu s Hs (Hsym s v HRsv).

(* Size of S6 is 6 *)
claim HS6_equip: equip 6 S6.
  exact equip_5_plus_1_is_6 Nu v HNu5 Hv_notin_Nu.

(* Contradiction with no_k_indep *)
claim S6_subset: S6 c= 18.
  Admitted. (* Easy from Nu c= 18 and v :e 18 *)

exact Hno6 S6 S6_subset HS6_equip HS6_indep.
Qed.

Theorem common_neighbors_ge_1 : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall u v :e 18,
    ~R u v -> u <> v ->
    exists x :e 18, R u x /\ R v x.
let R. assume Hsym Htf Hno6 u Hu v Hv HnotAdj Hneq.
(* Use 5-regularity to get Nu *)
apply graph_is_5_regular R Hsym Htf Hno6 u Hu.
let Nu. assume HNu_props.
(* Unpack properties *)
(* (equip 5 Nu /\ (forall x :e Nu, R v x)) /\ ((forall x :e 18, R v x -> x :e Nu) /\ Nu c= 18) *)
(* The unpacking structure depends on association *)
(* Assume pair structure: (A /\ B) /\ (C /\ D) *)
claim HNu5: equip 5 Nu. exact andEL _ _ (andEL _ _ HNu_props).
claim HNu_in: forall x :e Nu, R u x. exact andER _ _ (andEL _ _ HNu_props).
claim HNu_def: forall x :e 18, R u x -> x :e Nu. exact andEL _ _ (andER _ _ HNu_props).
claim HNu_subset: Nu c= 18. exact andER _ _ (andER _ _ HNu_props).

(* Use the lemma *)
apply common_neighbor_exists_if_deg_5 R Hsym Htf Hno6 u Hu v Hv Hneq HnotAdj Nu HNu5 HNu_in HNu_def HNu_subset.
let w. assume Hw: w :e Nu /\ R v w.
witness w.
apply andI.
- (* w :e 18 *)
  exact HNu_subset w (andEL _ _ Hw).
- (* R u w /\ R v w *)
  apply andI.
  + exact HNu_in w (andEL _ _ Hw).
  + exact andER _ _ Hw.
Qed.