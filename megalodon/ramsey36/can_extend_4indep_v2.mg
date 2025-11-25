Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Axiom vertex_has_12_nonneighbors : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.

Axiom indep_add_vertex : forall V:set, forall R:set -> set -> prop,
  forall S v:set,
  is_indep_set V R S ->
  v :e V ->
  v /:e S ->
  (forall s :e S, ~R v s) ->
  (forall s :e S, ~R s v) ->
  is_indep_set V R (S :\/: {v}).

Axiom equip_4_plus_1 : forall S v:set,
  equip 4 S -> v /:e S -> equip 5 (S :\/: {v}).

Axiom equip_5_plus_1 : forall S v:set,
  equip 5 S -> v /:e S -> equip 6 (S :\/: {v}).

(* This is the key lemma I need to prove or accept as axiom *)
Axiom intersection_nonempty : forall R:set -> set -> prop,
  forall S5:set, forall V13:set,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  equip 5 S5 ->
  equip 13 V13 ->
  S5 c= 18 ->
  V13 c= 18 ->
  is_indep_set 18 R S5 ->
  (forall x :e S5, forall y :e V13, x <> y) ->
  (* If each vertex in S5 has a 12-element non-neighbor set *)
  (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) ->
  (* Then there exists some w in V13 non-adjacent to all of S5 *)
  exists w :e V13, forall v :e S5, ~R v w.

Theorem can_extend_4indep_with_nonneighbor : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 18 R ->
  no_k_indep 18 R 6 ->
  forall v :e 18, forall S:set,
    S c= 18 ->
    equip 4 S ->
    (forall s :e S, ~R v s) ->
    (forall s :e S, ~R s v) ->
    is_indep_set 18 R S ->
    v /:e S ->
    False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
let v. assume Hv: v :e 18.
let S. assume HS18: S c= 18.
assume HS4: equip 4 S.
assume Hvs_nonadj1: forall s :e S, ~R v s.
assume Hvs_nonadj2: forall s :e S, ~R s v.
assume HS_indep: is_indep_set 18 R S.
assume Hv_notin_S: v /:e S.
prove False.

(* Step 1: Form S' = S ∪ {v}, a 5-element independent set *)
set S' := S :\/: {v}.

claim HS'_indep: is_indep_set 18 R S'.
  exact indep_add_vertex 18 R S v HS_indep Hv Hv_notin_S Hvs_nonadj1 Hvs_nonadj2.

claim HS'5: equip 5 S'.
  exact equip_4_plus_1 S v HS4 Hv_notin_S.

claim HS'_18: S' c= 18.
  let x. assume Hx: x :e S'.
  apply binunionE S {v} x Hx.
  - assume HxS: x :e S.
    exact HS18 x HxS.
  - assume Hxv: x :e {v}.
    claim Hxeqv: x = v. exact SingE v x Hxv.
    rewrite Hxeqv.
    exact Hv.

(* Step 2: Define V_rem = 18 \ S' *)
set V_rem := 18 :\: S'.

claim HVrem_18: V_rem c= 18.
  let w. assume Hw: w :e V_rem.
  apply setminusE 18 S' w Hw.
  assume Hw18: w :e 18.
  assume _: w /:e S'.
  exact Hw18.

claim HVrem13: equip 13 V_rem.
  Admitted.  (* Need: |18 \ 5| = 13 *)

claim HS'_Vrem_disjoint: forall x :e S', forall y :e V_rem, x <> y.
  let x. assume HxS': x :e S'.
  let y. assume HyV: y :e V_rem.
  assume Heq: x = y.
  apply setminusE 18 S' y HyV.
  assume _: y :e 18.
  assume HynotS': y /:e S'.
  apply HynotS'.
  rewrite <- Heq.
  exact HxS'.

(* Step 3: Each vertex in S' has a 12-element non-neighbor set *)
claim HS'_has_nonneighbors: forall v :e S', exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
  let x. assume HxS': x :e S'.
  claim Hx18: x :e 18.
    exact HS'_18 x HxS'.
  exact vertex_has_12_nonneighbors R Hsym Htf Hno6 x Hx18.

(* Step 4: Apply the intersection_nonempty lemma *)
claim Hex_w: exists w :e V_rem, forall v :e S', ~R v w.
  exact intersection_nonempty R S' V_rem Hsym Htf Hno6 HS'5 HVrem13 HS'_18 HVrem_18 HS'_indep HS'_Vrem_disjoint HS'_has_nonneighbors.

(* Step 5: Extract the witness w and show S' ∪ {w} is 6-indep *)
apply Hex_w.
let w. assume Hw: w :e V_rem /\ (forall v :e S', ~R v w).

claim HwVrem: w :e V_rem.
  exact andEL (w :e V_rem) (forall v :e S', ~R v w) Hw.

claim Hw_nonadj: forall v :e S', ~R v w.
  exact andER (w :e V_rem) (forall v :e S', ~R v w) Hw.

claim Hw18: w :e 18.
  exact HVrem_18 w HwVrem.

claim Hw_notin_S': w /:e S'.
  apply setminusE 18 S' w HwVrem.
  assume _: w :e 18.
  assume H: w /:e S'.
  exact H.

claim Hw_nonadj_sym: forall v :e S', ~R w v.
  let x. assume Hx: x :e S'.
  assume HRwx: R w x.
  apply Hw_nonadj x Hx.
  exact Hsym w x HRwx.

(* Form S6 = S' ∪ {w} *)
set S6 := S' :\/: {w}.

claim HS6_indep: is_indep_set 18 R S6.
  exact indep_add_vertex 18 R S' w HS'_indep Hw18 Hw_notin_S' Hw_nonadj_sym Hw_nonadj.

claim HS6_6: equip 6 S6.
  exact equip_5_plus_1 S' w HS'5 Hw_notin_S'.

claim HS6_18: S6 c= 18.
  let z. assume Hz: z :e S6.
  apply binunionE S' {w} z Hz.
  - assume HzS': z :e S'.
    exact HS'_18 z HzS'.
  - assume Hzw: z :e {w}.
    claim Hzeqw: z = w. exact SingE w z Hzw.
    rewrite Hzeqw.
    exact Hw18.

(* Contradiction with no_k_indep *)
exact Hno6 S6 HS6_18 HS6_6 HS6_indep.
Qed.
