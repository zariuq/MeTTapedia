Section Blocker2.

Variable v0 : set.
Variable v1 : set.
Variable v2 : set.

Hypothesis v0_neq_v1 : v0 <> v1.
Hypothesis v0_neq_v2 : v0 <> v2.
Hypothesis v1_neq_v2 : v1 <> v2.

Variable col : set -> set.

Hypothesis col_v0 : col v0 = 0.
Hypothesis col_v1 : col v1 = 1.
Hypothesis col_v2 : col v2 = 0.

Definition in_01_chain : set -> prop :=
  fun v => col v = 0 \/ col v = 1.

Theorem v0_in_chain : in_01_chain v0.
prove col v0 = 0 \/ col v0 = 1.
apply orIL.
exact col_v0.
Qed.

Theorem v1_in_chain : in_01_chain v1.
prove col v1 = 0 \/ col v1 = 1.
apply orIR.
exact col_v1.
Qed.

Theorem v2_in_chain : in_01_chain v2.
prove col v2 = 0 \/ col v2 = 1.
apply orIL.
exact col_v2.
Qed.

Definition swap_01 : set -> set :=
  fun c => if c = 0 then 1 else if c = 1 then 0 else c.

Theorem swap_creates_same_color :
  forall col' : set -> set,
    col' v0 = 1 ->
    col' v2 = 1 ->
    col' v0 = col' v2.
let col'.
assume H0 : col' v0 = 1.
assume H2 : col' v2 = 1.
prove col' v0 = col' v2.
rewrite H0.
rewrite H2.
reflexivity.
Qed.

Theorem spanning_exists_but_swap_conflicts :
  (in_01_chain v0 /\ in_01_chain v1 /\ in_01_chain v2) /\
  (col v0 = 0 /\ col v2 = 0).
apply andI.
- apply andI.
  + apply andI.
    * exact v0_in_chain.
    * exact v1_in_chain.
  + exact v2_in_chain.
- apply andI.
  + exact col_v0.
  + exact col_v2.
Qed.

End Blocker2.
