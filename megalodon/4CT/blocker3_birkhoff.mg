Definition F22_color : set -> prop :=
  fun c => c = 0 \/ c = 1 \/ c = 2 \/ c = 3.

Definition valid_edge_coloring : set -> set -> prop :=
  fun c1 c2 => c1 <> c2.

Section BirkhoffDiamond.

Variable v0 : set.
Variable v1 : set.
Variable v2 : set.
Variable v3 : set.
Variable v4 : set.
Variable v5 : set.

Hypothesis all_distinct : v0 <> v1 /\ v0 <> v2 /\ v0 <> v3 /\ v0 <> v4 /\ v0 <> v5 /\
                          v1 <> v2 /\ v1 <> v3 /\ v1 <> v4 /\ v1 <> v5 /\
                          v2 <> v3 /\ v2 <> v4 /\ v2 <> v5 /\
                          v3 <> v4 /\ v3 <> v5 /\
                          v4 <> v5.

Variable col : set -> set.

Hypothesis col_v0 : col v0 = 0.
Hypothesis col_v1 : col v1 = 1.
Hypothesis col_v2 : col v2 = 2.
Hypothesis col_v3 : col v3 = 3.
Hypothesis col_v4 : col v4 = 0.
Hypothesis col_v5 : col v5 = 1.

Hypothesis edge_01 : valid_edge_coloring (col v0) (col v1).
Hypothesis edge_12 : valid_edge_coloring (col v1) (col v2).
Hypothesis edge_23 : valid_edge_coloring (col v2) (col v3).
Hypothesis edge_34 : valid_edge_coloring (col v3) (col v4).
Hypothesis edge_45 : valid_edge_coloring (col v4) (col v5).
Hypothesis edge_50 : valid_edge_coloring (col v5) (col v0).

Definition kempe_chain_01 : set -> prop :=
  fun v => (col v = 0 \/ col v = 1).

Theorem v0_in_chain_01 : kempe_chain_01 v0.
prove col v0 = 0 \/ col v0 = 1.
apply orIL.
exact col_v0.
Qed.

Theorem v1_in_chain_01 : kempe_chain_01 v1.
prove col v1 = 0 \/ col v1 = 1.
apply orIR.
exact col_v1.
Qed.

Theorem v4_in_chain_01 : kempe_chain_01 v4.
prove col v4 = 0 \/ col v4 = 1.
apply orIL.
exact col_v4.
Qed.

Theorem v5_in_chain_01 : kempe_chain_01 v5.
prove col v5 = 0 \/ col v5 = 1.
apply orIR.
exact col_v5.
Qed.

Definition kempe_chain_23 : set -> prop :=
  fun v => (col v = 2 \/ col v = 3).

Theorem v2_in_chain_23 : kempe_chain_23 v2.
prove col v2 = 2 \/ col v2 = 3.
apply orIL.
exact col_v2.
Qed.

Theorem v3_in_chain_23 : kempe_chain_23 v3.
prove col v3 = 2 \/ col v3 = 3.
apply orIR.
exact col_v3.
Qed.

Theorem swap_creates_conflict :
  forall col' : set -> set,
    col' v0 = 1 ->
    col' v1 = 0 ->
    col' v4 = 1 ->
    col' v5 = 0 ->
    col' v0 = col' v4.
let col'.
assume H0: col' v0 = 1.
assume H1: col' v1 = 0.
assume H4: col' v4 = 1.
assume H5: col' v5 = 0.
prove col' v0 = col' v4.
rewrite H0.
rewrite H4.
reflexivity.
Qed.

End BirkhoffDiamond.
