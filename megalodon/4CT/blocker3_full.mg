Section BirkhoffDiamond_Full.

Variable E : set -> set -> prop.

Definition valid_coloring : (set -> set) -> prop :=
  fun col => forall x y : set, E x y -> col x <> col y.

Definition in_01_chain : (set -> set) -> set -> prop :=
  fun col v => col v = 0 \/ col v = 1.

Variable v0 : set.
Variable v1 : set.
Variable v2 : set.
Variable v3 : set.
Variable v4 : set.
Variable v5 : set.

Hypothesis edge_01 : E v0 v1.
Hypothesis edge_12 : E v1 v2.
Hypothesis edge_23 : E v2 v3.
Hypothesis edge_34 : E v3 v4.
Hypothesis edge_45 : E v4 v5.
Hypothesis edge_50 : E v5 v0.

Variable col : set -> set.

Hypothesis col_v0 : col v0 = 0.
Hypothesis col_v1 : col v1 = 1.
Hypothesis col_v2 : col v2 = 2.
Hypothesis col_v3 : col v3 = 3.
Hypothesis col_v4 : col v4 = 2.
Hypothesis col_v5 : col v5 = 3.

Theorem original_valid_01 : col v0 <> col v1.
rewrite col_v0. rewrite col_v1.
assume H: 0 = 1. apply neq_0_1. exact H.
Qed.

Theorem original_valid_12 : col v1 <> col v2.
rewrite col_v1. rewrite col_v2.
assume H: 1 = 2. apply neq_1_2. exact H.
Qed.

Theorem original_valid_23 : col v2 <> col v3.
rewrite col_v2. rewrite col_v3.
apply neq_i_sym. exact neq_3_2.
Qed.

Theorem original_valid_45 : col v4 <> col v5.
rewrite col_v4. rewrite col_v5.
apply neq_i_sym. exact neq_3_2.
Qed.

Theorem v0_in_01_chain : in_01_chain col v0.
prove col v0 = 0 \/ col v0 = 1.
apply orIL. exact col_v0.
Qed.

Theorem v1_in_01_chain : in_01_chain col v1.
prove col v1 = 0 \/ col v1 = 1.
apply orIR. exact col_v1.
Qed.

Theorem same_color_adjacent_invalid :
  forall col' : set -> set, forall x y : set,
    col' x = col' y -> E x y -> ~valid_coloring col'.
let col'. let x. let y.
assume Hsame: col' x = col' y.
assume Hedge: E x y.
assume Hvalid: valid_coloring col'.
prove False.
apply Hvalid x y Hedge.
exact Hsame.
Qed.

Theorem swap_01_both_1_invalid :
  forall col' : set -> set,
    col' v0 = 1 -> col' v1 = 1 -> ~valid_coloring col'.
let col'.
assume H0: col' v0 = 1.
assume H1: col' v1 = 1.
apply same_color_adjacent_invalid col' v0 v1.
- rewrite H0. rewrite H1. reflexivity.
- exact edge_01.
Qed.

Theorem kempe_chain_edge_constraint :
  (in_01_chain col v0 /\ in_01_chain col v1 /\ E v0 v1) /\
  (forall col' : set -> set, col' v0 = 1 -> col' v1 = 1 -> ~valid_coloring col').
apply andI.
- apply andI.
  + apply andI.
    * exact v0_in_01_chain.
    * exact v1_in_01_chain.
  + exact edge_01.
- exact swap_01_both_1_invalid.
Qed.

End BirkhoffDiamond_Full.
