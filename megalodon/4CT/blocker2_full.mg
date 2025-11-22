Section Blocker2_Full.

Variable E : set -> set -> prop.

Definition valid_coloring : (set -> set) -> prop :=
  fun col => forall x y : set, E x y -> col x <> col y.

Definition in_01_chain : (set -> set) -> set -> prop :=
  fun col v => col v = 0 \/ col v = 1.

Variable v0 : set.
Variable v1 : set.
Variable v2 : set.

Hypothesis v0_neq_v1 : v0 <> v1.
Hypothesis v0_neq_v2 : v0 <> v2.
Hypothesis v1_neq_v2 : v1 <> v2.

Hypothesis edge_01 : E v0 v1.
Hypothesis edge_12 : E v1 v2.
Hypothesis edge_02 : E v0 v2.

Variable col : set -> set.

Hypothesis col_v0 : col v0 = 0.
Hypothesis col_v1 : col v1 = 1.
Hypothesis col_v2 : col v2 = 2.

Theorem original_valid_01 : col v0 <> col v1.
rewrite col_v0. rewrite col_v1.
assume H: 0 = 1.
apply neq_0_1. exact H.
Qed.

Theorem original_valid_12 : col v1 <> col v2.
rewrite col_v1. rewrite col_v2.
assume H: 1 = 2.
apply neq_1_2. exact H.
Qed.

Theorem original_valid_02 : col v0 <> col v2.
rewrite col_v0. rewrite col_v2.
assume H: 0 = 2.
apply neq_0_2. exact H.
Qed.

Theorem v0_in_chain : in_01_chain col v0.
prove col v0 = 0 \/ col v0 = 1.
apply orIL.
exact col_v0.
Qed.

Theorem v1_in_chain : in_01_chain col v1.
prove col v1 = 0 \/ col v1 = 1.
apply orIR.
exact col_v1.
Qed.

Theorem swap_v0_v1_same :
  forall col' : set -> set,
    col' v0 = 1 -> col' v1 = 1 -> col' v0 = col' v1.
let col'.
assume H0: col' v0 = 1.
assume H1: col' v1 = 1.
rewrite H0. rewrite H1.
reflexivity.
Qed.

Theorem same_color_adjacent_invalid :
  forall col' : set -> set,
    col' v0 = col' v1 -> E v0 v1 -> ~valid_coloring col'.
let col'.
assume Hsame: col' v0 = col' v1.
assume Hedge: E v0 v1.
assume Hvalid: valid_coloring col'.
prove False.
apply Hvalid v0 v1 Hedge.
exact Hsame.
Qed.

Theorem partial_swap_invalidates :
  forall col' : set -> set,
    col' v0 = 1 -> col' v1 = 1 -> ~valid_coloring col'.
let col'.
assume H0: col' v0 = 1.
assume H1: col' v1 = 1.
apply same_color_adjacent_invalid col'.
- apply swap_v0_v1_same col' H0 H1.
- exact edge_01.
Qed.

Theorem chain_with_edge_blocks_partial_swap :
  (in_01_chain col v0 /\ in_01_chain col v1 /\ E v0 v1) /\
  (forall col' : set -> set, col' v0 = 1 -> col' v1 = 1 -> ~valid_coloring col').
apply andI.
- apply andI.
  + apply andI.
    * exact v0_in_chain.
    * exact v1_in_chain.
  + exact edge_01.
- exact partial_swap_invalidates.
Qed.

End Blocker2_Full.
