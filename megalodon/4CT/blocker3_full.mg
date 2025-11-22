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
Hypothesis edge_04 : E v0 v4.

Variable col : set -> set.

Hypothesis col_v0 : col v0 = 0.
Hypothesis col_v1 : col v1 = 1.
Hypothesis col_v2 : col v2 = 2.
Hypothesis col_v3 : col v3 = 3.
Hypothesis col_v4 : col v4 = 0.
Hypothesis col_v5 : col v5 = 1.

Theorem v0_in_01_chain : in_01_chain col v0.
prove col v0 = 0 \/ col v0 = 1.
apply orIL.
exact col_v0.
Qed.

Theorem v1_in_01_chain : in_01_chain col v1.
prove col v1 = 0 \/ col v1 = 1.
apply orIR.
exact col_v1.
Qed.

Theorem v4_in_01_chain : in_01_chain col v4.
prove col v4 = 0 \/ col v4 = 1.
apply orIL.
exact col_v4.
Qed.

Theorem v5_in_01_chain : in_01_chain col v5.
prove col v5 = 0 \/ col v5 = 1.
apply orIR.
exact col_v5.
Qed.

Theorem original_v0_v4_same : col v0 = col v4.
rewrite col_v0.
rewrite col_v4.
reflexivity.
Qed.

Theorem original_valid_01 : col v0 <> col v1.
rewrite col_v0.
rewrite col_v1.
assume H: 0 = 1.
apply neq_0_1.
exact H.
Qed.

Theorem swap_makes_both_1 :
  forall col' : set -> set,
    col' v0 = 1 -> col' v4 = 1 -> col' v0 = col' v4.
let col'.
assume H0: col' v0 = 1.
assume H4: col' v4 = 1.
rewrite H0.
rewrite H4.
reflexivity.
Qed.

Theorem same_color_adjacent_invalid :
  forall col' : set -> set,
    col' v0 = col' v4 -> E v0 v4 -> ~valid_coloring col'.
let col'.
assume Hsame: col' v0 = col' v4.
assume Hedge: E v0 v4.
assume Hvalid: valid_coloring col'.
prove False.
apply Hvalid v0 v4 Hedge.
exact Hsame.
Qed.

Theorem swap_01_chain_invalidates :
  forall col' : set -> set,
    col' v0 = 1 -> col' v4 = 1 -> ~valid_coloring col'.
let col'.
assume H0: col' v0 = 1.
assume H4: col' v4 = 1.
apply same_color_adjacent_invalid col'.
- apply swap_makes_both_1 col' H0 H4.
- exact edge_04.
Qed.

Theorem birkhoff_kempe_locking :
  (in_01_chain col v0 /\ in_01_chain col v4 /\ E v0 v4) /\
  (forall col' : set -> set, col' v0 = 1 -> col' v4 = 1 -> ~valid_coloring col').
apply andI.
- apply andI.
  + apply andI.
    * exact v0_in_01_chain.
    * exact v4_in_01_chain.
  + exact edge_04.
- exact swap_01_chain_invalidates.
Qed.

End BirkhoffDiamond_Full.
