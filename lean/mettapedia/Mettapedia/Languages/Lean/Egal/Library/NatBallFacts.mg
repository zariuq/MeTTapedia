(** Small facts for Lean's decision of a bounded quantifier (Nat.decidableBallLT). **)

Theorem LeanNat_add_one : forall n :e Lean_Nat, Lean_Nat_add n (LeanNum 1) = Lean_Nat_succ_node n.
let n. assume Hn: n :e Lean_Nat.
rewrite LeanNum_S 0 nat_0. rewrite LeanNum_0.
rewrite Lean_Nat_add_eq_2 n Hn Lean_Nat_zero_node Lean_Nat_zero_typed.
rewrite Lean_Nat_add_eq_1 n Hn.
reflexivity.
Qed.

Theorem LeanNat_not_below_zero : forall a :e Lean_Nat,
  0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node a) (LeanNum 0) -> False.
let a. assume Ha: a :e Lean_Nat. assume H: 0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node a) (LeanNum 0).
apply Lean_Nat_num a Ha. let j. assume Hj: nat_p j /\ a = LeanNum j.
apply Hj. assume Hj1: nat_p j. assume Hj2: a = LeanNum j.
claim L: 0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum j)) (LeanNum 0).
{ rewrite <- Hj2. exact H. }
exact EmptyE j (LeanNat_lt_In j Hj1 0 nat_0 L).
Qed.
