(** 1 is not a value of Fin 1: its guard 1 < 1 is Nat.le 2 1, and refl
    proves Nat.le 2 2, not Nat.le 2 1. **)
Theorem reject_fin_out_of_range :
  0 :e Lean_Nat_le_Prop (Lean_Nat_succ_node (Lean_Nat_succ_node Lean_Nat_zero_node)) (Lean_Nat_succ_node Lean_Nat_zero_node).
exact Lean_Nat_le_refl_proof_ok (Lean_Nat_succ_node (Lean_Nat_succ_node Lean_Nat_zero_node)).
Qed.
