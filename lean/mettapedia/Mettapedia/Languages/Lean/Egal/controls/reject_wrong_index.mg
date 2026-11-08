
(** Rejection control: reflexivity proves Eq at its own index only. **)
Theorem wrong_index : 0 :e Lean_Eq_Prop omega 0 1.
exact Lean_Eq_refl_proof_ok omega 0.
Qed.
