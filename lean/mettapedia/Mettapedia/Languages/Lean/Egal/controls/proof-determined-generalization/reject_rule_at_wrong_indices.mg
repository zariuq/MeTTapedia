(** A wrong claim: the derivation built by the right annihilation at x = var 0,
    claimed at the left annihilation's indices there, mul 0 x -> 0.  It
    derives mul x 0 -> 0.  (At x = 0 both index pairs are mul 0 0 -> 0.)
    Both checkers must refuse it. **)
Theorem Lean_pdg_rule_at_wrong_indices :
    Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Deriv_mulZeroR_node
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_var_node (LeanNum 0))
  :e Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Deriv
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_node
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_var_node (LeanNum 0)))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)).
exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Deriv_mulZeroR_typed
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_var_node (LeanNum 0))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_var_typed (LeanNum 0) (LeanNum_In 0
    nat_0)).
Qed.
