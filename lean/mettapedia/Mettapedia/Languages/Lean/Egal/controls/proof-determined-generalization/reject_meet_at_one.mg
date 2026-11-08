(** A wrong claim: the generalization the right-annihilation proof determines,
    instantiated at the literal 1, meets the example mul 0 0 -> 0.  It gives
    mul 1 0 -> 0 instead.  Both checkers must refuse it. **)
Theorem Lean_pdg_meet_at_one_wrong : Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_node
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0))
    Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 1))
  = Lean_Prod_mk_node Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm
    Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_node
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)).
claim HL: (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)) :e
    Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_typed (LeanNum 0) (LeanNum_In 0
    nat_0). }
claim HL1: (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 1)) :e
    Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_typed (LeanNum 1) (LeanNum_In 1
    nat_1). }
claim HM: (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_node
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0))) :e
    Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_typed
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)) HL
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)) HL. }
rewrite Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight_eq_1.
rewrite Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize_eq_1
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)) HL
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 1)) HL1
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_node
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0))
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0))) HM
    (Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node (LeanNum 0)) HL.
reflexivity.
Qed.
