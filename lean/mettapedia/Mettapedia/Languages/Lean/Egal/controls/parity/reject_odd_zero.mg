(** A wrong claim: Odd 0, offered the proof of Even 0.  Both checkers must refuse it. **)
Theorem Lean_parity_odd_zero_wrong : 0 :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Odd_Prop (LeanNum 0).
rewrite LeanNum_0.
exact Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_zero_b_proof_ok.
Qed.
