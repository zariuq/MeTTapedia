(** Even and Odd, a mutual pair of propositions, read from Lean into Egal.

    Lean declares them together: Even 0; Even (n+1) from Odd n; Odd (n+1)
    from Even n.  The reading is one family indexed by a member code and the
    number (Even at code 1, Odd at code 2), with each member its own view.
    Lean's theorem odd_zero_false (Odd 0 is impossible) is proved in Egal from
    its generated statement.  Here: 2 is even, built from the constructors. **)

Theorem Ex_even_two : 0 :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_Prop (LeanNum 2).
claim Z: LeanNum 0 :e Lean_Nat.
{ exact LeanNum_In 0 nat_0. }
claim E0: Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_zero_b_node :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_b (setsum 1 (LeanNum 0)).
{ exact Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_zero_b_typed. }
claim O1: Lean_Mettapedia_Languages_Lean_Declarations_Controls_Odd_succ_b_node (LeanNum 0) Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_zero_b_node
  :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_b (setsum 2 (LeanNum 1)).
{ rewrite LeanNum_S 0 nat_0. exact Lean_Mettapedia_Languages_Lean_Declarations_Controls_Odd_succ_b_typed (LeanNum 0) Z Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_zero_b_node E0. }
claim E2: 0 :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_b_PropPacked (setsum 1 (Lean_Nat_succ_node (LeanNum 1))).
{ exact Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_succ_b_proof_ok (LeanNum 1) (LeanNum_In 1 (nat_ordsucc 0 nat_0))
    (Lean_Mettapedia_Languages_Lean_Declarations_Controls_Odd_succ_b_node (LeanNum 0) Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_zero_b_node) O1. }
prove 0 :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Even_b_PropPacked (setsum 1 (LeanNum 2)).
rewrite LeanNum_S 1 (nat_ordsucc 0 nat_0). exact E2.
Qed.
