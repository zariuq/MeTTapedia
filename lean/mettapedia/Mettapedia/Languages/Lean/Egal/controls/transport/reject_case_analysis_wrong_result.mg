
(** Rejection control: a case analysis at a constant result lies in the type both of its minor
    premises give.  Here the successor case gives a value in C and the result is claimed in D. **)
Theorem case_analysis_wrong_result : forall C:set, forall D:set, forall h0 :e C, forall h1 :e (Pi_ x :e Lean_Nat, C),
  forall t :e Lean_Nat, Lean_Nat_casesOn h0 h1 t :e D.
let C D. let h0. assume H0: h0 :e C. let h1. assume H1: h1 :e (Pi_ x :e Lean_Nat, C). let t. assume Ht: t :e Lean_Nat.
exact Lean_Nat_casesOn_In C h0 H0 h1 H1 t Ht.
Qed.
