(** Divisibility is characterized by remainder zero, not remainder one. **)
Theorem reject_wrong_divisibility : forall d n :e Lean_Nat,
  0 :e Lean_Iff_Prop (Lean_Eq_Prop Lean_Nat (Lean_Nat_mod n d) (LeanNum 1)) (LeanNatDivides d n).
let d. assume Hd: d :e Lean_Nat. let n. assume Hn: n :e Lean_Nat.
exact Lean_mod_divisibility_iff d Hd n Hn.
Qed.
