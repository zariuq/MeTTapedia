(** Lean's equation is proved for Lean's recipe only: Nat.minFacAux does not
    satisfy the equation whose recursive call is at x + 1. **)
Theorem reject_changed_recipe : forall v_n :e Lean_Nat, forall v_x :e Lean_Nat,
  (Lean_Nat_minFacAux v_n v_x) = (Lean_ite Lean_Nat (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n) (Lean_Nat_mul v_x v_x))
    (Lean_Nat_decLt v_n (Lean_Nat_mul v_x v_x)) v_n
    (Lean_ite Lean_Nat (Lean_Exists_Prop Lean_Nat (fun v_c :e Lean_Nat => (Lean_Eq_Prop Lean_Nat v_n (Lean_Nat_mul v_x v_c))))
      (Lean_Nat_decidable_dvd v_x v_n) v_x (Lean_Nat_minFacAux v_n (Lean_Nat_add v_x (LeanNum 1))))).
exact LeanMinFacAux_equation.
Qed.
