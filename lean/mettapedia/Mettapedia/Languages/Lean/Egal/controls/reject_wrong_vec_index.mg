
(** Rejection control: cons lengthens the vector; it is not of the length of
    its tail. **)
Theorem wrong_vec_index : forall A, forall n :e Lean_Nat, forall x :e A, forall v :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec A n,
  Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec_cons_node A n x v :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec A n.
let A n. assume Hn: n :e Lean_Nat. let x. assume Hx: x :e A. let v. assume Hv: v :e Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec A n.
exact Lean_Mettapedia_Languages_Lean_Declarations_Controls_Vec_cons_typed A n Hn x Hx v Hv.
Qed.
