(** The zero proof value must still establish the operation's law. **)
Theorem reject_missing_associativity : forall A, forall operation :e Lean_Mul A,
  Lean_Semigroup_mk_node A operation 0 :e Lean_Semigroup A.
let A operation. assume Hoperation: operation :e Lean_Mul A.
exact Lean_Semigroup_mk_typed A operation Hoperation 0 In_0_1.
Qed.
