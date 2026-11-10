(** The semigroup projection does not have the type of the identity projection. **)
Theorem reject_wrong_parent_projection : forall A, forall m :e Lean_Monoid A,
  Lean_Monoid_toSemigroup A m :e Lean_One A.
let A m. assume Hm: m :e Lean_Monoid A.
exact Lean_Monoid_toSemigroup_In A m Hm.
Qed.
