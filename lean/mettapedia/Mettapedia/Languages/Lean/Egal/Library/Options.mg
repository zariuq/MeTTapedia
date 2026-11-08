(** Inversion for Lean_Option: every element of Lean_Option A is none, or
    some element of A. **)

Theorem Lean_Option_inv : forall A:set, forall o :e Lean_Option A,
  o = Lean_Option_none_node A \/ exists x :e A, o = Lean_Option_some_node A x.
let A.
apply Lean_Option_ind A.
- apply orIL. reflexivity.
- let x. assume Hx: x :e A. apply orIR. witness x. apply andI.
  + exact Hx.
  + reflexivity.
Qed.
