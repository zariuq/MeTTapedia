(** Returning the representative list would expose an order the quotient forgets. **)
Theorem reject_order_observing_lift : forall A, forall xs :e Lean_List A,
  LeanQuotLift (fun list => list) (LeanMultisetClass A xs) = xs.
let A xs. assume Hxs: xs :e Lean_List A.
apply LeanMultisetLift_beta A (fun list => list).
- let first. assume Hfirst: first :e Lean_List A. let second. assume Hsecond: second :e Lean_List A.
  assume Hperm: LeanListPerm A first second. reflexivity.
- exact Hxs.
Qed.
