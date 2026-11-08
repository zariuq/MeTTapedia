
(** Rejection control: Nat.rec's step must move the motive from n to its
    successor.  A step that stays at n does not type the recursor. **)
Theorem wrong_motive : forall C:set -> set, forall h0 :e C Lean_Nat_zero_node,
  forall h1 :e (Pi_ x0 :e Lean_Nat, Pi_ y0 :e C x0, C x0),
  forall t :e Lean_Nat, Lean_Nat_rec h0 h1 t :e C t.
let C h0. assume Hh0: h0 :e C Lean_Nat_zero_node.
let h1. assume Hh1: h1 :e (Pi_ x0 :e Lean_Nat, Pi_ y0 :e C x0, C x0).
exact Lean_Nat_rec_type C h0 Hh0 h1 Hh1.
Qed.
