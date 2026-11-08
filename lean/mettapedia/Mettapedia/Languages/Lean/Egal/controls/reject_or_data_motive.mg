
(** Rejection control: Or eliminates into propositions only.  Its recursor's
    typing asks for a Prop-valued motive, so a data motive does not type. **)
Theorem or_data_motive : forall A B, forall C:set -> set,
  forall h0 :e (Pi_ x0 :e A, C 0), forall h1 :e (Pi_ x0 :e B, C 0),
  forall t :e Lean_Or_Prop A B, Lean_Or_prec A B h0 h1 t :e C t.
let A B C h0. assume Hh0: h0 :e (Pi_ x0 :e A, C 0).
let h1. assume Hh1: h1 :e (Pi_ x0 :e B, C 0).
exact Lean_Or_prec_type A B C h0 Hh0 h1 Hh1.
Qed.
