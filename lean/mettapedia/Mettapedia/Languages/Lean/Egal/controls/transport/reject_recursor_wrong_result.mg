
(** Rejection control: a recursor at a constant motive lies in the type both of its minor
    premises give.  Here the none case gives a value in C and the result is claimed in D. **)
Theorem recursor_wrong_result : forall A, forall C:set, forall D:set, forall h0 :e C, forall h1 :e (Pi_ x :e A, C),
  forall t :e Lean_Option A, Lean_Option_rec A h0 h1 t :e D.
let A C D. let h0. assume H0: h0 :e C. let h1. assume H1: h1 :e (Pi_ x :e A, C). let t. assume Ht: t :e Lean_Option A.
exact Lean_Option_rec_In A C h0 H0 h1 H1 t Ht.
Qed.
