
(** Rejection control: Or.rec into a proposition, in Lean's form, takes a case
    for each side; the case for the left side alone does not eliminate a
    disjunction. **)
Theorem or_one_case : forall A B, forall motive:set -> set,
  0 :e (Pi_ x0 :e A, (motive 0)) ->
  0 :e Lean_Or_Prop A B -> 0 :e (motive 0).
let A B motive. assume H0. assume H.
exact Lean_Or_rec_proof_ok A B motive H0 H.
Qed.
