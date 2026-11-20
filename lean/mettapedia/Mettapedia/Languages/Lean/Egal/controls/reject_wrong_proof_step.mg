
(** Rejection control: Nat.rec into a proposition, in Lean's form.  Its step
    must take the motive from n to the successor of n; a step that stays at n
    proves nothing about the successor. **)
Theorem wrong_proof_step : forall motive:set -> set,
  0 :e (motive Lean_Nat_zero_node) ->
  0 :e (Pi_ x0 :e Lean_Nat, (Pi_ y0 :e (motive x0), (motive x0))) ->
  forall t :e Lean_Nat, 0 :e (motive t).
let motive. assume H0. assume H1.
exact Lean_Nat_rec_proof_ok motive H0 H1.
Qed.
