Section DeduktiProof.
Variable a : set.
Hypothesis axiom_3_ : (not (a = a)).
Theorem deduction3 : (not (a = a)).
exact axiom_3_.
Qed.
Hypothesis sorry4 : ((not (a = a)) -> (not (a = a))).
Theorem deduction4 : (not (a = a)).
exact (sorry4 deduction3).
Qed.
Hypothesis sorry6 : ((not (a = a)) -> (dk_cons (not (a = a)) dk_ec)).
Theorem deduction6 : (dk_cons (not (a = a)) dk_ec).
exact (sorry6 deduction4).
Qed.
Theorem deduction7 : dk_ec.
exact (deduction6 (fun p : (not (a = a)) => (p (eqI a)))).
Qed.
End DeduktiProof.
