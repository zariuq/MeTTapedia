Section DeduktiProof.
Variable a : set.
Hypothesis axiom_1_neq_self : (not (a = a)).
Theorem deduction1 : (not (a = a)).
exact axiom_1_neq_self.
Qed.
Hypothesis sorry5 : ((not (a = a)) -> (dk_cons (not (a = a)) dk_ec)).
Theorem deduction5 : (dk_cons (not (a = a)) dk_ec).
exact (sorry5 deduction1).
Qed.
Theorem deduction6 : dk_ec.
exact (deduction5 (fun p : (not (a = a)) => (p (eqI a)))).
Qed.
End DeduktiProof.
