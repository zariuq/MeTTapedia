Section DeduktiProof.
Variable a : set.
Variable p : (set -> prop).
Hypothesis axiom_1_all_p : (forall x0 : set, (dk_cons (p x0) dk_ec)).
Theorem deduction1 : (forall x0 : set, (dk_cons (p x0) dk_ec)).
exact axiom_1_all_p.
Qed.
Hypothesis axiom_2_neg_goal : (dk_cons (not (p a)) dk_ec).
Theorem deduction2 : (dk_cons (not (p a)) dk_ec).
exact axiom_2_neg_goal.
Qed.
Theorem deduction3 : dk_ec.
exact (deduction2 (fun tnp : (not (p a)) => (deduction1 a (fun tp : (p a) => (tnp tp))))).
Qed.
End DeduktiProof.
