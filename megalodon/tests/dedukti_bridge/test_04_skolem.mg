Section DeduktiProof.
Variable sK0 : set.
Variable p : (set -> prop).
Hypothesis axiom_1_ex : (dk_cons (p sK0) dk_ec).
Theorem deduction1 : (dk_cons (p sK0) dk_ec).
exact axiom_1_ex.
Qed.
Hypothesis axiom_2_goal : (dk_cons (not (p sK0)) dk_ec).
Theorem deduction2 : (dk_cons (not (p sK0)) dk_ec).
exact axiom_2_goal.
Qed.
Theorem deduction3 : dk_ec.
exact (deduction1 (fun tp : (p sK0) => (deduction2 (fun tnp : (not (p sK0)) => (tnp tp))))).
Qed.
End DeduktiProof.
