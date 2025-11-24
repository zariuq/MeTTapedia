Section DeduktiProof.
Variable f : (set -> set).
Variable a : set.
Variable p : (set -> (set -> prop)).
Hypothesis axiom_1_ax : (forall x0 : set, (dk_cons (p x0 (f x0)) dk_ec)).
Theorem deduction1 : (forall x0 : set, (dk_cons (p x0 (f x0)) dk_ec)).
exact axiom_1_ax.
Qed.
Hypothesis axiom_2_g : (dk_cons (not (p a (f a))) dk_ec).
Theorem deduction2 : (dk_cons (not (p a (f a))) dk_ec).
exact axiom_2_g.
Qed.
Theorem deduction3 : dk_ec.
exact (deduction1 a (fun tp : (p a (f a)) => (deduction2 (fun tnp : (not (p a (f a))) => (tnp tp))))).
Qed.
End DeduktiProof.
