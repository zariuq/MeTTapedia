Section DeduktiProof.
Variable a : set.
Variable f : (set -> set).
Hypothesis axiom_1_ax : (dk_cons (a = (f (f (f a)))) dk_ec).
Theorem deduction1 : (dk_cons (a = (f (f (f a)))) dk_ec).
exact axiom_1_ax.
Qed.
Hypothesis axiom_2_g : (dk_cons (not (a = (f (f (f a))))) dk_ec).
Theorem deduction2 : (dk_cons (not (a = (f (f (f a))))) dk_ec).
exact axiom_2_g.
Qed.
Theorem deduction3 : dk_ec.
exact (deduction1 (fun tp : (a = (f (f (f a)))) => (deduction2 (fun tnp : (not (a = (f (f (f a))))) => (tnp tp))))).
Qed.
End DeduktiProof.
