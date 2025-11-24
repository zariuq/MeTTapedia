Section DeduktiProof.
Variable sK0 : set.
Variable p : (set -> prop).
Hypothesis axiom_1_all_p : (forall x0 : set, (p x0)).
Theorem deduction1 : (forall x0 : set, (p x0)).
exact axiom_1_all_p.
Qed.
Hypothesis axiom_2_ex_not_p : (exists x1 : set, (not (p x1))).
Theorem deduction2 : (exists x1 : set, (not (p x1))).
exact axiom_2_ex_not_p.
Qed.
Hypothesis sorry5 : ((exists x1 : set, (not (p x1))) -> (exists x0 : set, (not (p x0)))).
Theorem deduction5 : (exists x0 : set, (not (p x0))).
exact (sorry5 deduction2).
Qed.
Hypothesis sorry7 : ((exists x0 : set, (not (p x0))) -> (not (p sK0))).
Theorem deduction7 : ((exists x0 : set, (not (p x0))) -> (not (p sK0))).
exact sorry7.
Qed.
Hypothesis sorry8 : ((exists x0 : set, (not (p x0))) -> (((exists x0 : set, (not (p x0))) -> (not (p sK0))) -> (not (p sK0)))).
Theorem deduction8 : (not (p sK0)).
exact (sorry8 deduction5 deduction7).
Qed.
Hypothesis sorry9 : ((forall x0 : set, (p x0)) -> (forall x0 : set, (dk_cons (p x0) dk_ec))).
Theorem deduction9 : (forall x0 : set, (dk_cons (p x0) dk_ec)).
exact (sorry9 deduction1).
Qed.
Hypothesis sorry10 : ((not (p sK0)) -> (dk_cons (not (p sK0)) dk_ec)).
Theorem deduction10 : (dk_cons (not (p sK0)) dk_ec).
exact (sorry10 deduction8).
Qed.
Theorem deduction11 : dk_ec.
exact (deduction10 (fun tnp : (not (p sK0)) => (deduction9 sK0 (fun tp : (p sK0) => (tnp tp))))).
Qed.
End DeduktiProof.
