Section DeduktiProof.
Variable a : set.
Variable b : set.
Variable p : prop.
Hypothesis axiom_2_c2 : p.
Theorem deduction2 : p.
exact axiom_2_c2.
Qed.
Hypothesis axiom_4_ : (not p).
Theorem deduction4 : (not p).
exact axiom_4_.
Qed.
Hypothesis sorry5 : ((not p) -> (not p)).
Theorem deduction5 : (not p).
exact (sorry5 deduction4).
Qed.
Hypothesis sorry7 : (p -> (dk_cons p dk_ec)).
Theorem deduction7 : (dk_cons p dk_ec).
exact (sorry7 deduction2).
Qed.
Hypothesis sorry8 : ((not p) -> (dk_cons (not p) dk_ec)).
Theorem deduction8 : (dk_cons (not p) dk_ec).
exact (sorry8 deduction5).
Qed.
Theorem deduction9 : dk_ec.
exact (deduction7 (fun tp : p => (deduction8 (fun tnp : (not p) => (tnp tp))))).
Qed.
End DeduktiProof.
