Section DeduktiProof.
Variable p : prop.
Variable q : prop.
Hypothesis axiom_1_imp : (dk_cons q (dk_cons (not p) dk_ec)).
Theorem deduction1 : (dk_cons q (dk_cons (not p) dk_ec)).
exact axiom_1_imp.
Qed.
Hypothesis axiom_2_nq : (dk_cons (not q) dk_ec).
Theorem deduction2 : (dk_cons (not q) dk_ec).
exact axiom_2_nq.
Qed.
Hypothesis axiom_3_p : (dk_cons p dk_ec).
Theorem deduction3 : (dk_cons p dk_ec).
exact axiom_3_p.
Qed.
Theorem deduction4 : (dk_cons (not p) dk_ec).
exact (fun x0x593b56738300 : ((not p) -> False) => (deduction1 (fun tp : q => (deduction2 (fun tnp : (not q) => (tnp tp)))) x0x593b56738300)).
Qed.
Theorem deduction5 : dk_ec.
exact (deduction4 (fun tnp : (not p) => (deduction3 (fun tp : p => (tnp tp))))).
Qed.
End DeduktiProof.
