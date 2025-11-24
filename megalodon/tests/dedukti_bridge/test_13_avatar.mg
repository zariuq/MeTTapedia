Section DeduktiProof.
Variable p : prop.
Variable q : prop.
Variable r : prop.
Hypothesis axiom_1_c1 : (or p q).
Theorem deduction1 : (or p q).
exact axiom_1_c1.
Qed.
Hypothesis axiom_2_c2 : (or (not p) r).
Theorem deduction2 : (or (not p) r).
exact axiom_2_c2.
Qed.
Hypothesis axiom_3_c3 : (not q).
Theorem deduction3 : (not q).
exact axiom_3_c3.
Qed.
Hypothesis axiom_4_c4 : (not r).
Theorem deduction4 : (not r).
exact axiom_4_c4.
Qed.
Hypothesis sorry8 : ((or p q) -> (dk_cons q (dk_cons p dk_ec))).
Theorem deduction8 : (dk_cons q (dk_cons p dk_ec)).
exact (sorry8 deduction1).
Qed.
Hypothesis sorry9 : ((or (not p) r) -> (dk_cons r (dk_cons (not p) dk_ec))).
Theorem deduction9 : (dk_cons r (dk_cons (not p) dk_ec)).
exact (sorry9 deduction2).
Qed.
Hypothesis sorry10 : ((not q) -> (dk_cons (not q) dk_ec)).
Theorem deduction10 : (dk_cons (not q) dk_ec).
exact (sorry10 deduction3).
Qed.
Hypothesis sorry11 : ((not r) -> (dk_cons (not r) dk_ec)).
Theorem deduction11 : (dk_cons (not r) dk_ec).
exact (sorry11 deduction4).
Qed.
Theorem deduction12 : (dk_cons (not p) dk_ec).
exact (fun x0x56992bc83240 : ((not p) -> False) => (deduction9 (fun tp : r => (deduction11 (fun tnp : (not r) => (tnp tp)))) x0x56992bc83240)).
Qed.
Theorem deduction13 : (dk_cons p dk_ec).
exact (fun x0x56992bc83330 : (p -> False) => (deduction8 (fun tp : q => (deduction10 (fun tnp : (not q) => (tnp tp)))) x0x56992bc83330)).
Qed.
Theorem deduction14 : dk_ec.
exact (deduction13 (fun tp : p => (deduction12 (fun tnp : (not p) => (tnp tp))))).
Qed.
End DeduktiProof.
