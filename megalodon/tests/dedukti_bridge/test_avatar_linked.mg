Section DeduktiProof.
Variable p : prop.
Variable q : prop.
Variable r : prop.
Variable s : prop.
Variable a : prop.
Hypothesis axiom_1_c1 : (dk_cons q (dk_cons p dk_ec)).
Theorem deduction1 : (dk_cons q (dk_cons p dk_ec)).
exact axiom_1_c1.
Qed.
Hypothesis axiom_3_c3 : (dk_cons a (dk_cons (not p) dk_ec)).
Theorem deduction3 : (dk_cons a (dk_cons (not p) dk_ec)).
exact axiom_3_c3.
Qed.
Hypothesis axiom_4_c4 : (dk_cons a (dk_cons (not q) dk_ec)).
Theorem deduction4 : (dk_cons a (dk_cons (not q) dk_ec)).
exact axiom_4_c4.
Qed.
Hypothesis axiom_7_c7 : (dk_cons (not a) dk_ec).
Theorem deduction7 : (dk_cons (not a) dk_ec).
exact axiom_7_c7.
Qed.
Theorem deduction8 : (dk_cons (not q) dk_ec).
exact (fun x0x651bb1d3e030 : ((not q) -> False) => (deduction4 (fun tp : a => (deduction7 (fun tnp : (not a) => (tnp tp)))) x0x651bb1d3e030)).
Qed.
Theorem deduction9 : (dk_cons (not p) dk_ec).
exact (fun x0x651bb1d3e150 : ((not p) -> False) => (deduction3 (fun tp : a => (deduction7 (fun tnp : (not a) => (tnp tp)))) x0x651bb1d3e150)).
Qed.
Definition sp3 : prop := ((not p) -> False).
Definition sp4 : prop := ((not q) -> False).
Theorem deduction27 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp4 (dk_cons sp3 dk_ec))))).
exact (fun nnsp4 : (sp4 -> False) => (fun nnsp3 : (sp3 -> False) => (nnsp4 (fun x0x651bb1d3e2d0 : (q -> False) => (nnsp3 (fun x0x651bb1d3e330 : (p -> False) => (deduction1 x0x651bb1d3e2d0 x0x651bb1d3e330))))))).
Qed.
Theorem deduction28 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp4) dk_ec)))).
exact (fun nnsp4 : ((not sp4) -> False) => (nnsp4 (fun x0x651bb1d3e030 : ((not q) -> False) => (deduction8 x0x651bb1d3e030)))).
Qed.
Theorem deduction29 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp3) dk_ec)))).
exact (fun nnsp3 : ((not sp3) -> False) => (nnsp3 (fun x0x651bb1d3e150 : ((not p) -> False) => (deduction9 x0x651bb1d3e150)))).
Qed.
End DeduktiProof.
