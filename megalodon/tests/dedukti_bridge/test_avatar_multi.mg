Section DeduktiProof.
Variable p : prop.
Variable q : prop.
Variable r : prop.
Variable s : prop.
Variable t : prop.
Variable u : prop.
Hypothesis axiom_1_c1 : (dk_cons r (dk_cons q (dk_cons p dk_ec))).
Theorem deduction1 : (dk_cons r (dk_cons q (dk_cons p dk_ec))).
exact axiom_1_c1.
Qed.
Hypothesis axiom_2_c2 : (dk_cons s (dk_cons (not p) dk_ec)).
Theorem deduction2 : (dk_cons s (dk_cons (not p) dk_ec)).
exact axiom_2_c2.
Qed.
Hypothesis axiom_3_c3 : (dk_cons t (dk_cons (not q) dk_ec)).
Theorem deduction3 : (dk_cons t (dk_cons (not q) dk_ec)).
exact axiom_3_c3.
Qed.
Hypothesis axiom_4_c4 : (dk_cons u (dk_cons (not r) dk_ec)).
Theorem deduction4 : (dk_cons u (dk_cons (not r) dk_ec)).
exact axiom_4_c4.
Qed.
Hypothesis axiom_5_c5 : (dk_cons (not s) dk_ec).
Theorem deduction5 : (dk_cons (not s) dk_ec).
exact axiom_5_c5.
Qed.
Hypothesis axiom_6_c6 : (dk_cons (not t) dk_ec).
Theorem deduction6 : (dk_cons (not t) dk_ec).
exact axiom_6_c6.
Qed.
Hypothesis axiom_7_c7 : (dk_cons (not u) dk_ec).
Theorem deduction7 : (dk_cons (not u) dk_ec).
exact axiom_7_c7.
Qed.
Theorem deduction8 : (dk_cons (not r) dk_ec).
exact (fun x0x61a05a23efa0 : ((not r) -> False) => (deduction4 (fun tp : u => (deduction7 (fun tnp : (not u) => (tnp tp)))) x0x61a05a23efa0)).
Qed.
Theorem deduction9 : (dk_cons (not q) dk_ec).
exact (fun x0x61a05a23f0c0 : ((not q) -> False) => (deduction3 (fun tp : t => (deduction6 (fun tnp : (not t) => (tnp tp)))) x0x61a05a23f0c0)).
Qed.
Theorem deduction10 : (dk_cons (not p) dk_ec).
exact (fun x0x61a05a23f1e0 : ((not p) -> False) => (deduction2 (fun tp : s => (deduction5 (fun tnp : (not s) => (tnp tp)))) x0x61a05a23f1e0)).
Qed.
Definition sp1 : prop := ((not p) -> False).
Definition sp2 : prop := ((not q) -> False).
Definition sp3 : prop := ((not r) -> False).
Theorem deduction23 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp3 (dk_cons sp2 (dk_cons sp1 dk_ec)))))).
exact (fun nnsp3 : (sp3 -> False) => (fun nnsp2 : (sp2 -> False) => (fun nnsp1 : (sp1 -> False) => (nnsp3 (fun x0x61a05a23f270 : (r -> False) => (nnsp2 (fun x0x61a05a23f2d0 : (q -> False) => (nnsp1 (fun x0x61a05a23f330 : (p -> False) => (deduction1 x0x61a05a23f270 x0x61a05a23f2d0 x0x61a05a23f330)))))))))).
Qed.
Theorem deduction24 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp3) dk_ec)))).
exact (fun nnsp3 : ((not sp3) -> False) => (nnsp3 (fun x0x61a05a23efa0 : ((not r) -> False) => (deduction8 x0x61a05a23efa0)))).
Qed.
Theorem deduction25 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp2) dk_ec)))).
exact (fun nnsp2 : ((not sp2) -> False) => (nnsp2 (fun x0x61a05a23f0c0 : ((not q) -> False) => (deduction9 x0x61a05a23f0c0)))).
Qed.
Theorem deduction26 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp1) dk_ec)))).
exact (fun nnsp1 : ((not sp1) -> False) => (nnsp1 (fun x0x61a05a23f1e0 : ((not p) -> False) => (deduction10 x0x61a05a23f1e0)))).
Qed.
End DeduktiProof.
