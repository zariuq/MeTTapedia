Section DeduktiProof.
Variable a : set.
Variable b : set.
Variable c : set.
Variable red : (set -> prop).
Variable blue : (set -> prop).
Variable edge : (set -> (set -> prop)).
Hypothesis axiom_1_coloring_a : (or (red a) (blue a)).
Theorem deduction1 : (or (red a) (blue a)).
exact axiom_1_coloring_a.
Qed.
Hypothesis axiom_2_coloring_b : (or (red b) (blue b)).
Theorem deduction2 : (or (red b) (blue b)).
exact axiom_2_coloring_b.
Qed.
Hypothesis axiom_3_coloring_c : (or (red c) (blue c)).
Theorem deduction3 : (or (red c) (blue c)).
exact axiom_3_coloring_c.
Qed.
Hypothesis axiom_7_edge_ab : (edge a b).
Theorem deduction7 : (edge a b).
exact axiom_7_edge_ab.
Qed.
Hypothesis axiom_8_edge_bc : (edge b c).
Theorem deduction8 : (edge b c).
exact axiom_8_edge_bc.
Qed.
Hypothesis axiom_9_edge_ca : (edge c a).
Theorem deduction9 : (edge c a).
exact axiom_9_edge_ca.
Qed.
Hypothesis axiom_13_edge_constraint1 : ((edge a b) -> (and (or (not (red a)) (not (red b))) (or (not (blue a)) (not (blue b))))).
Theorem deduction13 : ((edge a b) -> (and (or (not (red a)) (not (red b))) (or (not (blue a)) (not (blue b))))).
exact axiom_13_edge_constraint1.
Qed.
Hypothesis axiom_14_edge_constraint2 : ((edge b c) -> (and (or (not (red b)) (not (red c))) (or (not (blue b)) (not (blue c))))).
Theorem deduction14 : ((edge b c) -> (and (or (not (red b)) (not (red c))) (or (not (blue b)) (not (blue c))))).
exact axiom_14_edge_constraint2.
Qed.
Hypothesis axiom_15_edge_constraint3 : ((edge c a) -> (and (or (not (red c)) (not (red a))) (or (not (blue c)) (not (blue a))))).
Theorem deduction15 : ((edge c a) -> (and (or (not (red c)) (not (red a))) (or (not (blue c)) (not (blue a))))).
exact axiom_15_edge_constraint3.
Qed.
Hypothesis sorry25 : (((edge a b) -> (and (or (not (red a)) (not (red b))) (or (not (blue a)) (not (blue b))))) -> (or (not (edge a b)) (and (or (not (red a)) (not (red b))) (or (not (blue a)) (not (blue b)))))).
Theorem deduction25 : (or (not (edge a b)) (and (or (not (red a)) (not (red b))) (or (not (blue a)) (not (blue b))))).
exact (sorry25 deduction13).
Qed.
Hypothesis sorry26 : (((edge b c) -> (and (or (not (red b)) (not (red c))) (or (not (blue b)) (not (blue c))))) -> (or (not (edge b c)) (and (or (not (red b)) (not (red c))) (or (not (blue b)) (not (blue c)))))).
Theorem deduction26 : (or (not (edge b c)) (and (or (not (red b)) (not (red c))) (or (not (blue b)) (not (blue c))))).
exact (sorry26 deduction14).
Qed.
Hypothesis sorry27 : (((edge c a) -> (and (or (not (red c)) (not (red a))) (or (not (blue c)) (not (blue a))))) -> (or (not (edge c a)) (and (or (not (red c)) (not (red a))) (or (not (blue c)) (not (blue a)))))).
Theorem deduction27 : (or (not (edge c a)) (and (or (not (red c)) (not (red a))) (or (not (blue c)) (not (blue a))))).
exact (sorry27 deduction15).
Qed.
Hypothesis sorry28 : ((or (red a) (blue a)) -> (dk_cons (blue a) (dk_cons (red a) dk_ec))).
Theorem deduction28 : (dk_cons (blue a) (dk_cons (red a) dk_ec)).
exact (sorry28 deduction1).
Qed.
Hypothesis sorry29 : ((or (red b) (blue b)) -> (dk_cons (blue b) (dk_cons (red b) dk_ec))).
Theorem deduction29 : (dk_cons (blue b) (dk_cons (red b) dk_ec)).
exact (sorry29 deduction2).
Qed.
Hypothesis sorry30 : ((or (red c) (blue c)) -> (dk_cons (blue c) (dk_cons (red c) dk_ec))).
Theorem deduction30 : (dk_cons (blue c) (dk_cons (red c) dk_ec)).
exact (sorry30 deduction3).
Qed.
Hypothesis sorry34 : ((edge a b) -> (dk_cons (edge a b) dk_ec)).
Theorem deduction34 : (dk_cons (edge a b) dk_ec).
exact (sorry34 deduction7).
Qed.
Hypothesis sorry35 : ((edge b c) -> (dk_cons (edge b c) dk_ec)).
Theorem deduction35 : (dk_cons (edge b c) dk_ec).
exact (sorry35 deduction8).
Qed.
Hypothesis sorry36 : ((edge c a) -> (dk_cons (edge c a) dk_ec)).
Theorem deduction36 : (dk_cons (edge c a) dk_ec).
exact (sorry36 deduction9).
Qed.
Hypothesis sorry40 : ((or (not (edge a b)) (and (or (not (red a)) (not (red b))) (or (not (blue a)) (not (blue b))))) -> (dk_cons (not (red b)) (dk_cons (not (red a)) (dk_cons (not (edge a b)) dk_ec)))).
Theorem deduction40 : (dk_cons (not (red b)) (dk_cons (not (red a)) (dk_cons (not (edge a b)) dk_ec))).
exact (sorry40 deduction25).
Qed.
Hypothesis sorry41 : ((or (not (edge a b)) (and (or (not (red a)) (not (red b))) (or (not (blue a)) (not (blue b))))) -> (dk_cons (not (blue b)) (dk_cons (not (blue a)) (dk_cons (not (edge a b)) dk_ec)))).
Theorem deduction41 : (dk_cons (not (blue b)) (dk_cons (not (blue a)) (dk_cons (not (edge a b)) dk_ec))).
exact (sorry41 deduction25).
Qed.
Hypothesis sorry42 : ((or (not (edge b c)) (and (or (not (red b)) (not (red c))) (or (not (blue b)) (not (blue c))))) -> (dk_cons (not (red c)) (dk_cons (not (red b)) (dk_cons (not (edge b c)) dk_ec)))).
Theorem deduction42 : (dk_cons (not (red c)) (dk_cons (not (red b)) (dk_cons (not (edge b c)) dk_ec))).
exact (sorry42 deduction26).
Qed.
Hypothesis sorry43 : ((or (not (edge b c)) (and (or (not (red b)) (not (red c))) (or (not (blue b)) (not (blue c))))) -> (dk_cons (not (blue c)) (dk_cons (not (blue b)) (dk_cons (not (edge b c)) dk_ec)))).
Theorem deduction43 : (dk_cons (not (blue c)) (dk_cons (not (blue b)) (dk_cons (not (edge b c)) dk_ec))).
exact (sorry43 deduction26).
Qed.
Hypothesis sorry44 : ((or (not (edge c a)) (and (or (not (red c)) (not (red a))) (or (not (blue c)) (not (blue a))))) -> (dk_cons (not (red a)) (dk_cons (not (red c)) (dk_cons (not (edge c a)) dk_ec)))).
Theorem deduction44 : (dk_cons (not (red a)) (dk_cons (not (red c)) (dk_cons (not (edge c a)) dk_ec))).
exact (sorry44 deduction27).
Qed.
Hypothesis sorry45 : ((or (not (edge c a)) (and (or (not (red c)) (not (red a))) (or (not (blue c)) (not (blue a))))) -> (dk_cons (not (blue a)) (dk_cons (not (blue c)) (dk_cons (not (edge c a)) dk_ec)))).
Theorem deduction45 : (dk_cons (not (blue a)) (dk_cons (not (blue c)) (dk_cons (not (edge c a)) dk_ec))).
exact (sorry45 deduction27).
Qed.
Definition sp1 : prop := ((not (edge c a)) -> False).
Definition sp2 : prop := ((not (red c)) -> False).
Definition sp3 : prop := ((not (red a)) -> False).
Theorem deduction58 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp3) (dk_cons (not sp2) (dk_cons (not sp1) dk_ec)))))).
exact (fun nnsp3 : ((not sp3) -> False) => (fun nnsp2 : ((not sp2) -> False) => (fun nnsp1 : ((not sp1) -> False) => (nnsp3 (fun x0x57ba551c2630 : ((not (red a)) -> False) => (nnsp2 (fun x0x57ba551c24f0 : ((not (red c)) -> False) => (nnsp1 (fun x0x57ba551c2370 : ((not (edge c a)) -> False) => (deduction44 x0x57ba551c2630 x0x57ba551c24f0 x0x57ba551c2370)))))))))).
Qed.
Definition sp4 : prop := ((not (blue c)) -> False).
Definition sp5 : prop := ((not (blue a)) -> False).
Theorem deduction67 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp5) (dk_cons (not sp4) (dk_cons (not sp1) dk_ec)))))).
exact (fun nnsp5 : ((not sp5) -> False) => (fun nnsp4 : ((not sp4) -> False) => (fun nnsp1 : ((not sp1) -> False) => (nnsp5 (fun x0x57ba551c25b0 : ((not (blue a)) -> False) => (nnsp4 (fun x0x57ba551c24b0 : ((not (blue c)) -> False) => (nnsp1 (fun x0x57ba551c2370 : ((not (edge c a)) -> False) => (deduction45 x0x57ba551c25b0 x0x57ba551c24b0 x0x57ba551c2370)))))))))).
Qed.
Definition sp6 : prop := ((not (edge b c)) -> False).
Definition sp7 : prop := ((not (red b)) -> False).
Theorem deduction76 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp7) (dk_cons (not sp6) (dk_cons (not sp2) dk_ec)))))).
exact (fun nnsp7 : ((not sp7) -> False) => (fun nnsp6 : ((not sp6) -> False) => (fun nnsp2 : ((not sp2) -> False) => (nnsp2 (fun x0x57ba551c24f0 : ((not (red c)) -> False) => (nnsp7 (fun x0x57ba551c25f0 : ((not (red b)) -> False) => (nnsp6 (fun x0x57ba551c23b0 : ((not (edge b c)) -> False) => (deduction42 x0x57ba551c24f0 x0x57ba551c25f0 x0x57ba551c23b0)))))))))).
Qed.
Definition sp8 : prop := ((not (blue b)) -> False).
Theorem deduction81 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp8) (dk_cons (not sp6) (dk_cons (not sp4) dk_ec)))))).
exact (fun nnsp8 : ((not sp8) -> False) => (fun nnsp6 : ((not sp6) -> False) => (fun nnsp4 : ((not sp4) -> False) => (nnsp4 (fun x0x57ba551c24b0 : ((not (blue c)) -> False) => (nnsp8 (fun x0x57ba551c2570 : ((not (blue b)) -> False) => (nnsp6 (fun x0x57ba551c23b0 : ((not (edge b c)) -> False) => (deduction43 x0x57ba551c24b0 x0x57ba551c2570 x0x57ba551c23b0)))))))))).
Qed.
Definition sp9 : prop := ((not (edge a b)) -> False).
Theorem deduction86 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp9) (dk_cons (not sp7) (dk_cons (not sp3) dk_ec)))))).
exact (fun nnsp9 : ((not sp9) -> False) => (fun nnsp7 : ((not sp7) -> False) => (fun nnsp3 : ((not sp3) -> False) => (nnsp7 (fun x0x57ba551c25f0 : ((not (red b)) -> False) => (nnsp3 (fun x0x57ba551c2630 : ((not (red a)) -> False) => (nnsp9 (fun x0x57ba551c23f0 : ((not (edge a b)) -> False) => (deduction40 x0x57ba551c25f0 x0x57ba551c2630 x0x57ba551c23f0)))))))))).
Qed.
Theorem deduction87 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp9) (dk_cons (not sp8) (dk_cons (not sp5) dk_ec)))))).
exact (fun nnsp9 : ((not sp9) -> False) => (fun nnsp8 : ((not sp8) -> False) => (fun nnsp5 : ((not sp5) -> False) => (nnsp8 (fun x0x57ba551c2570 : ((not (blue b)) -> False) => (nnsp5 (fun x0x57ba551c25b0 : ((not (blue a)) -> False) => (nnsp9 (fun x0x57ba551c23f0 : ((not (edge a b)) -> False) => (deduction41 x0x57ba551c2570 x0x57ba551c25b0 x0x57ba551c23f0)))))))))).
Qed.
Theorem deduction103 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp1 dk_ec)))).
exact (fun nnsp1 : (sp1 -> False) => (nnsp1 (fun x0x57ba551c27f0 : ((edge c a) -> False) => (deduction36 x0x57ba551c27f0)))).
Qed.
Theorem deduction104 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp6 dk_ec)))).
exact (fun nnsp6 : (sp6 -> False) => (nnsp6 (fun x0x57ba551c2830 : ((edge b c) -> False) => (deduction35 x0x57ba551c2830)))).
Qed.
Theorem deduction105 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp9 dk_ec)))).
exact (fun nnsp9 : (sp9 -> False) => (nnsp9 (fun x0x57ba551c2870 : ((edge a b) -> False) => (deduction34 x0x57ba551c2870)))).
Qed.
Theorem deduction109 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp4 (dk_cons sp2 dk_ec))))).
exact (fun nnsp4 : (sp4 -> False) => (fun nnsp2 : (sp2 -> False) => (nnsp4 (fun x0x57ba551c28f0 : ((blue c) -> False) => (nnsp2 (fun x0x57ba551c2930 : ((red c) -> False) => (deduction30 x0x57ba551c28f0 x0x57ba551c2930))))))).
Qed.
Theorem deduction110 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp8 (dk_cons sp7 dk_ec))))).
exact (fun nnsp8 : (sp8 -> False) => (fun nnsp7 : (sp7 -> False) => (nnsp8 (fun x0x57ba551c2970 : ((blue b) -> False) => (nnsp7 (fun x0x57ba551c29b0 : ((red b) -> False) => (deduction29 x0x57ba551c2970 x0x57ba551c29b0))))))).
Qed.
Theorem deduction111 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp5 (dk_cons sp3 dk_ec))))).
exact (fun nnsp5 : (sp5 -> False) => (fun nnsp3 : (sp3 -> False) => (nnsp5 (fun x0x57ba551c29f0 : ((blue a) -> False) => (nnsp3 (fun x0x57ba551c2a70 : ((red a) -> False) => (deduction28 x0x57ba551c29f0 x0x57ba551c2a70))))))).
Qed.
End DeduktiProof.
