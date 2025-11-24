Section DeduktiProof.
Variable n1 : set.
Variable n2 : set.
Variable n3 : set.
Variable n4 : set.
Variable n5 : set.
Variable n6 : set.
Variable adj : (set -> (set -> prop)).
Hypothesis axiom_2_n1_not_adj_n2 : (not (adj n1 n2)).
Theorem deduction2 : (not (adj n1 n2)).
exact axiom_2_n1_not_adj_n2.
Qed.
Hypothesis axiom_3_n1_not_adj_n3 : (not (adj n1 n3)).
Theorem deduction3 : (not (adj n1 n3)).
exact axiom_3_n1_not_adj_n3.
Qed.
Hypothesis axiom_4_n1_not_adj_n4 : (not (adj n1 n4)).
Theorem deduction4 : (not (adj n1 n4)).
exact axiom_4_n1_not_adj_n4.
Qed.
Hypothesis axiom_5_n1_not_adj_n5 : (not (adj n1 n5)).
Theorem deduction5 : (not (adj n1 n5)).
exact axiom_5_n1_not_adj_n5.
Qed.
Hypothesis axiom_6_n1_not_adj_n6 : (not (adj n1 n6)).
Theorem deduction6 : (not (adj n1 n6)).
exact axiom_6_n1_not_adj_n6.
Qed.
Hypothesis axiom_7_n2_not_adj_n3 : (not (adj n2 n3)).
Theorem deduction7 : (not (adj n2 n3)).
exact axiom_7_n2_not_adj_n3.
Qed.
Hypothesis axiom_8_n2_not_adj_n4 : (not (adj n2 n4)).
Theorem deduction8 : (not (adj n2 n4)).
exact axiom_8_n2_not_adj_n4.
Qed.
Hypothesis axiom_9_n2_not_adj_n5 : (not (adj n2 n5)).
Theorem deduction9 : (not (adj n2 n5)).
exact axiom_9_n2_not_adj_n5.
Qed.
Hypothesis axiom_10_n2_not_adj_n6 : (not (adj n2 n6)).
Theorem deduction10 : (not (adj n2 n6)).
exact axiom_10_n2_not_adj_n6.
Qed.
Hypothesis axiom_11_n3_not_adj_n4 : (not (adj n3 n4)).
Theorem deduction11 : (not (adj n3 n4)).
exact axiom_11_n3_not_adj_n4.
Qed.
Hypothesis axiom_12_n3_not_adj_n5 : (not (adj n3 n5)).
Theorem deduction12 : (not (adj n3 n5)).
exact axiom_12_n3_not_adj_n5.
Qed.
Hypothesis axiom_13_n3_not_adj_n6 : (not (adj n3 n6)).
Theorem deduction13 : (not (adj n3 n6)).
exact axiom_13_n3_not_adj_n6.
Qed.
Hypothesis axiom_14_n4_not_adj_n5 : (not (adj n4 n5)).
Theorem deduction14 : (not (adj n4 n5)).
exact axiom_14_n4_not_adj_n5.
Qed.
Hypothesis axiom_15_n4_not_adj_n6 : (not (adj n4 n6)).
Theorem deduction15 : (not (adj n4 n6)).
exact axiom_15_n4_not_adj_n6.
Qed.
Hypothesis axiom_16_n5_not_adj_n6 : (not (adj n5 n6)).
Theorem deduction16 : (not (adj n5 n6)).
exact axiom_16_n5_not_adj_n6.
Qed.
Hypothesis axiom_18_no_6_indep : (or (adj n1 n2) (or (adj n1 n3) (or (adj n1 n4) (or (adj n1 n5) (or (adj n1 n6) (or (adj n2 n3) (or (adj n2 n4) (or (adj n2 n5) (or (adj n2 n6) (or (adj n3 n4) (or (adj n3 n5) (or (adj n3 n6) (or (adj n4 n5) (or (adj n4 n6) (adj n5 n6))))))))))))))).
Theorem deduction18 : (or (adj n1 n2) (or (adj n1 n3) (or (adj n1 n4) (or (adj n1 n5) (or (adj n1 n6) (or (adj n2 n3) (or (adj n2 n4) (or (adj n2 n5) (or (adj n2 n6) (or (adj n3 n4) (or (adj n3 n5) (or (adj n3 n6) (or (adj n4 n5) (or (adj n4 n6) (adj n5 n6))))))))))))))).
exact axiom_18_no_6_indep.
Qed.
Hypothesis sorry24 : ((not (adj n1 n2)) -> (dk_cons (not (adj n1 n2)) dk_ec)).
Theorem deduction24 : (dk_cons (not (adj n1 n2)) dk_ec).
exact (sorry24 deduction2).
Qed.
Hypothesis sorry25 : ((not (adj n1 n3)) -> (dk_cons (not (adj n1 n3)) dk_ec)).
Theorem deduction25 : (dk_cons (not (adj n1 n3)) dk_ec).
exact (sorry25 deduction3).
Qed.
Hypothesis sorry26 : ((not (adj n1 n4)) -> (dk_cons (not (adj n1 n4)) dk_ec)).
Theorem deduction26 : (dk_cons (not (adj n1 n4)) dk_ec).
exact (sorry26 deduction4).
Qed.
Hypothesis sorry27 : ((not (adj n1 n5)) -> (dk_cons (not (adj n1 n5)) dk_ec)).
Theorem deduction27 : (dk_cons (not (adj n1 n5)) dk_ec).
exact (sorry27 deduction5).
Qed.
Hypothesis sorry28 : ((not (adj n1 n6)) -> (dk_cons (not (adj n1 n6)) dk_ec)).
Theorem deduction28 : (dk_cons (not (adj n1 n6)) dk_ec).
exact (sorry28 deduction6).
Qed.
Hypothesis sorry29 : ((not (adj n2 n3)) -> (dk_cons (not (adj n2 n3)) dk_ec)).
Theorem deduction29 : (dk_cons (not (adj n2 n3)) dk_ec).
exact (sorry29 deduction7).
Qed.
Hypothesis sorry30 : ((not (adj n2 n4)) -> (dk_cons (not (adj n2 n4)) dk_ec)).
Theorem deduction30 : (dk_cons (not (adj n2 n4)) dk_ec).
exact (sorry30 deduction8).
Qed.
Hypothesis sorry31 : ((not (adj n2 n5)) -> (dk_cons (not (adj n2 n5)) dk_ec)).
Theorem deduction31 : (dk_cons (not (adj n2 n5)) dk_ec).
exact (sorry31 deduction9).
Qed.
Hypothesis sorry32 : ((not (adj n2 n6)) -> (dk_cons (not (adj n2 n6)) dk_ec)).
Theorem deduction32 : (dk_cons (not (adj n2 n6)) dk_ec).
exact (sorry32 deduction10).
Qed.
Hypothesis sorry33 : ((not (adj n3 n4)) -> (dk_cons (not (adj n3 n4)) dk_ec)).
Theorem deduction33 : (dk_cons (not (adj n3 n4)) dk_ec).
exact (sorry33 deduction11).
Qed.
Hypothesis sorry34 : ((not (adj n3 n5)) -> (dk_cons (not (adj n3 n5)) dk_ec)).
Theorem deduction34 : (dk_cons (not (adj n3 n5)) dk_ec).
exact (sorry34 deduction12).
Qed.
Hypothesis sorry35 : ((not (adj n3 n6)) -> (dk_cons (not (adj n3 n6)) dk_ec)).
Theorem deduction35 : (dk_cons (not (adj n3 n6)) dk_ec).
exact (sorry35 deduction13).
Qed.
Hypothesis sorry36 : ((not (adj n4 n5)) -> (dk_cons (not (adj n4 n5)) dk_ec)).
Theorem deduction36 : (dk_cons (not (adj n4 n5)) dk_ec).
exact (sorry36 deduction14).
Qed.
Hypothesis sorry37 : ((not (adj n4 n6)) -> (dk_cons (not (adj n4 n6)) dk_ec)).
Theorem deduction37 : (dk_cons (not (adj n4 n6)) dk_ec).
exact (sorry37 deduction15).
Qed.
Hypothesis sorry38 : ((not (adj n5 n6)) -> (dk_cons (not (adj n5 n6)) dk_ec)).
Theorem deduction38 : (dk_cons (not (adj n5 n6)) dk_ec).
exact (sorry38 deduction16).
Qed.
Hypothesis sorry54 : ((or (adj n1 n2) (or (adj n1 n3) (or (adj n1 n4) (or (adj n1 n5) (or (adj n1 n6) (or (adj n2 n3) (or (adj n2 n4) (or (adj n2 n5) (or (adj n2 n6) (or (adj n3 n4) (or (adj n3 n5) (or (adj n3 n6) (or (adj n4 n5) (or (adj n4 n6) (adj n5 n6))))))))))))))) -> (dk_cons (adj n5 n6) (dk_cons (adj n4 n6) (dk_cons (adj n4 n5) (dk_cons (adj n3 n6) (dk_cons (adj n3 n5) (dk_cons (adj n3 n4) (dk_cons (adj n2 n6) (dk_cons (adj n2 n5) (dk_cons (adj n2 n4) (dk_cons (adj n2 n3) (dk_cons (adj n1 n6) (dk_cons (adj n1 n5) (dk_cons (adj n1 n4) (dk_cons (adj n1 n3) (dk_cons (adj n1 n2) dk_ec)))))))))))))))).
Theorem deduction54 : (dk_cons (adj n5 n6) (dk_cons (adj n4 n6) (dk_cons (adj n4 n5) (dk_cons (adj n3 n6) (dk_cons (adj n3 n5) (dk_cons (adj n3 n4) (dk_cons (adj n2 n6) (dk_cons (adj n2 n5) (dk_cons (adj n2 n4) (dk_cons (adj n2 n3) (dk_cons (adj n1 n6) (dk_cons (adj n1 n5) (dk_cons (adj n1 n4) (dk_cons (adj n1 n3) (dk_cons (adj n1 n2) dk_ec))))))))))))))).
exact (sorry54 deduction18).
Qed.
Definition sp1 : prop := ((not (adj n1 n2)) -> False).
Definition sp2 : prop := ((not (adj n1 n3)) -> False).
Definition sp3 : prop := ((not (adj n1 n4)) -> False).
Definition sp4 : prop := ((not (adj n1 n5)) -> False).
Definition sp5 : prop := ((not (adj n1 n6)) -> False).
Definition sp6 : prop := ((not (adj n2 n3)) -> False).
Definition sp7 : prop := ((not (adj n2 n4)) -> False).
Definition sp8 : prop := ((not (adj n2 n5)) -> False).
Definition sp9 : prop := ((not (adj n2 n6)) -> False).
Definition sp10 : prop := ((not (adj n3 n4)) -> False).
Definition sp11 : prop := ((not (adj n3 n5)) -> False).
Definition sp12 : prop := ((not (adj n3 n6)) -> False).
Definition sp13 : prop := ((not (adj n4 n5)) -> False).
Definition sp14 : prop := ((not (adj n4 n6)) -> False).
Definition sp15 : prop := ((not (adj n5 n6)) -> False).
Theorem deduction115 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp15 (dk_cons sp14 (dk_cons sp13 (dk_cons sp12 (dk_cons sp11 (dk_cons sp10 (dk_cons sp9 (dk_cons sp8 (dk_cons sp7 (dk_cons sp6 (dk_cons sp5 (dk_cons sp4 (dk_cons sp3 (dk_cons sp2 (dk_cons sp1 dk_ec)))))))))))))))))).
exact (fun nnsp15 : (sp15 -> False) => (fun nnsp14 : (sp14 -> False) => (fun nnsp13 : (sp13 -> False) => (fun nnsp12 : (sp12 -> False) => (fun nnsp11 : (sp11 -> False) => (fun nnsp10 : (sp10 -> False) => (fun nnsp9 : (sp9 -> False) => (fun nnsp8 : (sp8 -> False) => (fun nnsp7 : (sp7 -> False) => (fun nnsp6 : (sp6 -> False) => (fun nnsp5 : (sp5 -> False) => (fun nnsp4 : (sp4 -> False) => (fun nnsp3 : (sp3 -> False) => (fun nnsp2 : (sp2 -> False) => (fun nnsp1 : (sp1 -> False) => (nnsp15 (fun x0x5c3ac0b65130 : ((adj n5 n6) -> False) => (nnsp14 (fun x0x5c3ac0b651b0 : ((adj n4 n6) -> False) => (nnsp13 (fun x0x5c3ac0b65230 : ((adj n4 n5) -> False) => (nnsp12 (fun x0x5c3ac0b652b0 : ((adj n3 n6) -> False) => (nnsp11 (fun x0x5c3ac0b65330 : ((adj n3 n5) -> False) => (nnsp10 (fun x0x5c3ac0b653b0 : ((adj n3 n4) -> False) => (nnsp9 (fun x0x5c3ac0b65430 : ((adj n2 n6) -> False) => (nnsp8 (fun x0x5c3ac0b654b0 : ((adj n2 n5) -> False) => (nnsp7 (fun x0x5c3ac0b65530 : ((adj n2 n4) -> False) => (nnsp6 (fun x0x5c3ac0b655b0 : ((adj n2 n3) -> False) => (nnsp5 (fun x0x5c3ac0b65630 : ((adj n1 n6) -> False) => (nnsp4 (fun x0x5c3ac0b656b0 : ((adj n1 n5) -> False) => (nnsp3 (fun x0x5c3ac0b65730 : ((adj n1 n4) -> False) => (nnsp2 (fun x0x5c3ac0b657b0 : ((adj n1 n3) -> False) => (nnsp1 (fun x0x5c3ac0b65830 : ((adj n1 n2) -> False) => (deduction54 x0x5c3ac0b65130 x0x5c3ac0b651b0 x0x5c3ac0b65230 x0x5c3ac0b652b0 x0x5c3ac0b65330 x0x5c3ac0b653b0 x0x5c3ac0b65430 x0x5c3ac0b654b0 x0x5c3ac0b65530 x0x5c3ac0b655b0 x0x5c3ac0b65630 x0x5c3ac0b656b0 x0x5c3ac0b65730 x0x5c3ac0b657b0 x0x5c3ac0b65830)))))))))))))))))))))))))))))))))))))))))))))).
Qed.
Theorem deduction116 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp15) dk_ec)))).
exact (fun nnsp15 : ((not sp15) -> False) => (nnsp15 (fun x0x5c3ac0b650f0 : ((not (adj n5 n6)) -> False) => (deduction38 x0x5c3ac0b650f0)))).
Qed.
Theorem deduction117 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp14) dk_ec)))).
exact (fun nnsp14 : ((not sp14) -> False) => (nnsp14 (fun x0x5c3ac0b65170 : ((not (adj n4 n6)) -> False) => (deduction37 x0x5c3ac0b65170)))).
Qed.
Theorem deduction118 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp13) dk_ec)))).
exact (fun nnsp13 : ((not sp13) -> False) => (nnsp13 (fun x0x5c3ac0b651f0 : ((not (adj n4 n5)) -> False) => (deduction36 x0x5c3ac0b651f0)))).
Qed.
Theorem deduction119 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp12) dk_ec)))).
exact (fun nnsp12 : ((not sp12) -> False) => (nnsp12 (fun x0x5c3ac0b65270 : ((not (adj n3 n6)) -> False) => (deduction35 x0x5c3ac0b65270)))).
Qed.
Theorem deduction120 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp11) dk_ec)))).
exact (fun nnsp11 : ((not sp11) -> False) => (nnsp11 (fun x0x5c3ac0b652f0 : ((not (adj n3 n5)) -> False) => (deduction34 x0x5c3ac0b652f0)))).
Qed.
Theorem deduction121 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp10) dk_ec)))).
exact (fun nnsp10 : ((not sp10) -> False) => (nnsp10 (fun x0x5c3ac0b65370 : ((not (adj n3 n4)) -> False) => (deduction33 x0x5c3ac0b65370)))).
Qed.
Theorem deduction122 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp9) dk_ec)))).
exact (fun nnsp9 : ((not sp9) -> False) => (nnsp9 (fun x0x5c3ac0b653f0 : ((not (adj n2 n6)) -> False) => (deduction32 x0x5c3ac0b653f0)))).
Qed.
Theorem deduction123 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp8) dk_ec)))).
exact (fun nnsp8 : ((not sp8) -> False) => (nnsp8 (fun x0x5c3ac0b65470 : ((not (adj n2 n5)) -> False) => (deduction31 x0x5c3ac0b65470)))).
Qed.
Theorem deduction124 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp7) dk_ec)))).
exact (fun nnsp7 : ((not sp7) -> False) => (nnsp7 (fun x0x5c3ac0b654f0 : ((not (adj n2 n4)) -> False) => (deduction30 x0x5c3ac0b654f0)))).
Qed.
Theorem deduction125 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp6) dk_ec)))).
exact (fun nnsp6 : ((not sp6) -> False) => (nnsp6 (fun x0x5c3ac0b65570 : ((not (adj n2 n3)) -> False) => (deduction29 x0x5c3ac0b65570)))).
Qed.
Theorem deduction126 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp5) dk_ec)))).
exact (fun nnsp5 : ((not sp5) -> False) => (nnsp5 (fun x0x5c3ac0b655f0 : ((not (adj n1 n6)) -> False) => (deduction28 x0x5c3ac0b655f0)))).
Qed.
Theorem deduction127 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp4) dk_ec)))).
exact (fun nnsp4 : ((not sp4) -> False) => (nnsp4 (fun x0x5c3ac0b65670 : ((not (adj n1 n5)) -> False) => (deduction27 x0x5c3ac0b65670)))).
Qed.
Theorem deduction128 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp3) dk_ec)))).
exact (fun nnsp3 : ((not sp3) -> False) => (nnsp3 (fun x0x5c3ac0b656f0 : ((not (adj n1 n4)) -> False) => (deduction26 x0x5c3ac0b656f0)))).
Qed.
Theorem deduction129 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp2) dk_ec)))).
exact (fun nnsp2 : ((not sp2) -> False) => (nnsp2 (fun x0x5c3ac0b65770 : ((not (adj n1 n3)) -> False) => (deduction25 x0x5c3ac0b65770)))).
Qed.
Theorem deduction130 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp1) dk_ec)))).
exact (fun nnsp1 : ((not sp1) -> False) => (nnsp1 (fun x0x5c3ac0b657f0 : ((not (adj n1 n2)) -> False) => (deduction24 x0x5c3ac0b657f0)))).
Qed.
End DeduktiProof.
