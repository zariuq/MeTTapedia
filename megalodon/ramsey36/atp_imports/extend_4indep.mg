Section DeduktiProof.
Variable v0 : set.
Variable v1 : set.
Variable v2 : set.
Variable v3 : set.
Variable v4 : set.
Variable v5 : set.
Variable v6 : set.
Variable v7 : set.
Variable v8 : set.
Variable v9 : set.
Variable v10 : set.
Variable adj : (set -> (set -> prop)).
Hypothesis axiom_1_adj_sym : (forall v0 : set, (forall v1 : set, ((adj v0 v1) -> (adj v1 v0)))).
Theorem deduction1 : (forall v0 : set, (forall v1 : set, ((adj v0 v1) -> (adj v1 v0)))).
exact axiom_1_adj_sym.
Qed.
Hypothesis axiom_3_distinct_01 : (not (v0 = v1)).
Theorem deduction3 : (not (v0 = v1)).
exact axiom_3_distinct_01.
Qed.
Hypothesis axiom_4_distinct_02 : (not (v0 = v2)).
Theorem deduction4 : (not (v0 = v2)).
exact axiom_4_distinct_02.
Qed.
Hypothesis axiom_5_distinct_03 : (not (v0 = v3)).
Theorem deduction5 : (not (v0 = v3)).
exact axiom_5_distinct_03.
Qed.
Hypothesis axiom_6_distinct_04 : (not (v0 = v4)).
Theorem deduction6 : (not (v0 = v4)).
exact axiom_6_distinct_04.
Qed.
Hypothesis axiom_7_distinct_12 : (not (v1 = v2)).
Theorem deduction7 : (not (v1 = v2)).
exact axiom_7_distinct_12.
Qed.
Hypothesis axiom_8_distinct_13 : (not (v1 = v3)).
Theorem deduction8 : (not (v1 = v3)).
exact axiom_8_distinct_13.
Qed.
Hypothesis axiom_9_distinct_14 : (not (v1 = v4)).
Theorem deduction9 : (not (v1 = v4)).
exact axiom_9_distinct_14.
Qed.
Hypothesis axiom_10_distinct_23 : (not (v2 = v3)).
Theorem deduction10 : (not (v2 = v3)).
exact axiom_10_distinct_23.
Qed.
Hypothesis axiom_11_distinct_24 : (not (v2 = v4)).
Theorem deduction11 : (not (v2 = v4)).
exact axiom_11_distinct_24.
Qed.
Hypothesis axiom_12_distinct_34 : (not (v3 = v4)).
Theorem deduction12 : (not (v3 = v4)).
exact axiom_12_distinct_34.
Qed.
Hypothesis axiom_14_indep_12 : (not (adj v1 v2)).
Theorem deduction14 : (not (adj v1 v2)).
exact axiom_14_indep_12.
Qed.
Hypothesis axiom_15_indep_13 : (not (adj v1 v3)).
Theorem deduction15 : (not (adj v1 v3)).
exact axiom_15_indep_13.
Qed.
Hypothesis axiom_16_indep_14 : (not (adj v1 v4)).
Theorem deduction16 : (not (adj v1 v4)).
exact axiom_16_indep_14.
Qed.
Hypothesis axiom_17_indep_23 : (not (adj v2 v3)).
Theorem deduction17 : (not (adj v2 v3)).
exact axiom_17_indep_23.
Qed.
Hypothesis axiom_18_indep_24 : (not (adj v2 v4)).
Theorem deduction18 : (not (adj v2 v4)).
exact axiom_18_indep_24.
Qed.
Hypothesis axiom_19_indep_34 : (not (adj v3 v4)).
Theorem deduction19 : (not (adj v3 v4)).
exact axiom_19_indep_34.
Qed.
Hypothesis axiom_20_v0_nonadj_1 : (not (adj v0 v1)).
Theorem deduction20 : (not (adj v0 v1)).
exact axiom_20_v0_nonadj_1.
Qed.
Hypothesis axiom_21_v0_nonadj_2 : (not (adj v0 v2)).
Theorem deduction21 : (not (adj v0 v2)).
exact axiom_21_v0_nonadj_2.
Qed.
Hypothesis axiom_22_v0_nonadj_3 : (not (adj v0 v3)).
Theorem deduction22 : (not (adj v0 v3)).
exact axiom_22_v0_nonadj_3.
Qed.
Hypothesis axiom_23_v0_nonadj_4 : (not (adj v0 v4)).
Theorem deduction23 : (not (adj v0 v4)).
exact axiom_23_v0_nonadj_4.
Qed.
Hypothesis axiom_29_no_6_indep : (forall v3 : set, (forall v4 : set, (forall v5 : set, (forall v6 : set, (forall v7 : set, (forall v8 : set, ((and (not (v3 = v4)) (and (not (v3 = v5)) (and (not (v3 = v6)) (and (not (v3 = v7)) (and (not (v3 = v8)) (and (not (v4 = v5)) (and (not (v4 = v6)) (and (not (v4 = v7)) (and (not (v4 = v8)) (and (not (v5 = v6)) (and (not (v5 = v7)) (and (not (v5 = v8)) (and (not (v6 = v7)) (and (not (v6 = v8)) (not (v7 = v8)))))))))))))))) -> (or (adj v3 v4) (or (adj v3 v5) (or (adj v3 v6) (or (adj v3 v7) (or (adj v3 v8) (or (adj v4 v5) (or (adj v4 v6) (or (adj v4 v7) (or (adj v4 v8) (or (adj v5 v6) (or (adj v5 v7) (or (adj v5 v8) (or (adj v6 v7) (or (adj v6 v8) (adj v7 v8)))))))))))))))))))))).
Theorem deduction29 : (forall v3 : set, (forall v4 : set, (forall v5 : set, (forall v6 : set, (forall v7 : set, (forall v8 : set, ((and (not (v3 = v4)) (and (not (v3 = v5)) (and (not (v3 = v6)) (and (not (v3 = v7)) (and (not (v3 = v8)) (and (not (v4 = v5)) (and (not (v4 = v6)) (and (not (v4 = v7)) (and (not (v4 = v8)) (and (not (v5 = v6)) (and (not (v5 = v7)) (and (not (v5 = v8)) (and (not (v6 = v7)) (and (not (v6 = v8)) (not (v7 = v8)))))))))))))))) -> (or (adj v3 v4) (or (adj v3 v5) (or (adj v3 v6) (or (adj v3 v7) (or (adj v3 v8) (or (adj v4 v5) (or (adj v4 v6) (or (adj v4 v7) (or (adj v4 v8) (or (adj v5 v6) (or (adj v5 v7) (or (adj v5 v8) (or (adj v6 v7) (or (adj v6 v8) (adj v7 v8)))))))))))))))))))))).
exact axiom_29_no_6_indep.
Qed.
Hypothesis axiom_30_v5_nonadj_0 : (not (adj v5 v0)).
Theorem deduction30 : (not (adj v5 v0)).
exact axiom_30_v5_nonadj_0.
Qed.
Hypothesis axiom_31_v5_nonadj_1 : (not (adj v5 v1)).
Theorem deduction31 : (not (adj v5 v1)).
exact axiom_31_v5_nonadj_1.
Qed.
Hypothesis axiom_32_v5_nonadj_2 : (not (adj v5 v2)).
Theorem deduction32 : (not (adj v5 v2)).
exact axiom_32_v5_nonadj_2.
Qed.
Hypothesis axiom_33_v5_nonadj_3 : (not (adj v5 v3)).
Theorem deduction33 : (not (adj v5 v3)).
exact axiom_33_v5_nonadj_3.
Qed.
Hypothesis axiom_34_v5_nonadj_4 : (not (adj v5 v4)).
Theorem deduction34 : (not (adj v5 v4)).
exact axiom_34_v5_nonadj_4.
Qed.
Hypothesis axiom_35_v5_distinct : (and (not (v0 = v5)) (and (not (v1 = v5)) (and (not (v2 = v5)) (and (not (v3 = v5)) (not (v4 = v5)))))).
Theorem deduction35 : (and (not (v0 = v5)) (and (not (v1 = v5)) (and (not (v2 = v5)) (and (not (v3 = v5)) (not (v4 = v5)))))).
exact axiom_35_v5_distinct.
Qed.
Hypothesis sorry38 : ((forall v3 : set, (forall v4 : set, (forall v5 : set, (forall v6 : set, (forall v7 : set, (forall v8 : set, ((and (not (v3 = v4)) (and (not (v3 = v5)) (and (not (v3 = v6)) (and (not (v3 = v7)) (and (not (v3 = v8)) (and (not (v4 = v5)) (and (not (v4 = v6)) (and (not (v4 = v7)) (and (not (v4 = v8)) (and (not (v5 = v6)) (and (not (v5 = v7)) (and (not (v5 = v8)) (and (not (v6 = v7)) (and (not (v6 = v8)) (not (v7 = v8)))))))))))))))) -> (or (adj v3 v4) (or (adj v3 v5) (or (adj v3 v6) (or (adj v3 v7) (or (adj v3 v8) (or (adj v4 v5) (or (adj v4 v6) (or (adj v4 v7) (or (adj v4 v8) (or (adj v5 v6) (or (adj v5 v7) (or (adj v5 v8) (or (adj v6 v7) (or (adj v6 v8) (adj v7 v8)))))))))))))))))))))) -> (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, ((and (not (v0 = v1)) (and (not (v0 = v2)) (and (not (v0 = v3)) (and (not (v0 = v4)) (and (not (v0 = v5)) (and (not (v1 = v2)) (and (not (v1 = v3)) (and (not (v1 = v4)) (and (not (v1 = v5)) (and (not (v2 = v3)) (and (not (v2 = v4)) (and (not (v2 = v5)) (and (not (v3 = v4)) (and (not (v3 = v5)) (not (v4 = v5)))))))))))))))) -> (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5))))))))))))))))))))))).
Theorem deduction38 : (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, ((and (not (v0 = v1)) (and (not (v0 = v2)) (and (not (v0 = v3)) (and (not (v0 = v4)) (and (not (v0 = v5)) (and (not (v1 = v2)) (and (not (v1 = v3)) (and (not (v1 = v4)) (and (not (v1 = v5)) (and (not (v2 = v3)) (and (not (v2 = v4)) (and (not (v2 = v5)) (and (not (v3 = v4)) (and (not (v3 = v5)) (not (v4 = v5)))))))))))))))) -> (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5)))))))))))))))))))))).
exact (sorry38 deduction29).
Qed.
Hypothesis sorry40 : ((forall v0 : set, (forall v1 : set, ((adj v0 v1) -> (adj v1 v0)))) -> (forall v0 : set, (forall v1 : set, (or (not (adj v0 v1)) (adj v1 v0))))).
Theorem deduction40 : (forall v0 : set, (forall v1 : set, (or (not (adj v0 v1)) (adj v1 v0)))).
exact (sorry40 deduction1).
Qed.
Hypothesis sorry47 : ((forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, ((and (not (v0 = v1)) (and (not (v0 = v2)) (and (not (v0 = v3)) (and (not (v0 = v4)) (and (not (v0 = v5)) (and (not (v1 = v2)) (and (not (v1 = v3)) (and (not (v1 = v4)) (and (not (v1 = v5)) (and (not (v2 = v3)) (and (not (v2 = v4)) (and (not (v2 = v5)) (and (not (v3 = v4)) (and (not (v3 = v5)) (not (v4 = v5)))))))))))))))) -> (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5)))))))))))))))))))))) -> (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, (or (or (v0 = v1) (or (v0 = v2) (or (v0 = v3) (or (v0 = v4) (or (v0 = v5) (or (v1 = v2) (or (v1 = v3) (or (v1 = v4) (or (v1 = v5) (or (v2 = v3) (or (v2 = v4) (or (v2 = v5) (or (v3 = v4) (or (v3 = v5) (v4 = v5))))))))))))))) (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5))))))))))))))))))))))).
Theorem deduction47 : (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, (or (or (v0 = v1) (or (v0 = v2) (or (v0 = v3) (or (v0 = v4) (or (v0 = v5) (or (v1 = v2) (or (v1 = v3) (or (v1 = v4) (or (v1 = v5) (or (v2 = v3) (or (v2 = v4) (or (v2 = v5) (or (v3 = v4) (or (v3 = v5) (v4 = v5))))))))))))))) (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5)))))))))))))))))))))).
exact (sorry47 deduction38).
Qed.
Hypothesis sorry48 : ((forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, (or (or (v0 = v1) (or (v0 = v2) (or (v0 = v3) (or (v0 = v4) (or (v0 = v5) (or (v1 = v2) (or (v1 = v3) (or (v1 = v4) (or (v1 = v5) (or (v2 = v3) (or (v2 = v4) (or (v2 = v5) (or (v3 = v4) (or (v3 = v5) (v4 = v5))))))))))))))) (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5)))))))))))))))))))))) -> (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, (or (v0 = v1) (or (v0 = v2) (or (v0 = v3) (or (v0 = v4) (or (v0 = v5) (or (v1 = v2) (or (v1 = v3) (or (v1 = v4) (or (v1 = v5) (or (v2 = v3) (or (v2 = v4) (or (v2 = v5) (or (v3 = v4) (or (v3 = v5) (or (v4 = v5) (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5))))))))))))))))))))))))))))))))))))).
Theorem deduction48 : (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, (or (v0 = v1) (or (v0 = v2) (or (v0 = v3) (or (v0 = v4) (or (v0 = v5) (or (v1 = v2) (or (v1 = v3) (or (v1 = v4) (or (v1 = v5) (or (v2 = v3) (or (v2 = v4) (or (v2 = v5) (or (v3 = v4) (or (v3 = v5) (or (v4 = v5) (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5)))))))))))))))))))))))))))))))))))).
exact (sorry48 deduction47).
Qed.
Hypothesis sorry49 : ((forall v0 : set, (forall v1 : set, (or (not (adj v0 v1)) (adj v1 v0)))) -> (forall v0 : set, (forall v1 : set, (not (not (adj v0 v1)) -> (not (adj v1 v0) -> False))))).
Theorem deduction49 : (forall v0 : set, (forall v1 : set, (not (not (adj v0 v1)) -> (not (adj v1 v0) -> False)))).
exact (sorry49 deduction40).
Qed.
Hypothesis sorry51 : ((not (v0 = v1)) -> (not (not (v0 = v1)) -> False)).
Theorem deduction51 : (not (not (v0 = v1)) -> False).
exact (sorry51 deduction3).
Qed.
Hypothesis sorry52 : ((not (v0 = v2)) -> (not (not (v0 = v2)) -> False)).
Theorem deduction52 : (not (not (v0 = v2)) -> False).
exact (sorry52 deduction4).
Qed.
Hypothesis sorry53 : ((not (v0 = v3)) -> (not (not (v0 = v3)) -> False)).
Theorem deduction53 : (not (not (v0 = v3)) -> False).
exact (sorry53 deduction5).
Qed.
Hypothesis sorry54 : ((not (v0 = v4)) -> (not (not (v0 = v4)) -> False)).
Theorem deduction54 : (not (not (v0 = v4)) -> False).
exact (sorry54 deduction6).
Qed.
Hypothesis sorry55 : ((not (v1 = v2)) -> (not (not (v1 = v2)) -> False)).
Theorem deduction55 : (not (not (v1 = v2)) -> False).
exact (sorry55 deduction7).
Qed.
Hypothesis sorry56 : ((not (v1 = v3)) -> (not (not (v1 = v3)) -> False)).
Theorem deduction56 : (not (not (v1 = v3)) -> False).
exact (sorry56 deduction8).
Qed.
Hypothesis sorry57 : ((not (v1 = v4)) -> (not (not (v1 = v4)) -> False)).
Theorem deduction57 : (not (not (v1 = v4)) -> False).
exact (sorry57 deduction9).
Qed.
Hypothesis sorry58 : ((not (v2 = v3)) -> (not (not (v2 = v3)) -> False)).
Theorem deduction58 : (not (not (v2 = v3)) -> False).
exact (sorry58 deduction10).
Qed.
Hypothesis sorry59 : ((not (v2 = v4)) -> (not (not (v2 = v4)) -> False)).
Theorem deduction59 : (not (not (v2 = v4)) -> False).
exact (sorry59 deduction11).
Qed.
Hypothesis sorry60 : ((not (v3 = v4)) -> (not (not (v3 = v4)) -> False)).
Theorem deduction60 : (not (not (v3 = v4)) -> False).
exact (sorry60 deduction12).
Qed.
Hypothesis sorry62 : ((not (adj v1 v2)) -> (not (not (adj v1 v2)) -> False)).
Theorem deduction62 : (not (not (adj v1 v2)) -> False).
exact (sorry62 deduction14).
Qed.
Hypothesis sorry63 : ((not (adj v1 v3)) -> (not (not (adj v1 v3)) -> False)).
Theorem deduction63 : (not (not (adj v1 v3)) -> False).
exact (sorry63 deduction15).
Qed.
Hypothesis sorry64 : ((not (adj v1 v4)) -> (not (not (adj v1 v4)) -> False)).
Theorem deduction64 : (not (not (adj v1 v4)) -> False).
exact (sorry64 deduction16).
Qed.
Hypothesis sorry65 : ((not (adj v2 v3)) -> (not (not (adj v2 v3)) -> False)).
Theorem deduction65 : (not (not (adj v2 v3)) -> False).
exact (sorry65 deduction17).
Qed.
Hypothesis sorry66 : ((not (adj v2 v4)) -> (not (not (adj v2 v4)) -> False)).
Theorem deduction66 : (not (not (adj v2 v4)) -> False).
exact (sorry66 deduction18).
Qed.
Hypothesis sorry67 : ((not (adj v3 v4)) -> (not (not (adj v3 v4)) -> False)).
Theorem deduction67 : (not (not (adj v3 v4)) -> False).
exact (sorry67 deduction19).
Qed.
Hypothesis sorry68 : ((not (adj v0 v1)) -> (not (not (adj v0 v1)) -> False)).
Theorem deduction68 : (not (not (adj v0 v1)) -> False).
exact (sorry68 deduction20).
Qed.
Hypothesis sorry69 : ((not (adj v0 v2)) -> (not (not (adj v0 v2)) -> False)).
Theorem deduction69 : (not (not (adj v0 v2)) -> False).
exact (sorry69 deduction21).
Qed.
Hypothesis sorry70 : ((not (adj v0 v3)) -> (not (not (adj v0 v3)) -> False)).
Theorem deduction70 : (not (not (adj v0 v3)) -> False).
exact (sorry70 deduction22).
Qed.
Hypothesis sorry71 : ((not (adj v0 v4)) -> (not (not (adj v0 v4)) -> False)).
Theorem deduction71 : (not (not (adj v0 v4)) -> False).
exact (sorry71 deduction23).
Qed.
Hypothesis sorry77 : ((forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, (or (v0 = v1) (or (v0 = v2) (or (v0 = v3) (or (v0 = v4) (or (v0 = v5) (or (v1 = v2) (or (v1 = v3) (or (v1 = v4) (or (v1 = v5) (or (v2 = v3) (or (v2 = v4) (or (v2 = v5) (or (v3 = v4) (or (v3 = v5) (or (v4 = v5) (or (adj v0 v1) (or (adj v0 v2) (or (adj v0 v3) (or (adj v0 v4) (or (adj v0 v5) (or (adj v1 v2) (or (adj v1 v3) (or (adj v1 v4) (or (adj v1 v5) (or (adj v2 v3) (or (adj v2 v4) (or (adj v2 v5) (or (adj v3 v4) (or (adj v3 v5) (adj v4 v5)))))))))))))))))))))))))))))))))))) -> (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, (not (adj v4 v5) -> (not (adj v3 v5) -> (not (adj v3 v4) -> (not (adj v2 v5) -> (not (adj v2 v4) -> (not (adj v2 v3) -> (not (adj v1 v5) -> (not (adj v1 v4) -> (not (adj v1 v3) -> (not (adj v1 v2) -> (not (adj v0 v5) -> (not (adj v0 v4) -> (not (adj v0 v3) -> (not (adj v0 v2) -> (not (adj v0 v1) -> (not (v4 = v5) -> (not (v3 = v5) -> (not (v3 = v4) -> (not (v2 = v5) -> (not (v2 = v4) -> (not (v2 = v3) -> (not (v1 = v5) -> (not (v1 = v4) -> (not (v1 = v3) -> (not (v1 = v2) -> (not (v0 = v5) -> (not (v0 = v4) -> (not (v0 = v3) -> (not (v0 = v2) -> (not (v0 = v1) -> False))))))))))))))))))))))))))))))))))))).
Theorem deduction77 : (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (forall v4 : set, (forall v5 : set, (not (adj v4 v5) -> (not (adj v3 v5) -> (not (adj v3 v4) -> (not (adj v2 v5) -> (not (adj v2 v4) -> (not (adj v2 v3) -> (not (adj v1 v5) -> (not (adj v1 v4) -> (not (adj v1 v3) -> (not (adj v1 v2) -> (not (adj v0 v5) -> (not (adj v0 v4) -> (not (adj v0 v3) -> (not (adj v0 v2) -> (not (adj v0 v1) -> (not (v4 = v5) -> (not (v3 = v5) -> (not (v3 = v4) -> (not (v2 = v5) -> (not (v2 = v4) -> (not (v2 = v3) -> (not (v1 = v5) -> (not (v1 = v4) -> (not (v1 = v3) -> (not (v1 = v2) -> (not (v0 = v5) -> (not (v0 = v4) -> (not (v0 = v3) -> (not (v0 = v2) -> (not (v0 = v1) -> False)))))))))))))))))))))))))))))))))))).
exact (sorry77 deduction48).
Qed.
Hypothesis sorry78 : ((not (adj v5 v0)) -> (not (not (adj v5 v0)) -> False)).
Theorem deduction78 : (not (not (adj v5 v0)) -> False).
exact (sorry78 deduction30).
Qed.
Hypothesis sorry79 : ((not (adj v5 v1)) -> (not (not (adj v5 v1)) -> False)).
Theorem deduction79 : (not (not (adj v5 v1)) -> False).
exact (sorry79 deduction31).
Qed.
Hypothesis sorry80 : ((not (adj v5 v2)) -> (not (not (adj v5 v2)) -> False)).
Theorem deduction80 : (not (not (adj v5 v2)) -> False).
exact (sorry80 deduction32).
Qed.
Hypothesis sorry81 : ((not (adj v5 v3)) -> (not (not (adj v5 v3)) -> False)).
Theorem deduction81 : (not (not (adj v5 v3)) -> False).
exact (sorry81 deduction33).
Qed.
Hypothesis sorry82 : ((not (adj v5 v4)) -> (not (not (adj v5 v4)) -> False)).
Theorem deduction82 : (not (not (adj v5 v4)) -> False).
exact (sorry82 deduction34).
Qed.
Hypothesis sorry83 : ((and (not (v0 = v5)) (and (not (v1 = v5)) (and (not (v2 = v5)) (and (not (v3 = v5)) (not (v4 = v5)))))) -> (not (not (v0 = v5)) -> False)).
Theorem deduction83 : (not (not (v0 = v5)) -> False).
exact (sorry83 deduction35).
Qed.
Hypothesis sorry84 : ((and (not (v0 = v5)) (and (not (v1 = v5)) (and (not (v2 = v5)) (and (not (v3 = v5)) (not (v4 = v5)))))) -> (not (not (v1 = v5)) -> False)).
Theorem deduction84 : (not (not (v1 = v5)) -> False).
exact (sorry84 deduction35).
Qed.
Hypothesis sorry85 : ((and (not (v0 = v5)) (and (not (v1 = v5)) (and (not (v2 = v5)) (and (not (v3 = v5)) (not (v4 = v5)))))) -> (not (not (v2 = v5)) -> False)).
Theorem deduction85 : (not (not (v2 = v5)) -> False).
exact (sorry85 deduction35).
Qed.
Hypothesis sorry86 : ((and (not (v0 = v5)) (and (not (v1 = v5)) (and (not (v2 = v5)) (and (not (v3 = v5)) (not (v4 = v5)))))) -> (not (not (v3 = v5)) -> False)).
Theorem deduction86 : (not (not (v3 = v5)) -> False).
exact (sorry86 deduction35).
Qed.
Hypothesis sorry87 : ((and (not (v0 = v5)) (and (not (v1 = v5)) (and (not (v2 = v5)) (and (not (v3 = v5)) (not (v4 = v5)))))) -> (not (not (v4 = v5)) -> False)).
Theorem deduction87 : (not (not (v4 = v5)) -> False).
exact (sorry87 deduction35).
Qed.
Theorem deduction557 : (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (not (adj v0 v1) -> (not (adj v2 v1) -> (not (adj v2 v0) -> (not (adj v3 v1) -> (not (adj v3 v0) -> (not (adj v3 v2) -> (not (adj v4 v1) -> (not (adj v4 v0) -> (not (adj v4 v2) -> (not (adj v4 v3) -> (not (adj v5 v1) -> (not (adj v5 v0) -> (not (adj v5 v2) -> (not (adj v5 v3) -> (not (v0 = v1) -> (not (v1 = v2) -> (not (v0 = v2) -> (not (v1 = v3) -> (not (v0 = v3) -> (not (v2 = v3) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v4 = v2) -> (not (v4 = v3) -> (not (v5 = v1) -> (not (v5 = v0) -> (not (v5 = v2) -> (not (v5 = v3) -> (not (v4 = v5) -> False))))))))))))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v2 : set => (fun v3 : set => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac95f0 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9570 : ((adj v2 v0) -> False) => (fun v0x5bbd0aac95b0 : ((adj v3 v1) -> False) => (fun v0x5bbd0aac9530 : ((adj v3 v0) -> False) => (fun v0x5bbd0aac9430 : ((adj v3 v2) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6cb0 : ((adj v4 v2) -> False) => (fun v0x5bbd0aac6b30 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6c70 : ((adj v5 v2) -> False) => (fun v0x5bbd0aac6af0 : ((adj v5 v3) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aacbd30 : ((v1 = v2) -> False) => (fun v0x5bbd0aacbe30 : ((v0 = v2) -> False) => (fun v0x5bbd0aacbcf0 : ((v1 = v3) -> False) => (fun v0x5bbd0aacbdf0 : ((v0 = v3) -> False) => (fun v0x5bbd0aacbc30 : ((v2 = v3) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aac7e30 : ((v4 = v2) -> False) => (fun v0x5bbd0aac7df0 : ((v4 = v3) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (fun v0x5bbd0aac79f0 : ((v5 = v2) -> False) => (fun v0x5bbd0aac79b0 : ((v5 = v3) -> False) => (fun v0x5bbd0aacacf0 : ((v4 = v5) -> False) => (deduction77 v5 v4 v3 v2 v0 v1 v0x5bbd0aacea30 v0x5bbd0aac95f0 v0x5bbd0aac9570 v0x5bbd0aac95b0 v0x5bbd0aac9530 v0x5bbd0aac9430 v0x5bbd0aac6f70 v0x5bbd0aac7270 v0x5bbd0aac6cb0 v0x5bbd0aac6b30 v0x5bbd0aac6f30 v0x5bbd0aac7230 v0x5bbd0aac6c70 v0x5bbd0aac6af0 (fun tp : (adj v5 v4) => (deduction82 (fun tnp : (not (adj v5 v4)) => (tnp tp)))) v0x5bbd0aacbe70 (comml v1 v2 v0x5bbd0aacbd30) (comml v0 v2 v0x5bbd0aacbe30) (comml v1 v3 v0x5bbd0aacbcf0) (comml v0 v3 v0x5bbd0aacbdf0) (comml v2 v3 v0x5bbd0aacbc30) v0x5bbd0aac7e70 v0x5bbd0aac7eb0 v0x5bbd0aac7e30 v0x5bbd0aac7df0 v0x5bbd0aac7a30 v0x5bbd0aac7a70 v0x5bbd0aac79f0 v0x5bbd0aac79b0 (comml v4 v5 v0x5bbd0aacacf0))))))))))))))))))))))))))))))))))).
Qed.
Theorem deduction783 : (forall v0 : set, (forall v1 : set, (forall v2 : set, (forall v3 : set, (not (adj v5 v3) -> (not (adj v5 v2) -> (not (adj v5 v1) -> (not (adj v5 v0) -> (not (adj v3 v2) -> (not (adj v3 v1) -> (not (adj v3 v0) -> (not (adj v2 v1) -> (not (adj v2 v0) -> (not (adj v0 v1) -> (not (adj v4 v3) -> (not (adj v4 v2) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (v0 = v1) -> (not (v1 = v2) -> (not (v0 = v2) -> (not (v1 = v3) -> (not (v0 = v3) -> (not (v2 = v3) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v4 = v2) -> (not (v4 = v3) -> (not (v5 = v1) -> (not (v5 = v0) -> (not (v5 = v2) -> (not (v5 = v3) -> False)))))))))))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v2 : set => (fun v3 : set => (fun v0x5bbd0aac6af0 : ((adj v5 v3) -> False) => (fun v0x5bbd0aac6c70 : ((adj v5 v2) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac9430 : ((adj v3 v2) -> False) => (fun v0x5bbd0aac95b0 : ((adj v3 v1) -> False) => (fun v0x5bbd0aac9530 : ((adj v3 v0) -> False) => (fun v0x5bbd0aac95f0 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9570 : ((adj v2 v0) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac6b30 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac6cb0 : ((adj v4 v2) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aacbd30 : ((v1 = v2) -> False) => (fun v0x5bbd0aacbe30 : ((v0 = v2) -> False) => (fun v0x5bbd0aacbcf0 : ((v1 = v3) -> False) => (fun v0x5bbd0aacbdf0 : ((v0 = v3) -> False) => (fun v0x5bbd0aacbc30 : ((v2 = v3) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aac7e30 : ((v4 = v2) -> False) => (fun v0x5bbd0aac7df0 : ((v4 = v3) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (fun v0x5bbd0aac79f0 : ((v5 = v2) -> False) => (fun v0x5bbd0aac79b0 : ((v5 = v3) -> False) => (deduction557 v0 v1 v2 v3 v0x5bbd0aacea30 v0x5bbd0aac95f0 v0x5bbd0aac9570 v0x5bbd0aac95b0 v0x5bbd0aac9530 v0x5bbd0aac9430 v0x5bbd0aac6f70 v0x5bbd0aac7270 v0x5bbd0aac6cb0 v0x5bbd0aac6b30 v0x5bbd0aac6f30 v0x5bbd0aac7230 v0x5bbd0aac6c70 v0x5bbd0aac6af0 v0x5bbd0aacbe70 v0x5bbd0aacbd30 v0x5bbd0aacbe30 v0x5bbd0aacbcf0 v0x5bbd0aacbdf0 v0x5bbd0aacbc30 v0x5bbd0aac7e70 v0x5bbd0aac7eb0 v0x5bbd0aac7e30 v0x5bbd0aac7df0 v0x5bbd0aac7a30 v0x5bbd0aac7a70 v0x5bbd0aac79f0 v0x5bbd0aac79b0 (fun tp : (v4 = v5) => (deduction87 (fun tnp : (not (v4 = v5)) => (tnp tp))))))))))))))))))))))))))))))))))))).
Qed.
Theorem deduction2527 : (forall v0 : set, (forall v1 : set, (not (adj v5 v0) -> (not (adj v5 v1) -> (not (adj v5 v3) -> (not (adj v5 v1) -> (not (adj v0 v1) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (adj v1 v3) -> (not (adj v1 v1) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (adj v4 v1) -> (not (adj v4 v3) -> (not (v1 = v3) -> (not (v3 = v1) -> (not (v1 = v1) -> (not (v3 = v0) -> (not (v1 = v0) -> (not (v0 = v1) -> (not (v3 = v4) -> (not (v1 = v4) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v3 = v5) -> (not (v1 = v5) -> (not (v5 = v1) -> (not (v5 = v0) -> False))))))))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacce70 : ((adj v5 v3) -> False) => (fun v0x5bbd0aaccf70 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac8b30 : ((v1 = v3) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac90b0 : ((v3 = v4) -> False) => (fun v0x5bbd0aac9830 : ((v1 = v4) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aacab70 : ((v3 = v5) -> False) => (fun v0x5bbd0aacadb0 : ((v1 = v5) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (deduction783 v1 v3 v1 v0 v0x5bbd0aac7230 v0x5bbd0aac6f30 v0x5bbd0aacce70 v0x5bbd0aaccf70 v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 (fun tp : (adj v1 v3) => (deduction63 (fun tnp : (not (adj v1 v3)) => (tnp tp)))) v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 v0x5bbd0aac8b30 v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 (comml v0 v1 v0x5bbd0aacbe70) (comml v3 v4 v0x5bbd0aac90b0) (comml v1 v4 v0x5bbd0aac9830) v0x5bbd0aac7e70 v0x5bbd0aac7eb0 (comml v3 v5 v0x5bbd0aacab70) (comml v1 v5 v0x5bbd0aacadb0) v0x5bbd0aac7a30 v0x5bbd0aac7a70)))))))))))))))))))))))))))))).
Qed.
Theorem deduction2784 : (forall v0 : set, (forall v1 : set, (not (adj v5 v0) -> (not (adj v5 v1) -> (not (adj v5 v1) -> (not (adj v0 v1) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (adj v1 v3) -> (not (adj v1 v1) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (adj v4 v1) -> (not (adj v4 v3) -> (not (v1 = v3) -> (not (v3 = v1) -> (not (v1 = v1) -> (not (v3 = v0) -> (not (v1 = v0) -> (not (v0 = v1) -> (not (v3 = v4) -> (not (v1 = v4) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v3 = v5) -> (not (v1 = v5) -> (not (v5 = v1) -> (not (v5 = v0) -> False)))))))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aaccf70 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac8b30 : ((v1 = v3) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac90b0 : ((v3 = v4) -> False) => (fun v0x5bbd0aac9830 : ((v1 = v4) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aacab70 : ((v3 = v5) -> False) => (fun v0x5bbd0aacadb0 : ((v1 = v5) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (deduction2527 v0 v1 v0x5bbd0aac7230 v0x5bbd0aac6f30 (fun tp : (adj v5 v3) => (deduction81 (fun tnp : (not (adj v5 v3)) => (tnp tp)))) v0x5bbd0aaccf70 v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 v0x5bbd0aac8b30 v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 v0x5bbd0aacbe70 v0x5bbd0aac90b0 v0x5bbd0aac9830 v0x5bbd0aac7e70 v0x5bbd0aac7eb0 v0x5bbd0aacab70 v0x5bbd0aacadb0 v0x5bbd0aac7a30 v0x5bbd0aac7a70))))))))))))))))))))))))))))).
Qed.
Theorem deduction3178 : (forall v0 : set, (forall v1 : set, (not (adj v5 v0) -> (not (adj v5 v1) -> (not (adj v0 v1) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (adj v1 v3) -> (not (adj v1 v1) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (adj v4 v1) -> (not (adj v4 v3) -> (not (v1 = v3) -> (not (v3 = v1) -> (not (v1 = v1) -> (not (v3 = v0) -> (not (v1 = v0) -> (not (v0 = v1) -> (not (v3 = v4) -> (not (v1 = v4) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v3 = v5) -> (not (v1 = v5) -> (not (v5 = v1) -> (not (v5 = v0) -> False))))))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac8b30 : ((v1 = v3) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac90b0 : ((v3 = v4) -> False) => (fun v0x5bbd0aac9830 : ((v1 = v4) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aacab70 : ((v3 = v5) -> False) => (fun v0x5bbd0aacadb0 : ((v1 = v5) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (deduction2784 v0 v1 v0x5bbd0aac7230 v0x5bbd0aac6f30 (fun tp : (adj v5 v1) => (deduction79 (fun tnp : (not (adj v5 v1)) => (tnp tp)))) v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 v0x5bbd0aac8b30 v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 v0x5bbd0aacbe70 v0x5bbd0aac90b0 v0x5bbd0aac9830 v0x5bbd0aac7e70 v0x5bbd0aac7eb0 v0x5bbd0aacab70 v0x5bbd0aacadb0 v0x5bbd0aac7a30 v0x5bbd0aac7a70)))))))))))))))))))))))))))).
Qed.
Theorem deduction3248 : (forall v0 : set, (forall v1 : set, (not (adj v5 v0) -> (not (adj v5 v1) -> (not (adj v0 v1) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (adj v1 v3) -> (not (adj v1 v1) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (adj v4 v1) -> (not (adj v4 v3) -> (not (v3 = v1) -> (not (v1 = v1) -> (not (v3 = v0) -> (not (v1 = v0) -> (not (v0 = v1) -> (not (v3 = v4) -> (not (v1 = v4) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v3 = v5) -> (not (v1 = v5) -> (not (v5 = v1) -> (not (v5 = v0) -> False)))))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac90b0 : ((v3 = v4) -> False) => (fun v0x5bbd0aac9830 : ((v1 = v4) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aacab70 : ((v3 = v5) -> False) => (fun v0x5bbd0aacadb0 : ((v1 = v5) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (deduction3178 v0 v1 v0x5bbd0aac7230 v0x5bbd0aac6f30 v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 (fun tp : (v1 = v3) => (deduction56 (fun tnp : (not (v1 = v3)) => (tnp tp)))) v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 v0x5bbd0aacbe70 v0x5bbd0aac90b0 v0x5bbd0aac9830 v0x5bbd0aac7e70 v0x5bbd0aac7eb0 v0x5bbd0aacab70 v0x5bbd0aacadb0 v0x5bbd0aac7a30 v0x5bbd0aac7a70))))))))))))))))))))))))))).
Qed.
Definition sp288 : prop := ((not (adj v4 v3)) -> False).
Theorem deduction3301 : (Prf_av_clause (av_if sp288 (dk_acl (dk_cl (dk_cons (adj v4 v3) dk_ec))))).
exact (fun nnsp288 : ((not sp288) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (nnsp288 (fun psp : sp288 => (psp v0x5bbd0aebcc00))))).
Qed.
Definition sp290 : prop := ((not (adj v4 v2)) -> False).
Theorem deduction3308 : (Prf_av_clause (av_if (not sp290) (dk_acl (dk_cl (dk_cons (not (adj v4 v2)) dk_ec))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun v0x5bbd0aebc540 : ((not (adj v4 v2)) -> False) => (nnsp290 (fun psp : (not sp290) => (psp v0x5bbd0aebc540))))).
Qed.
Theorem deduction3309 : (Prf_av_clause (av_if sp290 (dk_acl (dk_cl (dk_cons (adj v4 v2) dk_ec))))).
exact (fun nnsp290 : ((not sp290) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (nnsp290 (fun psp : sp290 => (psp v0x5bbd0aebcc40))))).
Qed.
Definition sp292 : prop := ((not (adj v4 v1)) -> False).
Theorem deduction3317 : (Prf_av_clause (av_if sp292 (dk_acl (dk_cl (dk_cons (adj v4 v1) dk_ec))))).
exact (fun nnsp292 : ((not sp292) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (nnsp292 (fun psp : sp292 => (psp v0x5bbd0aebcc80))))).
Qed.
Definition sp294 : prop := ((not (adj v4 v0)) -> False).
Theorem deduction3324 : (Prf_av_clause (av_if (not sp294) (dk_acl (dk_cl (dk_cons (not (adj v4 v0)) dk_ec))))).
exact (fun nnsp294 : ((not (not sp294)) -> False) => (fun v0x5bbd0aebc5c0 : ((not (adj v4 v0)) -> False) => (nnsp294 (fun psp : (not sp294) => (psp v0x5bbd0aebc5c0))))).
Qed.
Theorem deduction3325 : (Prf_av_clause (av_if sp294 (dk_acl (dk_cl (dk_cons (adj v4 v0) dk_ec))))).
exact (fun nnsp294 : ((not sp294) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (nnsp294 (fun psp : sp294 => (psp v0x5bbd0aebccc0))))).
Qed.
Theorem deduction3382 : (forall v0 : set, (forall v1 : set, (not (adj v5 v0) -> (not (adj v5 v1) -> (not (adj v0 v1) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (adj v1 v3) -> (not (adj v1 v1) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (adj v4 v1) -> (not (adj v4 v3) -> (not (v3 = v1) -> (not (v1 = v1) -> (not (v3 = v0) -> (not (v1 = v0) -> (not (v0 = v1) -> (not (v1 = v4) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v3 = v5) -> (not (v1 = v5) -> (not (v5 = v1) -> (not (v5 = v0) -> False))))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac9830 : ((v1 = v4) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aacab70 : ((v3 = v5) -> False) => (fun v0x5bbd0aacadb0 : ((v1 = v5) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (deduction3248 v0 v1 v0x5bbd0aac7230 v0x5bbd0aac6f30 v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 v0x5bbd0aacbe70 (fun tp : (v3 = v4) => (deduction60 (fun tnp : (not (v3 = v4)) => (tnp tp)))) v0x5bbd0aac9830 v0x5bbd0aac7e70 v0x5bbd0aac7eb0 v0x5bbd0aacab70 v0x5bbd0aacadb0 v0x5bbd0aac7a30 v0x5bbd0aac7a70)))))))))))))))))))))))))).
Qed.
Theorem deduction3436 : (forall v0 : set, (forall v1 : set, (not (adj v5 v0) -> (not (adj v5 v1) -> (not (adj v0 v1) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (adj v1 v3) -> (not (adj v1 v1) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (adj v4 v1) -> (not (adj v4 v3) -> (not (v3 = v1) -> (not (v1 = v1) -> (not (v3 = v0) -> (not (v1 = v0) -> (not (v0 = v1) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v3 = v5) -> (not (v1 = v5) -> (not (v5 = v1) -> (not (v5 = v0) -> False)))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aacab70 : ((v3 = v5) -> False) => (fun v0x5bbd0aacadb0 : ((v1 = v5) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (deduction3382 v0 v1 v0x5bbd0aac7230 v0x5bbd0aac6f30 v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 v0x5bbd0aacbe70 (fun tp : (v1 = v4) => (deduction57 (fun tnp : (not (v1 = v4)) => (tnp tp)))) v0x5bbd0aac7e70 v0x5bbd0aac7eb0 v0x5bbd0aacab70 v0x5bbd0aacadb0 v0x5bbd0aac7a30 v0x5bbd0aac7a70))))))))))))))))))))))))).
Qed.
Theorem deduction3490 : (forall v0 : set, (forall v1 : set, (not (adj v5 v0) -> (not (adj v5 v1) -> (not (adj v0 v1) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (adj v1 v3) -> (not (adj v1 v1) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (adj v4 v1) -> (not (adj v4 v3) -> (not (v3 = v1) -> (not (v1 = v1) -> (not (v3 = v0) -> (not (v1 = v0) -> (not (v0 = v1) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v1 = v5) -> (not (v5 = v1) -> (not (v5 = v0) -> False))))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aacadb0 : ((v1 = v5) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (deduction3436 v0 v1 v0x5bbd0aac7230 v0x5bbd0aac6f30 v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 v0x5bbd0aacbe70 v0x5bbd0aac7e70 v0x5bbd0aac7eb0 (fun tp : (v3 = v5) => (deduction86 (fun tnp : (not (v3 = v5)) => (tnp tp)))) v0x5bbd0aacadb0 v0x5bbd0aac7a30 v0x5bbd0aac7a70)))))))))))))))))))))))).
Qed.
Theorem deduction3544 : (forall v0 : set, (forall v1 : set, (not (adj v5 v0) -> (not (adj v5 v1) -> (not (adj v0 v1) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (adj v1 v3) -> (not (adj v1 v1) -> (not (adj v4 v0) -> (not (adj v4 v1) -> (not (adj v4 v1) -> (not (adj v4 v3) -> (not (v3 = v1) -> (not (v1 = v1) -> (not (v3 = v0) -> (not (v1 = v0) -> (not (v0 = v1) -> (not (v4 = v1) -> (not (v4 = v0) -> (not (v5 = v1) -> (not (v5 = v0) -> False)))))))))))))))))))))).
exact (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (deduction3490 v0 v1 v0x5bbd0aac7230 v0x5bbd0aac6f30 v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 v0x5bbd0aacbe70 v0x5bbd0aac7e70 v0x5bbd0aac7eb0 (fun tp : (v1 = v5) => (deduction84 (fun tnp : (not (v1 = v5)) => (tnp tp)))) v0x5bbd0aac7a30 v0x5bbd0aac7a70))))))))))))))))))))))).
Qed.
Definition sp311 : prop := (forall v0 : set, (forall v1 : set, ((not (adj v5 v1)) -> ((not (adj v5 v0)) -> ((not (adj v1 v3)) -> ((not (adj v0 v3)) -> ((not (adj v0 v1)) -> ((not (v0 = v1)) -> ((not (v1 = v0)) -> ((not (v3 = v0)) -> ((not (v1 = v1)) -> ((not (v3 = v1)) -> ((not (adj v4 v1)) -> ((not (adj v4 v0)) -> ((not (adj v1 v1)) -> ((not (v4 = v1)) -> ((not (adj v0 v1)) -> ((not (v4 = v0)) -> ((not (v5 = v1)) -> ((not (v5 = v0)) -> False)))))))))))))))))))).
Theorem deduction3609 : (Prf_av_clause (av_if sp311 (dk_acl (forall v0 : set, (forall v1 : set, (not (adj v5 v1) -> (not (adj v5 v0) -> (not (adj v1 v3) -> (not (adj v0 v3) -> (not (adj v0 v1) -> (not (v0 = v1) -> (not (v1 = v0) -> (not (v3 = v0) -> (not (v1 = v1) -> (not (v3 = v1) -> (not (adj v4 v1) -> (not (adj v4 v0) -> (not (adj v1 v1) -> (not (v4 = v1) -> (not (adj v0 v1) -> (not (v4 = v0) -> (not (v5 = v1) -> (not (v5 = v0) -> False))))))))))))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (nnsp311 (fun psp : sp311 => (psp v0 v1 v0x5bbd0aac6f30 v0x5bbd0aac7230 v0x5bbd0aac8170 v0x5bbd0aac81b0 v0x5bbd0aacea30 v0x5bbd0aacbe70 v0x5bbd0aac85b0 v0x5bbd0aac80b0 v0x5bbd0aac8530 v0x5bbd0aac8070 v0x5bbd0aac6f70 v0x5bbd0aac7270 v0x5bbd0aac91b0 v0x5bbd0aac7e70 v0x5bbd0aac91f0 v0x5bbd0aac7eb0 v0x5bbd0aac7a30 v0x5bbd0aac7a70)))))))))))))))))))))))).
Qed.
Theorem deduction3610 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp311 (dk_cons sp292 (dk_cons sp288 dk_ec)))))).
exact (fun nnsp311 : (sp311 -> False) => (fun nnsp292 : (sp292 -> False) => (fun nnsp288 : (sp288 -> False) => (nnsp311 (fun v0 : set => (fun v1 : set => (fun v0x5bbd0aac6f30 : ((adj v5 v1) -> False) => (fun v0x5bbd0aac7230 : ((adj v5 v0) -> False) => (fun v0x5bbd0aac8170 : ((adj v1 v3) -> False) => (fun v0x5bbd0aac81b0 : ((adj v0 v3) -> False) => (fun v0x5bbd0aacea30 : ((adj v0 v1) -> False) => (fun v0x5bbd0aacbe70 : ((v0 = v1) -> False) => (fun v0x5bbd0aac85b0 : ((v1 = v0) -> False) => (fun v0x5bbd0aac80b0 : ((v3 = v0) -> False) => (fun v0x5bbd0aac8530 : ((v1 = v1) -> False) => (fun v0x5bbd0aac8070 : ((v3 = v1) -> False) => (fun v0x5bbd0aac6f70 : ((adj v4 v1) -> False) => (fun v0x5bbd0aac7270 : ((adj v4 v0) -> False) => (fun v0x5bbd0aac91b0 : ((adj v1 v1) -> False) => (fun v0x5bbd0aac7e70 : ((v4 = v1) -> False) => (fun v0x5bbd0aac91f0 : ((adj v0 v1) -> False) => (fun v0x5bbd0aac7eb0 : ((v4 = v0) -> False) => (fun v0x5bbd0aac7a30 : ((v5 = v1) -> False) => (fun v0x5bbd0aac7a70 : ((v5 = v0) -> False) => (nnsp292 (fun v0x5bbd0aebcc80 : ((adj v4 v1) -> False) => (nnsp288 (fun v0x5bbd0aebcc00 : ((adj v4 v3) -> False) => (deduction3544 v0 v1 v0x5bbd0aac7230 v0x5bbd0aac6f30 v0x5bbd0aacea30 v0x5bbd0aac81b0 v0x5bbd0aac91f0 v0x5bbd0aac8170 v0x5bbd0aac91b0 v0x5bbd0aac7270 v0x5bbd0aac6f70 v0x5bbd0aebcc80 v0x5bbd0aebcc00 v0x5bbd0aac8070 v0x5bbd0aac8530 v0x5bbd0aac80b0 v0x5bbd0aac85b0 v0x5bbd0aacbe70 v0x5bbd0aac7e70 v0x5bbd0aac7eb0 v0x5bbd0aac7a30 v0x5bbd0aac7a70))))))))))))))))))))))))))))).
Qed.
Theorem deduction4769 : (Prf_av_clause (av_if sp288 (dk_acl (dk_cl (dk_cons (adj v3 v4) dk_ec))))).
exact (fun nnsp288 : ((not sp288) -> False) => (fun v0x5bbd0aace1b0 : ((adj v3 v4) -> False) => (deduction3301 nnsp288 (fun tp : (adj v4 v3) => (deduction49 v4 v3 (fun tnp : (not (adj v4 v3)) => (tnp tp)) v0x5bbd0aace1b0))))).
Qed.
Theorem deduction4770 : (Prf_av_clause (av_if sp288 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp288 : ((not sp288) -> False) => (deduction4769 nnsp288 (fun tp : (adj v3 v4) => (deduction67 (fun tnp : (not (adj v3 v4)) => (tnp tp)))))).
Qed.
Theorem deduction4771 : (Prf_av_clause (av_if sp288 (dk_acl (dk_cl dk_ec)))).
exact deduction4770.
Qed.
Theorem deduction4857 : (Prf_av_clause (av_if sp290 (dk_acl (dk_cl (dk_cons (adj v2 v4) dk_ec))))).
exact (fun nnsp290 : ((not sp290) -> False) => (fun v0x5bbd0aace230 : ((adj v2 v4) -> False) => (deduction3309 nnsp290 (fun tp : (adj v4 v2) => (deduction49 v4 v2 (fun tnp : (not (adj v4 v2)) => (tnp tp)) v0x5bbd0aace230))))).
Qed.
Theorem deduction4858 : (Prf_av_clause (av_if sp290 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp290 : ((not sp290) -> False) => (deduction4857 nnsp290 (fun tp : (adj v2 v4) => (deduction66 (fun tnp : (not (adj v2 v4)) => (tnp tp)))))).
Qed.
Theorem deduction4859 : (Prf_av_clause (av_if sp290 (dk_acl (dk_cl dk_ec)))).
exact deduction4858.
Qed.
Theorem deduction4950 : (Prf_av_clause (av_if sp292 (dk_acl (dk_cl (dk_cons (adj v1 v4) dk_ec))))).
exact (fun nnsp292 : ((not sp292) -> False) => (fun v0x5bbd0aace330 : ((adj v1 v4) -> False) => (deduction3317 nnsp292 (fun tp : (adj v4 v1) => (deduction49 v4 v1 (fun tnp : (not (adj v4 v1)) => (tnp tp)) v0x5bbd0aace330))))).
Qed.
Theorem deduction4951 : (Prf_av_clause (av_if sp292 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp292 : ((not sp292) -> False) => (deduction4950 nnsp292 (fun tp : (adj v1 v4) => (deduction64 (fun tnp : (not (adj v1 v4)) => (tnp tp)))))).
Qed.
Theorem deduction4952 : (Prf_av_clause (av_if sp292 (dk_acl (dk_cl dk_ec)))).
exact deduction4951.
Qed.
Theorem deduction6548 : (Prf_av_clause (av_if sp294 (dk_acl (dk_cl (dk_cons (adj v0 v4) dk_ec))))).
exact (fun nnsp294 : ((not sp294) -> False) => (fun v0x5bbd0aacdfb0 : ((adj v0 v4) -> False) => (deduction3325 nnsp294 (fun tp : (adj v4 v0) => (deduction49 v4 v0 (fun tnp : (not (adj v4 v0)) => (tnp tp)) v0x5bbd0aacdfb0))))).
Qed.
Theorem deduction6549 : (Prf_av_clause (av_if sp294 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp294 : ((not sp294) -> False) => (deduction6548 nnsp294 (fun tp : (adj v0 v4) => (deduction71 (fun tnp : (not (adj v0 v4)) => (tnp tp)))))).
Qed.
Theorem deduction6550 : (Prf_av_clause (av_if sp294 (dk_acl (dk_cl dk_ec)))).
exact deduction6549.
Qed.
Definition sp512 : prop := ((not (adj v2 v1)) -> False).
Theorem deduction8223 : (Prf_av_clause (av_if (not sp512) (dk_acl (dk_cl (dk_cons (not (adj v2 v1)) dk_ec))))).
exact (fun nnsp512 : ((not (not sp512)) -> False) => (fun v0x5bbd0b24adb0 : ((not (adj v2 v1)) -> False) => (nnsp512 (fun psp : (not sp512) => (psp v0x5bbd0b24adb0))))).
Qed.
Theorem deduction8224 : (Prf_av_clause (av_if sp512 (dk_acl (dk_cl (dk_cons (adj v2 v1) dk_ec))))).
exact (fun nnsp512 : ((not sp512) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (nnsp512 (fun psp : sp512 => (psp v0x5bbd0b24b930))))).
Qed.
Theorem deduction10653 : (Prf_av_clause (av_if sp512 (dk_acl (dk_cl (dk_cons (adj v1 v2) dk_ec))))).
exact (fun nnsp512 : ((not sp512) -> False) => (fun v0x5bbd0aace430 : ((adj v1 v2) -> False) => (deduction8224 nnsp512 (fun tp : (adj v2 v1) => (deduction49 v2 v1 (fun tnp : (not (adj v2 v1)) => (tnp tp)) v0x5bbd0aace430))))).
Qed.
Theorem deduction10654 : (Prf_av_clause (av_if sp512 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp512 : ((not sp512) -> False) => (deduction10653 nnsp512 (fun tp : (adj v1 v2) => (deduction62 (fun tnp : (not (adj v1 v2)) => (tnp tp)))))).
Qed.
Theorem deduction10655 : (Prf_av_clause (av_if sp512 (dk_acl (dk_cl dk_ec)))).
exact deduction10654.
Qed.
Theorem deduction15256 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (adj v5 v2) (dk_cons (adj v5 v0) (dk_cons (adj v2 v3) (dk_cons (adj v0 v3) (dk_cons (v0 = v2) (dk_cons (v0 = v1) (dk_cons (v0 = v3) (dk_cons (v1 = v2) (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec))))))))))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aaccef0 : ((adj v5 v2) -> False) => (fun v0x5bbd0aaccff0 : ((adj v5 v0) -> False) => (fun v0x5bbd0aace2b0 : ((adj v2 v3) -> False) => (fun v0x5bbd0aace030 : ((adj v0 v3) -> False) => (fun v0x5bbd0aaca2f0 : ((v0 = v2) -> False) => (fun v0x5bbd0aaca230 : ((v0 = v1) -> False) => (fun v0x5bbd0aaca330 : ((v0 = v3) -> False) => (fun v0x5bbd0aaca4b0 : ((v1 = v2) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction3609 nnsp311 v0 v2 v0x5bbd0aaccef0 v0x5bbd0aaccff0 v0x5bbd0aace2b0 v0x5bbd0aace030 (fun tp : (adj v0 v2) => (deduction69 (fun tnp : (not (adj v0 v2)) => (tnp tp)))) v0x5bbd0aaca2f0 (comml v0 v1 v0x5bbd0aaca230) (comml v0 v3 v0x5bbd0aaca330) v0x5bbd0aaca4b0 (comml v2 v3 v0x5bbd0aac98b0) v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 (comml v2 v4 v0x5bbd0aac9970) v0x5bbd0aace130 (comml v0 v4 v0x5bbd0aaca430) (comml v2 v5 v0x5bbd0aacabf0) (comml v0 v5 v0x5bbd0aac74f0)))))))))))))))))))).
Qed.
Theorem deduction15373 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (adj v5 v0) (dk_cons (adj v2 v3) (dk_cons (adj v0 v3) (dk_cons (v0 = v2) (dk_cons (v0 = v1) (dk_cons (v0 = v3) (dk_cons (v1 = v2) (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aaccff0 : ((adj v5 v0) -> False) => (fun v0x5bbd0aace2b0 : ((adj v2 v3) -> False) => (fun v0x5bbd0aace030 : ((adj v0 v3) -> False) => (fun v0x5bbd0aaca2f0 : ((v0 = v2) -> False) => (fun v0x5bbd0aaca230 : ((v0 = v1) -> False) => (fun v0x5bbd0aaca330 : ((v0 = v3) -> False) => (fun v0x5bbd0aaca4b0 : ((v1 = v2) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15256 nnsp311 (fun tp : (adj v5 v2) => (deduction80 (fun tnp : (not (adj v5 v2)) => (tnp tp)))) v0x5bbd0aaccff0 v0x5bbd0aace2b0 v0x5bbd0aace030 v0x5bbd0aaca2f0 v0x5bbd0aaca230 v0x5bbd0aaca330 v0x5bbd0aaca4b0 v0x5bbd0aac98b0 v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))))))))))))).
Qed.
Theorem deduction15383 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (adj v2 v3) (dk_cons (adj v0 v3) (dk_cons (v0 = v2) (dk_cons (v0 = v1) (dk_cons (v0 = v3) (dk_cons (v1 = v2) (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec))))))))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aace2b0 : ((adj v2 v3) -> False) => (fun v0x5bbd0aace030 : ((adj v0 v3) -> False) => (fun v0x5bbd0aaca2f0 : ((v0 = v2) -> False) => (fun v0x5bbd0aaca230 : ((v0 = v1) -> False) => (fun v0x5bbd0aaca330 : ((v0 = v3) -> False) => (fun v0x5bbd0aaca4b0 : ((v1 = v2) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15373 nnsp311 (fun tp : (adj v5 v0) => (deduction78 (fun tnp : (not (adj v5 v0)) => (tnp tp)))) v0x5bbd0aace2b0 v0x5bbd0aace030 v0x5bbd0aaca2f0 v0x5bbd0aaca230 v0x5bbd0aaca330 v0x5bbd0aaca4b0 v0x5bbd0aac98b0 v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0))))))))))))))))).
Qed.
Theorem deduction15393 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (adj v0 v3) (dk_cons (v0 = v2) (dk_cons (v0 = v1) (dk_cons (v0 = v3) (dk_cons (v1 = v2) (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aace030 : ((adj v0 v3) -> False) => (fun v0x5bbd0aaca2f0 : ((v0 = v2) -> False) => (fun v0x5bbd0aaca230 : ((v0 = v1) -> False) => (fun v0x5bbd0aaca330 : ((v0 = v3) -> False) => (fun v0x5bbd0aaca4b0 : ((v1 = v2) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15383 nnsp311 (fun tp : (adj v2 v3) => (deduction65 (fun tnp : (not (adj v2 v3)) => (tnp tp)))) v0x5bbd0aace030 v0x5bbd0aaca2f0 v0x5bbd0aaca230 v0x5bbd0aaca330 v0x5bbd0aaca4b0 v0x5bbd0aac98b0 v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))))))))))).
Qed.
Theorem deduction15403 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (v0 = v2) (dk_cons (v0 = v1) (dk_cons (v0 = v3) (dk_cons (v1 = v2) (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec))))))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aaca2f0 : ((v0 = v2) -> False) => (fun v0x5bbd0aaca230 : ((v0 = v1) -> False) => (fun v0x5bbd0aaca330 : ((v0 = v3) -> False) => (fun v0x5bbd0aaca4b0 : ((v1 = v2) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15393 nnsp311 (fun tp : (adj v0 v3) => (deduction70 (fun tnp : (not (adj v0 v3)) => (tnp tp)))) v0x5bbd0aaca2f0 v0x5bbd0aaca230 v0x5bbd0aaca330 v0x5bbd0aaca4b0 v0x5bbd0aac98b0 v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0))))))))))))))).
Qed.
Theorem deduction15413 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (v0 = v1) (dk_cons (v0 = v3) (dk_cons (v1 = v2) (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aaca230 : ((v0 = v1) -> False) => (fun v0x5bbd0aaca330 : ((v0 = v3) -> False) => (fun v0x5bbd0aaca4b0 : ((v1 = v2) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15403 nnsp311 (fun tp : (v0 = v2) => (deduction52 (fun tnp : (not (v0 = v2)) => (tnp tp)))) v0x5bbd0aaca230 v0x5bbd0aaca330 v0x5bbd0aaca4b0 v0x5bbd0aac98b0 v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))))))))).
Qed.
Theorem deduction15423 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (v0 = v3) (dk_cons (v1 = v2) (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec))))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aaca330 : ((v0 = v3) -> False) => (fun v0x5bbd0aaca4b0 : ((v1 = v2) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15413 nnsp311 (fun tp : (v0 = v1) => (deduction51 (fun tnp : (not (v0 = v1)) => (tnp tp)))) v0x5bbd0aaca330 v0x5bbd0aaca4b0 v0x5bbd0aac98b0 v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0))))))))))))).
Qed.
Theorem deduction15433 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (v1 = v2) (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aaca4b0 : ((v1 = v2) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15423 nnsp311 (fun tp : (v0 = v3) => (deduction53 (fun tnp : (not (v0 = v3)) => (tnp tp)))) v0x5bbd0aaca4b0 v0x5bbd0aac98b0 v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))))))).
Qed.
Theorem deduction15443 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (v2 = v3) (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec))))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aac98b0 : ((v2 = v3) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15433 nnsp311 (fun tp : (v1 = v2) => (deduction55 (fun tnp : (not (v1 = v2)) => (tnp tp)))) v0x5bbd0aac98b0 v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0))))))))))).
Qed.
Theorem deduction15445 : (Prf_av_clause (av_if sp311 (dk_acl (dk_cl (dk_cons (adj v4 v2) (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))))).
exact (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aebcc40 : ((adj v4 v2) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15443 nnsp311 (fun tp : (v2 = v3) => (deduction58 (fun tnp : (not (v2 = v3)) => (tnp tp)))) v0x5bbd0aebcc40 v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))))).
Qed.
Theorem deduction15447 : (Prf_av_clause (av_if (not sp290) (av_if sp311 (dk_acl (dk_cl (dk_cons (adj v4 v0) (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0aebccc0 : ((adj v4 v0) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15445 nnsp311 (fun tp : (adj v4 v2) => (deduction3308 nnsp290 (fun tnp : (not (adj v4 v2)) => (tnp tp)))) v0x5bbd0aebccc0 v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))))).
Qed.
Theorem deduction15449 : (Prf_av_clause (av_if (not sp290) (av_if (not sp294) (av_if sp311 (dk_acl (dk_cl (dk_cons (adj v2 v1) (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun nnsp294 : ((not (not sp294)) -> False) => (fun nnsp311 : ((not sp311) -> False) => (fun v0x5bbd0b24b930 : ((adj v2 v1) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15447 nnsp290 nnsp311 (fun tp : (adj v4 v0) => (deduction3324 nnsp294 (fun tnp : (not (adj v4 v0)) => (tnp tp)))) v0x5bbd0b24b930 v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))))).
Qed.
Theorem deduction15451 : (Prf_av_clause (av_if (not sp290) (av_if (not sp294) (av_if sp311 (av_if (not sp512) (dk_acl (dk_cl (dk_cons (v2 = v4) (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun nnsp294 : ((not (not sp294)) -> False) => (fun nnsp311 : ((not sp311) -> False) => (fun nnsp512 : ((not (not sp512)) -> False) => (fun v0x5bbd0aac9970 : ((v2 = v4) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15449 nnsp290 nnsp294 nnsp311 (fun tp : (adj v2 v1) => (deduction8223 nnsp512 (fun tnp : (not (adj v2 v1)) => (tnp tp)))) v0x5bbd0aac9970 v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))))).
Qed.
Theorem deduction15453 : (Prf_av_clause (av_if (not sp290) (av_if (not sp294) (av_if sp311 (av_if (not sp512) (dk_acl (dk_cl (dk_cons (adj v0 v1) (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec))))))))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun nnsp294 : ((not (not sp294)) -> False) => (fun nnsp311 : ((not sp311) -> False) => (fun nnsp512 : ((not (not sp512)) -> False) => (fun v0x5bbd0aace130 : ((adj v0 v1) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15451 nnsp290 nnsp294 nnsp311 nnsp512 (fun tp : (v2 = v4) => (deduction59 (fun tnp : (not (v2 = v4)) => (tnp tp)))) v0x5bbd0aace130 v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0))))))))).
Qed.
Theorem deduction15455 : (Prf_av_clause (av_if (not sp290) (av_if (not sp294) (av_if sp311 (av_if (not sp512) (dk_acl (dk_cl (dk_cons (v0 = v4) (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec)))))))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun nnsp294 : ((not (not sp294)) -> False) => (fun nnsp311 : ((not sp311) -> False) => (fun nnsp512 : ((not (not sp512)) -> False) => (fun v0x5bbd0aaca430 : ((v0 = v4) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15453 nnsp290 nnsp294 nnsp311 nnsp512 (fun tp : (adj v0 v1) => (deduction68 (fun tnp : (not (adj v0 v1)) => (tnp tp)))) v0x5bbd0aaca430 v0x5bbd0aacabf0 v0x5bbd0aac74f0)))))))).
Qed.
Theorem deduction15457 : (Prf_av_clause (av_if (not sp290) (av_if (not sp294) (av_if sp311 (av_if (not sp512) (dk_acl (dk_cl (dk_cons (v2 = v5) (dk_cons (v0 = v5) dk_ec))))))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun nnsp294 : ((not (not sp294)) -> False) => (fun nnsp311 : ((not sp311) -> False) => (fun nnsp512 : ((not (not sp512)) -> False) => (fun v0x5bbd0aacabf0 : ((v2 = v5) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15455 nnsp290 nnsp294 nnsp311 nnsp512 (fun tp : (v0 = v4) => (deduction54 (fun tnp : (not (v0 = v4)) => (tnp tp)))) v0x5bbd0aacabf0 v0x5bbd0aac74f0))))))).
Qed.
Theorem deduction15459 : (Prf_av_clause (av_if (not sp290) (av_if (not sp294) (av_if sp311 (av_if (not sp512) (dk_acl (dk_cl (dk_cons (v0 = v5) dk_ec)))))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun nnsp294 : ((not (not sp294)) -> False) => (fun nnsp311 : ((not sp311) -> False) => (fun nnsp512 : ((not (not sp512)) -> False) => (fun v0x5bbd0aac74f0 : ((v0 = v5) -> False) => (deduction15457 nnsp290 nnsp294 nnsp311 nnsp512 (fun tp : (v2 = v5) => (deduction85 (fun tnp : (not (v2 = v5)) => (tnp tp)))) v0x5bbd0aac74f0)))))).
Qed.
Theorem deduction15462 : (Prf_av_clause (av_if (not sp290) (av_if (not sp294) (av_if sp311 (av_if (not sp512) (dk_acl (dk_cl dk_ec))))))).
exact (fun nnsp290 : ((not (not sp290)) -> False) => (fun nnsp294 : ((not (not sp294)) -> False) => (fun nnsp311 : ((not sp311) -> False) => (fun nnsp512 : ((not (not sp512)) -> False) => (deduction15459 nnsp290 nnsp294 nnsp311 nnsp512 (fun tp : (v0 = v5) => (deduction83 (fun tnp : (not (v0 = v5)) => (tnp tp))))))))).
Qed.
Theorem deduction15463 : (Prf_av_clause (av_if (not sp290) (av_if (not sp294) (av_if sp311 (av_if (not sp512) (dk_acl (dk_cl dk_ec))))))).
exact deduction15462.
Qed.
End DeduktiProof.
