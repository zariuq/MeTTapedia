Section DeduktiProof.
Variable v0 : set.
Variable n1 : set.
Variable n2 : set.
Variable n3 : set.
Variable n4 : set.
Variable n5 : set.
Variable n6 : set.
Variable red : (set -> (set -> prop)).
Variable blue : (set -> (set -> prop)).
Hypothesis axiom_1_red_sym : (forall x0 : set, (forall x1 : set, ((red x0 x1) -> (red x1 x0)))).
Theorem deduction1 : (forall x0 : set, (forall x1 : set, ((red x0 x1) -> (red x1 x0)))).
exact axiom_1_red_sym.
Qed.
Hypothesis axiom_3_edge_coloring : (forall x0 : set, (forall x1 : set, ((not (x0 = x1)) -> (iff (red x0 x1) (not (blue x0 x1)))))).
Theorem deduction3 : (forall x0 : set, (forall x1 : set, ((not (x0 = x1)) -> (iff (red x0 x1) (not (blue x0 x1)))))).
exact axiom_3_edge_coloring.
Qed.
Hypothesis axiom_4_red_neighbors : (and (red v0 n1) (and (red v0 n2) (and (red v0 n3) (and (red v0 n4) (and (red v0 n5) (red v0 n6)))))).
Theorem deduction4 : (and (red v0 n1) (and (red v0 n2) (and (red v0 n3) (and (red v0 n4) (and (red v0 n5) (red v0 n6)))))).
exact axiom_4_red_neighbors.
Qed.
Hypothesis axiom_5_distinct : (and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))).
Theorem deduction5 : (and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))).
exact axiom_5_distinct.
Qed.
Hypothesis axiom_6_no_red_K3 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (red x0 x1) (and (red x1 x2) (red x0 x2))))))).
Theorem deduction6 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (red x0 x1) (and (red x1 x2) (red x0 x2))))))).
exact axiom_6_no_red_K3.
Qed.
Hypothesis axiom_8_ : (not (and (blue n1 n2) (and (blue n1 n3) (and (blue n1 n4) (and (blue n1 n5) (and (blue n1 n6) (and (blue n2 n3) (and (blue n2 n4) (and (blue n2 n5) (and (blue n2 n6) (and (blue n3 n4) (and (blue n3 n5) (and (blue n3 n6) (and (blue n4 n5) (and (blue n4 n6) (blue n5 n6)))))))))))))))).
Theorem deduction8 : (not (and (blue n1 n2) (and (blue n1 n3) (and (blue n1 n4) (and (blue n1 n5) (and (blue n1 n6) (and (blue n2 n3) (and (blue n2 n4) (and (blue n2 n5) (and (blue n2 n6) (and (blue n3 n4) (and (blue n3 n5) (and (blue n3 n6) (and (blue n4 n5) (and (blue n4 n6) (blue n5 n6)))))))))))))))).
exact axiom_8_.
Qed.
Hypothesis sorry9 : ((forall x0 : set, (forall x1 : set, ((red x0 x1) -> (red x1 x0)))) -> (forall x0 : set, (forall x1 : set, (or (not (red x0 x1)) (red x1 x0))))).
Theorem deduction9 : (forall x0 : set, (forall x1 : set, (or (not (red x0 x1)) (red x1 x0)))).
exact (sorry9 deduction1).
Qed.
Hypothesis sorry11 : ((forall x0 : set, (forall x1 : set, ((not (x0 = x1)) -> (iff (red x0 x1) (not (blue x0 x1)))))) -> (forall x0 : set, (forall x1 : set, (or (x0 = x1) (iff (red x0 x1) (not (blue x0 x1))))))).
Theorem deduction11 : (forall x0 : set, (forall x1 : set, (or (x0 = x1) (iff (red x0 x1) (not (blue x0 x1)))))).
exact (sorry11 deduction3).
Qed.
Hypothesis sorry12 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (red x0 x1) (and (red x1 x2) (red x0 x2))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (red x0 x1)) (or (not (red x1 x2)) (not (red x0 x2)))))))).
Theorem deduction12 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (red x0 x1)) (or (not (red x1 x2)) (not (red x0 x2))))))).
exact (sorry12 deduction6).
Qed.
Hypothesis sorry13 : ((not (and (blue n1 n2) (and (blue n1 n3) (and (blue n1 n4) (and (blue n1 n5) (and (blue n1 n6) (and (blue n2 n3) (and (blue n2 n4) (and (blue n2 n5) (and (blue n2 n6) (and (blue n3 n4) (and (blue n3 n5) (and (blue n3 n6) (and (blue n4 n5) (and (blue n4 n6) (blue n5 n6)))))))))))))))) -> (or (not (blue n1 n2)) (or (not (blue n1 n3)) (or (not (blue n1 n4)) (or (not (blue n1 n5)) (or (not (blue n1 n6)) (or (not (blue n2 n3)) (or (not (blue n2 n4)) (or (not (blue n2 n5)) (or (not (blue n2 n6)) (or (not (blue n3 n4)) (or (not (blue n3 n5)) (or (not (blue n3 n6)) (or (not (blue n4 n5)) (or (not (blue n4 n6)) (not (blue n5 n6))))))))))))))))).
Theorem deduction13 : (or (not (blue n1 n2)) (or (not (blue n1 n3)) (or (not (blue n1 n4)) (or (not (blue n1 n5)) (or (not (blue n1 n6)) (or (not (blue n2 n3)) (or (not (blue n2 n4)) (or (not (blue n2 n5)) (or (not (blue n2 n6)) (or (not (blue n3 n4)) (or (not (blue n3 n5)) (or (not (blue n3 n6)) (or (not (blue n4 n5)) (or (not (blue n4 n6)) (not (blue n5 n6)))))))))))))))).
exact (sorry13 deduction8).
Qed.
Hypothesis sorry14 : ((forall x0 : set, (forall x1 : set, (or (x0 = x1) (iff (red x0 x1) (not (blue x0 x1)))))) -> (forall x0 : set, (forall x1 : set, (or (x0 = x1) (and (or (not (red x0 x1)) (not (blue x0 x1))) (or (blue x0 x1) (red x0 x1))))))).
Theorem deduction14 : (forall x0 : set, (forall x1 : set, (or (x0 = x1) (and (or (not (red x0 x1)) (not (blue x0 x1))) (or (blue x0 x1) (red x0 x1)))))).
exact (sorry14 deduction11).
Qed.
Hypothesis sorry15 : ((forall x0 : set, (forall x1 : set, (or (not (red x0 x1)) (red x1 x0)))) -> (forall x0 : set, (forall x1 : set, (dk_cons (not (red x0 x1)) (dk_cons (red x1 x0) dk_ec))))).
Theorem deduction15 : (forall x0 : set, (forall x1 : set, (dk_cons (not (red x0 x1)) (dk_cons (red x1 x0) dk_ec)))).
exact (sorry15 deduction9).
Qed.
Hypothesis sorry18 : ((forall x0 : set, (forall x1 : set, (or (x0 = x1) (and (or (not (red x0 x1)) (not (blue x0 x1))) (or (blue x0 x1) (red x0 x1)))))) -> (forall x0 : set, (forall x1 : set, (dk_cons (blue x0 x1) (dk_cons (red x0 x1) (dk_cons (x0 = x1) dk_ec)))))).
Theorem deduction18 : (forall x0 : set, (forall x1 : set, (dk_cons (blue x0 x1) (dk_cons (red x0 x1) (dk_cons (x0 = x1) dk_ec))))).
exact (sorry18 deduction14).
Qed.
Hypothesis sorry19 : ((and (red v0 n1) (and (red v0 n2) (and (red v0 n3) (and (red v0 n4) (and (red v0 n5) (red v0 n6)))))) -> (dk_cons (red v0 n1) dk_ec)).
Theorem deduction19 : (dk_cons (red v0 n1) dk_ec).
exact (sorry19 deduction4).
Qed.
Hypothesis sorry20 : ((and (red v0 n1) (and (red v0 n2) (and (red v0 n3) (and (red v0 n4) (and (red v0 n5) (red v0 n6)))))) -> (dk_cons (red v0 n2) dk_ec)).
Theorem deduction20 : (dk_cons (red v0 n2) dk_ec).
exact (sorry20 deduction4).
Qed.
Hypothesis sorry21 : ((and (red v0 n1) (and (red v0 n2) (and (red v0 n3) (and (red v0 n4) (and (red v0 n5) (red v0 n6)))))) -> (dk_cons (red v0 n3) dk_ec)).
Theorem deduction21 : (dk_cons (red v0 n3) dk_ec).
exact (sorry21 deduction4).
Qed.
Hypothesis sorry22 : ((and (red v0 n1) (and (red v0 n2) (and (red v0 n3) (and (red v0 n4) (and (red v0 n5) (red v0 n6)))))) -> (dk_cons (red v0 n4) dk_ec)).
Theorem deduction22 : (dk_cons (red v0 n4) dk_ec).
exact (sorry22 deduction4).
Qed.
Hypothesis sorry23 : ((and (red v0 n1) (and (red v0 n2) (and (red v0 n3) (and (red v0 n4) (and (red v0 n5) (red v0 n6)))))) -> (dk_cons (red v0 n5) dk_ec)).
Theorem deduction23 : (dk_cons (red v0 n5) dk_ec).
exact (sorry23 deduction4).
Qed.
Hypothesis sorry24 : ((and (red v0 n1) (and (red v0 n2) (and (red v0 n3) (and (red v0 n4) (and (red v0 n5) (red v0 n6)))))) -> (dk_cons (red v0 n6) dk_ec)).
Theorem deduction24 : (dk_cons (red v0 n6) dk_ec).
exact (sorry24 deduction4).
Qed.
Hypothesis sorry31 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n1 = n2)) dk_ec)).
Theorem deduction31 : (dk_cons (not (n1 = n2)) dk_ec).
exact (sorry31 deduction5).
Qed.
Hypothesis sorry32 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n1 = n3)) dk_ec)).
Theorem deduction32 : (dk_cons (not (n1 = n3)) dk_ec).
exact (sorry32 deduction5).
Qed.
Hypothesis sorry33 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n1 = n4)) dk_ec)).
Theorem deduction33 : (dk_cons (not (n1 = n4)) dk_ec).
exact (sorry33 deduction5).
Qed.
Hypothesis sorry34 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n1 = n5)) dk_ec)).
Theorem deduction34 : (dk_cons (not (n1 = n5)) dk_ec).
exact (sorry34 deduction5).
Qed.
Hypothesis sorry35 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n1 = n6)) dk_ec)).
Theorem deduction35 : (dk_cons (not (n1 = n6)) dk_ec).
exact (sorry35 deduction5).
Qed.
Hypothesis sorry36 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n2 = n3)) dk_ec)).
Theorem deduction36 : (dk_cons (not (n2 = n3)) dk_ec).
exact (sorry36 deduction5).
Qed.
Hypothesis sorry37 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n2 = n4)) dk_ec)).
Theorem deduction37 : (dk_cons (not (n2 = n4)) dk_ec).
exact (sorry37 deduction5).
Qed.
Hypothesis sorry38 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n2 = n5)) dk_ec)).
Theorem deduction38 : (dk_cons (not (n2 = n5)) dk_ec).
exact (sorry38 deduction5).
Qed.
Hypothesis sorry39 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n2 = n6)) dk_ec)).
Theorem deduction39 : (dk_cons (not (n2 = n6)) dk_ec).
exact (sorry39 deduction5).
Qed.
Hypothesis sorry40 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n3 = n4)) dk_ec)).
Theorem deduction40 : (dk_cons (not (n3 = n4)) dk_ec).
exact (sorry40 deduction5).
Qed.
Hypothesis sorry41 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n3 = n5)) dk_ec)).
Theorem deduction41 : (dk_cons (not (n3 = n5)) dk_ec).
exact (sorry41 deduction5).
Qed.
Hypothesis sorry42 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n3 = n6)) dk_ec)).
Theorem deduction42 : (dk_cons (not (n3 = n6)) dk_ec).
exact (sorry42 deduction5).
Qed.
Hypothesis sorry43 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n4 = n5)) dk_ec)).
Theorem deduction43 : (dk_cons (not (n4 = n5)) dk_ec).
exact (sorry43 deduction5).
Qed.
Hypothesis sorry44 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n4 = n6)) dk_ec)).
Theorem deduction44 : (dk_cons (not (n4 = n6)) dk_ec).
exact (sorry44 deduction5).
Qed.
Hypothesis sorry45 : ((and (not (v0 = n1)) (and (not (v0 = n2)) (and (not (v0 = n3)) (and (not (v0 = n4)) (and (not (v0 = n5)) (and (not (v0 = n6)) (and (not (n1 = n2)) (and (not (n1 = n3)) (and (not (n1 = n4)) (and (not (n1 = n5)) (and (not (n1 = n6)) (and (not (n2 = n3)) (and (not (n2 = n4)) (and (not (n2 = n5)) (and (not (n2 = n6)) (and (not (n3 = n4)) (and (not (n3 = n5)) (and (not (n3 = n6)) (and (not (n4 = n5)) (and (not (n4 = n6)) (not (n5 = n6)))))))))))))))))))))) -> (dk_cons (not (n5 = n6)) dk_ec)).
Theorem deduction45 : (dk_cons (not (n5 = n6)) dk_ec).
exact (sorry45 deduction5).
Qed.
Hypothesis sorry46 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (red x0 x1)) (or (not (red x1 x2)) (not (red x0 x2))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (dk_cons (not (red x1 x2)) (dk_cons (not (red x0 x2)) (dk_cons (not (red x0 x1)) dk_ec))))))).
Theorem deduction46 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (dk_cons (not (red x1 x2)) (dk_cons (not (red x0 x2)) (dk_cons (not (red x0 x1)) dk_ec)))))).
exact (sorry46 deduction12).
Qed.
Hypothesis sorry47 : ((or (not (blue n1 n2)) (or (not (blue n1 n3)) (or (not (blue n1 n4)) (or (not (blue n1 n5)) (or (not (blue n1 n6)) (or (not (blue n2 n3)) (or (not (blue n2 n4)) (or (not (blue n2 n5)) (or (not (blue n2 n6)) (or (not (blue n3 n4)) (or (not (blue n3 n5)) (or (not (blue n3 n6)) (or (not (blue n4 n5)) (or (not (blue n4 n6)) (not (blue n5 n6)))))))))))))))) -> (dk_cons (not (blue n5 n6)) (dk_cons (not (blue n4 n6)) (dk_cons (not (blue n4 n5)) (dk_cons (not (blue n3 n6)) (dk_cons (not (blue n3 n5)) (dk_cons (not (blue n3 n4)) (dk_cons (not (blue n2 n6)) (dk_cons (not (blue n2 n5)) (dk_cons (not (blue n2 n4)) (dk_cons (not (blue n2 n3)) (dk_cons (not (blue n1 n6)) (dk_cons (not (blue n1 n5)) (dk_cons (not (blue n1 n4)) (dk_cons (not (blue n1 n3)) (dk_cons (not (blue n1 n2)) dk_ec)))))))))))))))).
Theorem deduction47 : (dk_cons (not (blue n5 n6)) (dk_cons (not (blue n4 n6)) (dk_cons (not (blue n4 n5)) (dk_cons (not (blue n3 n6)) (dk_cons (not (blue n3 n5)) (dk_cons (not (blue n3 n4)) (dk_cons (not (blue n2 n6)) (dk_cons (not (blue n2 n5)) (dk_cons (not (blue n2 n4)) (dk_cons (not (blue n2 n3)) (dk_cons (not (blue n1 n6)) (dk_cons (not (blue n1 n5)) (dk_cons (not (blue n1 n4)) (dk_cons (not (blue n1 n3)) (dk_cons (not (blue n1 n2)) dk_ec))))))))))))))).
exact (sorry47 deduction13).
Qed.
Definition sp1 : prop := ((not (blue n1 n2)) -> False).
Theorem deduction51 : (Prf_av_clause (av_if (not sp1) (dk_acl (dk_cl (dk_cons (not (blue n1 n2)) dk_ec))))).
exact (fun nnsp1 : ((not (not sp1)) -> False) => (fun x0x5f598c1c09b0 : ((not (blue n1 n2)) -> False) => (nnsp1 (fun psp : (not sp1) => (psp x0x5f598c1c09b0))))).
Qed.
Definition sp2 : prop := ((not (blue n1 n3)) -> False).
Theorem deduction55 : (Prf_av_clause (av_if (not sp2) (dk_acl (dk_cl (dk_cons (not (blue n1 n3)) dk_ec))))).
exact (fun nnsp2 : ((not (not sp2)) -> False) => (fun x0x5f598c1c0970 : ((not (blue n1 n3)) -> False) => (nnsp2 (fun psp : (not sp2) => (psp x0x5f598c1c0970))))).
Qed.
Definition sp3 : prop := ((not (blue n1 n4)) -> False).
Theorem deduction59 : (Prf_av_clause (av_if (not sp3) (dk_acl (dk_cl (dk_cons (not (blue n1 n4)) dk_ec))))).
exact (fun nnsp3 : ((not (not sp3)) -> False) => (fun x0x5f598c1c0930 : ((not (blue n1 n4)) -> False) => (nnsp3 (fun psp : (not sp3) => (psp x0x5f598c1c0930))))).
Qed.
Definition sp4 : prop := ((not (blue n1 n5)) -> False).
Theorem deduction63 : (Prf_av_clause (av_if (not sp4) (dk_acl (dk_cl (dk_cons (not (blue n1 n5)) dk_ec))))).
exact (fun nnsp4 : ((not (not sp4)) -> False) => (fun x0x5f598c1c08f0 : ((not (blue n1 n5)) -> False) => (nnsp4 (fun psp : (not sp4) => (psp x0x5f598c1c08f0))))).
Qed.
Definition sp5 : prop := ((not (blue n1 n6)) -> False).
Theorem deduction67 : (Prf_av_clause (av_if (not sp5) (dk_acl (dk_cl (dk_cons (not (blue n1 n6)) dk_ec))))).
exact (fun nnsp5 : ((not (not sp5)) -> False) => (fun x0x5f598c1c08b0 : ((not (blue n1 n6)) -> False) => (nnsp5 (fun psp : (not sp5) => (psp x0x5f598c1c08b0))))).
Qed.
Definition sp6 : prop := ((not (blue n2 n3)) -> False).
Theorem deduction71 : (Prf_av_clause (av_if (not sp6) (dk_acl (dk_cl (dk_cons (not (blue n2 n3)) dk_ec))))).
exact (fun nnsp6 : ((not (not sp6)) -> False) => (fun x0x5f598c1c0870 : ((not (blue n2 n3)) -> False) => (nnsp6 (fun psp : (not sp6) => (psp x0x5f598c1c0870))))).
Qed.
Definition sp7 : prop := ((not (blue n2 n4)) -> False).
Theorem deduction75 : (Prf_av_clause (av_if (not sp7) (dk_acl (dk_cl (dk_cons (not (blue n2 n4)) dk_ec))))).
exact (fun nnsp7 : ((not (not sp7)) -> False) => (fun x0x5f598c1c0830 : ((not (blue n2 n4)) -> False) => (nnsp7 (fun psp : (not sp7) => (psp x0x5f598c1c0830))))).
Qed.
Definition sp8 : prop := ((not (blue n2 n5)) -> False).
Theorem deduction79 : (Prf_av_clause (av_if (not sp8) (dk_acl (dk_cl (dk_cons (not (blue n2 n5)) dk_ec))))).
exact (fun nnsp8 : ((not (not sp8)) -> False) => (fun x0x5f598c1c07f0 : ((not (blue n2 n5)) -> False) => (nnsp8 (fun psp : (not sp8) => (psp x0x5f598c1c07f0))))).
Qed.
Definition sp9 : prop := ((not (blue n2 n6)) -> False).
Theorem deduction83 : (Prf_av_clause (av_if (not sp9) (dk_acl (dk_cl (dk_cons (not (blue n2 n6)) dk_ec))))).
exact (fun nnsp9 : ((not (not sp9)) -> False) => (fun x0x5f598c1c07b0 : ((not (blue n2 n6)) -> False) => (nnsp9 (fun psp : (not sp9) => (psp x0x5f598c1c07b0))))).
Qed.
Definition sp10 : prop := ((not (blue n3 n4)) -> False).
Theorem deduction87 : (Prf_av_clause (av_if (not sp10) (dk_acl (dk_cl (dk_cons (not (blue n3 n4)) dk_ec))))).
exact (fun nnsp10 : ((not (not sp10)) -> False) => (fun x0x5f598c1c0770 : ((not (blue n3 n4)) -> False) => (nnsp10 (fun psp : (not sp10) => (psp x0x5f598c1c0770))))).
Qed.
Definition sp11 : prop := ((not (blue n3 n5)) -> False).
Theorem deduction91 : (Prf_av_clause (av_if (not sp11) (dk_acl (dk_cl (dk_cons (not (blue n3 n5)) dk_ec))))).
exact (fun nnsp11 : ((not (not sp11)) -> False) => (fun x0x5f598c1c0730 : ((not (blue n3 n5)) -> False) => (nnsp11 (fun psp : (not sp11) => (psp x0x5f598c1c0730))))).
Qed.
Definition sp12 : prop := ((not (blue n3 n6)) -> False).
Theorem deduction95 : (Prf_av_clause (av_if (not sp12) (dk_acl (dk_cl (dk_cons (not (blue n3 n6)) dk_ec))))).
exact (fun nnsp12 : ((not (not sp12)) -> False) => (fun x0x5f598c1c06f0 : ((not (blue n3 n6)) -> False) => (nnsp12 (fun psp : (not sp12) => (psp x0x5f598c1c06f0))))).
Qed.
Definition sp13 : prop := ((not (blue n4 n5)) -> False).
Theorem deduction99 : (Prf_av_clause (av_if (not sp13) (dk_acl (dk_cl (dk_cons (not (blue n4 n5)) dk_ec))))).
exact (fun nnsp13 : ((not (not sp13)) -> False) => (fun x0x5f598c1c06b0 : ((not (blue n4 n5)) -> False) => (nnsp13 (fun psp : (not sp13) => (psp x0x5f598c1c06b0))))).
Qed.
Definition sp14 : prop := ((not (blue n4 n6)) -> False).
Theorem deduction103 : (Prf_av_clause (av_if (not sp14) (dk_acl (dk_cl (dk_cons (not (blue n4 n6)) dk_ec))))).
exact (fun nnsp14 : ((not (not sp14)) -> False) => (fun x0x5f598c1c0670 : ((not (blue n4 n6)) -> False) => (nnsp14 (fun psp : (not sp14) => (psp x0x5f598c1c0670))))).
Qed.
Definition sp15 : prop := ((not (blue n5 n6)) -> False).
Theorem deduction107 : (Prf_av_clause (av_if (not sp15) (dk_acl (dk_cl (dk_cons (not (blue n5 n6)) dk_ec))))).
exact (fun nnsp15 : ((not (not sp15)) -> False) => (fun x0x5f598c1c0630 : ((not (blue n5 n6)) -> False) => (nnsp15 (fun psp : (not sp15) => (psp x0x5f598c1c0630))))).
Qed.
Theorem deduction108 : (Prf_av_clause (dk_acl (dk_cl (dk_cons (not sp15) (dk_cons (not sp14) (dk_cons (not sp13) (dk_cons (not sp12) (dk_cons (not sp11) (dk_cons (not sp10) (dk_cons (not sp9) (dk_cons (not sp8) (dk_cons (not sp7) (dk_cons (not sp6) (dk_cons (not sp5) (dk_cons (not sp4) (dk_cons (not sp3) (dk_cons (not sp2) (dk_cons (not sp1) dk_ec)))))))))))))))))).
exact (fun nnsp15 : ((not sp15) -> False) => (fun nnsp14 : ((not sp14) -> False) => (fun nnsp13 : ((not sp13) -> False) => (fun nnsp12 : ((not sp12) -> False) => (fun nnsp11 : ((not sp11) -> False) => (fun nnsp10 : ((not sp10) -> False) => (fun nnsp9 : ((not sp9) -> False) => (fun nnsp8 : ((not sp8) -> False) => (fun nnsp7 : ((not sp7) -> False) => (fun nnsp6 : ((not sp6) -> False) => (fun nnsp5 : ((not sp5) -> False) => (fun nnsp4 : ((not sp4) -> False) => (fun nnsp3 : ((not sp3) -> False) => (fun nnsp2 : ((not sp2) -> False) => (fun nnsp1 : ((not sp1) -> False) => (nnsp15 (fun x0x5f598c1c0630 : ((not (blue n5 n6)) -> False) => (nnsp14 (fun x0x5f598c1c0670 : ((not (blue n4 n6)) -> False) => (nnsp13 (fun x0x5f598c1c06b0 : ((not (blue n4 n5)) -> False) => (nnsp12 (fun x0x5f598c1c06f0 : ((not (blue n3 n6)) -> False) => (nnsp11 (fun x0x5f598c1c0730 : ((not (blue n3 n5)) -> False) => (nnsp10 (fun x0x5f598c1c0770 : ((not (blue n3 n4)) -> False) => (nnsp9 (fun x0x5f598c1c07b0 : ((not (blue n2 n6)) -> False) => (nnsp8 (fun x0x5f598c1c07f0 : ((not (blue n2 n5)) -> False) => (nnsp7 (fun x0x5f598c1c0830 : ((not (blue n2 n4)) -> False) => (nnsp6 (fun x0x5f598c1c0870 : ((not (blue n2 n3)) -> False) => (nnsp5 (fun x0x5f598c1c08b0 : ((not (blue n1 n6)) -> False) => (nnsp4 (fun x0x5f598c1c08f0 : ((not (blue n1 n5)) -> False) => (nnsp3 (fun x0x5f598c1c0930 : ((not (blue n1 n4)) -> False) => (nnsp2 (fun x0x5f598c1c0970 : ((not (blue n1 n3)) -> False) => (nnsp1 (fun x0x5f598c1c09b0 : ((not (blue n1 n2)) -> False) => (deduction47 x0x5f598c1c0630 x0x5f598c1c0670 x0x5f598c1c06b0 x0x5f598c1c06f0 x0x5f598c1c0730 x0x5f598c1c0770 x0x5f598c1c07b0 x0x5f598c1c07f0 x0x5f598c1c0830 x0x5f598c1c0870 x0x5f598c1c08b0 x0x5f598c1c08f0 x0x5f598c1c0930 x0x5f598c1c0970 x0x5f598c1c09b0)))))))))))))))))))))))))))))))))))))))))))))).
Qed.
Theorem deduction109 : (dk_cons (red n1 v0) dk_ec).
exact (fun x0x5f598c1bf170 : ((red n1 v0) -> False) => (deduction15 v0 n1 (fun tnp : (not (red v0 n1)) => (deduction19 (fun tp : (red v0 n1) => (tnp tp)))) x0x5f598c1bf170)).
Qed.
Theorem deduction110 : (dk_cons (red n2 v0) dk_ec).
exact (fun x0x5f598c1bfe30 : ((red n2 v0) -> False) => (deduction15 v0 n2 (fun tnp : (not (red v0 n2)) => (deduction20 (fun tp : (red v0 n2) => (tnp tp)))) x0x5f598c1bfe30)).
Qed.
Theorem deduction111 : (dk_cons (red n3 v0) dk_ec).
exact (fun x0x5f598c1bfdf0 : ((red n3 v0) -> False) => (deduction15 v0 n3 (fun tnp : (not (red v0 n3)) => (deduction21 (fun tp : (red v0 n3) => (tnp tp)))) x0x5f598c1bfdf0)).
Qed.
Theorem deduction112 : (dk_cons (red n4 v0) dk_ec).
exact (fun x0x5f598c1bf2b0 : ((red n4 v0) -> False) => (deduction15 v0 n4 (fun tnp : (not (red v0 n4)) => (deduction22 (fun tp : (red v0 n4) => (tnp tp)))) x0x5f598c1bf2b0)).
Qed.
Theorem deduction113 : (dk_cons (red n5 v0) dk_ec).
exact (fun x0x5f598c1bfdb0 : ((red n5 v0) -> False) => (deduction15 v0 n5 (fun tnp : (not (red v0 n5)) => (deduction23 (fun tp : (red v0 n5) => (tnp tp)))) x0x5f598c1bfdb0)).
Qed.
Theorem deduction117 : (Prf_av_clause (av_if (not sp1) (dk_acl (dk_cl (dk_cons (red n1 n2) (dk_cons (n1 = n2) dk_ec)))))).
exact (fun nnsp1 : ((not (not sp1)) -> False) => (fun x0x5f598c1bd370 : ((red n1 n2) -> False) => (fun x0x5f598c1be6b0 : ((n1 = n2) -> False) => (deduction18 n1 n2 (fun tp : (blue n1 n2) => (deduction51 nnsp1 (fun tnp : (not (blue n1 n2)) => (tnp tp)))) x0x5f598c1bd370 x0x5f598c1be6b0)))).
Qed.
Theorem deduction121 : (Prf_av_clause (av_if (not sp1) (dk_acl (dk_cl (dk_cons (red n1 n2) dk_ec))))).
exact (fun nnsp1 : ((not (not sp1)) -> False) => (fun x0x5f598c1bd370 : ((red n1 n2) -> False) => (deduction117 nnsp1 x0x5f598c1bd370 (fun tp : (n1 = n2) => (deduction31 (fun tnp : (not (n1 = n2)) => (tnp tp))))))).
Qed.
Theorem deduction125 : (forall x0 : set, (dk_cons (not (red x0 n3)) (dk_cons (not (red x0 v0)) dk_ec))).
exact (fun x0 : set => (fun x0x5f598c1bf8b0 : ((not (red x0 n3)) -> False) => (fun x0x5f598c1bd4f0 : ((not (red x0 v0)) -> False) => (deduction46 x0 v0 n3 (fun tnp : (not (red v0 n3)) => (deduction21 (fun tp : (red v0 n3) => (tnp tp)))) x0x5f598c1bf8b0 x0x5f598c1bd4f0)))).
Qed.
Theorem deduction126 : (forall x0 : set, (dk_cons (not (red x0 n4)) (dk_cons (not (red x0 v0)) dk_ec))).
exact (fun x0 : set => (fun x0x5f598c1bfcf0 : ((not (red x0 n4)) -> False) => (fun x0x5f598c1bd4f0 : ((not (red x0 v0)) -> False) => (deduction46 x0 v0 n4 (fun tnp : (not (red v0 n4)) => (deduction22 (fun tp : (red v0 n4) => (tnp tp)))) x0x5f598c1bfcf0 x0x5f598c1bd4f0)))).
Qed.
Theorem deduction127 : (forall x0 : set, (dk_cons (not (red x0 n5)) (dk_cons (not (red x0 v0)) dk_ec))).
exact (fun x0 : set => (fun x0x5f598c1bfcb0 : ((not (red x0 n5)) -> False) => (fun x0x5f598c1bd4f0 : ((not (red x0 v0)) -> False) => (deduction46 x0 v0 n5 (fun tnp : (not (red v0 n5)) => (deduction23 (fun tp : (red v0 n5) => (tnp tp)))) x0x5f598c1bfcb0 x0x5f598c1bd4f0)))).
Qed.
Theorem deduction128 : (forall x0 : set, (dk_cons (not (red x0 n6)) (dk_cons (not (red x0 v0)) dk_ec))).
exact (fun x0 : set => (fun x0x5f598c1bf0f0 : ((not (red x0 n6)) -> False) => (fun x0x5f598c1bd4f0 : ((not (red x0 v0)) -> False) => (deduction46 x0 v0 n6 (fun tnp : (not (red v0 n6)) => (deduction24 (fun tp : (red v0 n6) => (tnp tp)))) x0x5f598c1bf0f0 x0x5f598c1bd4f0)))).
Qed.
Theorem deduction130 : (Prf_av_clause (av_if (not sp1) (dk_acl (forall x0 : set, (dk_cons (not (red x0 n2)) (dk_cons (not (red x0 n1)) dk_ec)))))).
exact (fun nnsp1 : ((not (not sp1)) -> False) => (fun x0 : set => (fun x0x5f598c1bd4b0 : ((not (red x0 n2)) -> False) => (fun x0x5f598c1bfe70 : ((not (red x0 n1)) -> False) => (deduction46 x0 n1 n2 (fun tnp : (not (red n1 n2)) => (deduction121 nnsp1 (fun tp : (red n1 n2) => (tnp tp)))) x0x5f598c1bd4b0 x0x5f598c1bfe70))))).
Qed.
Theorem deduction146 : (Prf_av_clause (av_if (not sp1) (dk_acl (dk_cl (dk_cons (not (red v0 n1)) dk_ec))))).
exact (fun nnsp1 : ((not (not sp1)) -> False) => (fun x0x5f598c1be470 : ((not (red v0 n1)) -> False) => (deduction130 nnsp1 v0 (fun tnp : (not (red v0 n2)) => (deduction20 (fun tp : (red v0 n2) => (tnp tp)))) x0x5f598c1be470))).
Qed.
Theorem deduction148 : (Prf_av_clause (av_if (not sp1) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp1 : ((not (not sp1)) -> False) => (deduction146 nnsp1 (fun tnp : (not (red v0 n1)) => (deduction19 (fun tp : (red v0 n1) => (tnp tp)))))).
Qed.
Theorem deduction149 : (Prf_av_clause (av_if (not sp1) (dk_acl (dk_cl dk_ec)))).
exact deduction148.
Qed.
Theorem deduction153 : (Prf_av_clause (av_if (not sp2) (dk_acl (dk_cl (dk_cons (red n1 n3) (dk_cons (n1 = n3) dk_ec)))))).
exact (fun nnsp2 : ((not (not sp2)) -> False) => (fun x0x5f598c1bcdb0 : ((red n1 n3) -> False) => (fun x0x5f598c1bfff0 : ((n1 = n3) -> False) => (deduction55 nnsp2 (fun tnp : (not (blue n1 n3)) => (deduction18 n1 n3 (fun tp : (blue n1 n3) => (tnp tp)) x0x5f598c1bcdb0 x0x5f598c1bfff0)))))).
Qed.
Theorem deduction154 : (Prf_av_clause (av_if (not sp2) (dk_acl (dk_cl (dk_cons (red n1 n3) dk_ec))))).
exact (fun nnsp2 : ((not (not sp2)) -> False) => (fun x0x5f598c1bcdb0 : ((red n1 n3) -> False) => (deduction153 nnsp2 x0x5f598c1bcdb0 (fun tp : (n1 = n3) => (deduction32 (fun tnp : (not (n1 = n3)) => (tnp tp))))))).
Qed.
Theorem deduction158 : (Prf_av_clause (av_if (not sp2) (dk_acl (dk_cl (dk_cons (not (red n1 v0)) dk_ec))))).
exact (fun nnsp2 : ((not (not sp2)) -> False) => (fun x0x5f598c1bd830 : ((not (red n1 v0)) -> False) => (deduction154 nnsp2 (fun tp : (red n1 n3) => (deduction125 n1 (fun tnp : (not (red n1 n3)) => (tnp tp)) x0x5f598c1bd830))))).
Qed.
Theorem deduction161 : (Prf_av_clause (av_if (not sp2) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp2 : ((not (not sp2)) -> False) => (deduction158 nnsp2 (fun tnp : (not (red n1 v0)) => (deduction109 (fun tp : (red n1 v0) => (tnp tp)))))).
Qed.
Theorem deduction162 : (Prf_av_clause (av_if (not sp2) (dk_acl (dk_cl dk_ec)))).
exact deduction161.
Qed.
Theorem deduction166 : (Prf_av_clause (av_if (not sp3) (dk_acl (dk_cl (dk_cons (red n1 n4) (dk_cons (n1 = n4) dk_ec)))))).
exact (fun nnsp3 : ((not (not sp3)) -> False) => (fun x0x5f598c1bc8f0 : ((red n1 n4) -> False) => (fun x0x5f598c1bffb0 : ((n1 = n4) -> False) => (deduction59 nnsp3 (fun tnp : (not (blue n1 n4)) => (deduction18 n1 n4 (fun tp : (blue n1 n4) => (tnp tp)) x0x5f598c1bc8f0 x0x5f598c1bffb0)))))).
Qed.
Theorem deduction167 : (Prf_av_clause (av_if (not sp3) (dk_acl (dk_cl (dk_cons (red n1 n4) dk_ec))))).
exact (fun nnsp3 : ((not (not sp3)) -> False) => (fun x0x5f598c1bc8f0 : ((red n1 n4) -> False) => (deduction166 nnsp3 x0x5f598c1bc8f0 (fun tp : (n1 = n4) => (deduction33 (fun tnp : (not (n1 = n4)) => (tnp tp))))))).
Qed.
Theorem deduction171 : (Prf_av_clause (av_if (not sp3) (dk_acl (dk_cl (dk_cons (not (red n1 v0)) dk_ec))))).
exact (fun nnsp3 : ((not (not sp3)) -> False) => (fun x0x5f598c1bd830 : ((not (red n1 v0)) -> False) => (deduction167 nnsp3 (fun tp : (red n1 n4) => (deduction126 n1 (fun tnp : (not (red n1 n4)) => (tnp tp)) x0x5f598c1bd830))))).
Qed.
Theorem deduction174 : (Prf_av_clause (av_if (not sp3) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp3 : ((not (not sp3)) -> False) => (deduction171 nnsp3 (fun tnp : (not (red n1 v0)) => (deduction109 (fun tp : (red n1 v0) => (tnp tp)))))).
Qed.
Theorem deduction175 : (Prf_av_clause (av_if (not sp3) (dk_acl (dk_cl dk_ec)))).
exact deduction174.
Qed.
Theorem deduction179 : (Prf_av_clause (av_if (not sp4) (dk_acl (dk_cl (dk_cons (red n1 n5) (dk_cons (n1 = n5) dk_ec)))))).
exact (fun nnsp4 : ((not (not sp4)) -> False) => (fun x0x5f598c1bc5f0 : ((red n1 n5) -> False) => (fun x0x5f598c1be5f0 : ((n1 = n5) -> False) => (deduction63 nnsp4 (fun tnp : (not (blue n1 n5)) => (deduction18 n1 n5 (fun tp : (blue n1 n5) => (tnp tp)) x0x5f598c1bc5f0 x0x5f598c1be5f0)))))).
Qed.
Theorem deduction180 : (Prf_av_clause (av_if (not sp4) (dk_acl (dk_cl (dk_cons (red n1 n5) dk_ec))))).
exact (fun nnsp4 : ((not (not sp4)) -> False) => (fun x0x5f598c1bc5f0 : ((red n1 n5) -> False) => (deduction179 nnsp4 x0x5f598c1bc5f0 (fun tp : (n1 = n5) => (deduction34 (fun tnp : (not (n1 = n5)) => (tnp tp))))))).
Qed.
Theorem deduction184 : (Prf_av_clause (av_if (not sp4) (dk_acl (dk_cl (dk_cons (not (red n1 v0)) dk_ec))))).
exact (fun nnsp4 : ((not (not sp4)) -> False) => (fun x0x5f598c1bd830 : ((not (red n1 v0)) -> False) => (deduction180 nnsp4 (fun tp : (red n1 n5) => (deduction127 n1 (fun tnp : (not (red n1 n5)) => (tnp tp)) x0x5f598c1bd830))))).
Qed.
Theorem deduction187 : (Prf_av_clause (av_if (not sp4) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp4 : ((not (not sp4)) -> False) => (deduction184 nnsp4 (fun tnp : (not (red n1 v0)) => (deduction109 (fun tp : (red n1 v0) => (tnp tp)))))).
Qed.
Theorem deduction188 : (Prf_av_clause (av_if (not sp4) (dk_acl (dk_cl dk_ec)))).
exact deduction187.
Qed.
Theorem deduction192 : (Prf_av_clause (av_if (not sp5) (dk_acl (dk_cl (dk_cons (red n1 n6) (dk_cons (n1 = n6) dk_ec)))))).
exact (fun nnsp5 : ((not (not sp5)) -> False) => (fun x0x5f598c1bc1f0 : ((red n1 n6) -> False) => (fun x0x5f598c1be670 : ((n1 = n6) -> False) => (deduction67 nnsp5 (fun tnp : (not (blue n1 n6)) => (deduction18 n1 n6 (fun tp : (blue n1 n6) => (tnp tp)) x0x5f598c1bc1f0 x0x5f598c1be670)))))).
Qed.
Theorem deduction193 : (Prf_av_clause (av_if (not sp5) (dk_acl (dk_cl (dk_cons (red n1 n6) dk_ec))))).
exact (fun nnsp5 : ((not (not sp5)) -> False) => (fun x0x5f598c1bc1f0 : ((red n1 n6) -> False) => (deduction192 nnsp5 x0x5f598c1bc1f0 (fun tp : (n1 = n6) => (deduction35 (fun tnp : (not (n1 = n6)) => (tnp tp))))))).
Qed.
Theorem deduction197 : (Prf_av_clause (av_if (not sp5) (dk_acl (dk_cl (dk_cons (not (red n1 v0)) dk_ec))))).
exact (fun nnsp5 : ((not (not sp5)) -> False) => (fun x0x5f598c1bd830 : ((not (red n1 v0)) -> False) => (deduction193 nnsp5 (fun tp : (red n1 n6) => (deduction128 n1 (fun tnp : (not (red n1 n6)) => (tnp tp)) x0x5f598c1bd830))))).
Qed.
Theorem deduction200 : (Prf_av_clause (av_if (not sp5) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp5 : ((not (not sp5)) -> False) => (deduction197 nnsp5 (fun tnp : (not (red n1 v0)) => (deduction109 (fun tp : (red n1 v0) => (tnp tp)))))).
Qed.
Theorem deduction201 : (Prf_av_clause (av_if (not sp5) (dk_acl (dk_cl dk_ec)))).
exact deduction200.
Qed.
Theorem deduction205 : (Prf_av_clause (av_if (not sp6) (dk_acl (dk_cl (dk_cons (red n2 n3) (dk_cons (n2 = n3) dk_ec)))))).
exact (fun nnsp6 : ((not (not sp6)) -> False) => (fun x0x5f598c1bbeb0 : ((red n2 n3) -> False) => (fun x0x5f598c1bfb70 : ((n2 = n3) -> False) => (deduction71 nnsp6 (fun tnp : (not (blue n2 n3)) => (deduction18 n2 n3 (fun tp : (blue n2 n3) => (tnp tp)) x0x5f598c1bbeb0 x0x5f598c1bfb70)))))).
Qed.
Theorem deduction206 : (Prf_av_clause (av_if (not sp6) (dk_acl (dk_cl (dk_cons (red n2 n3) dk_ec))))).
exact (fun nnsp6 : ((not (not sp6)) -> False) => (fun x0x5f598c1bbeb0 : ((red n2 n3) -> False) => (deduction205 nnsp6 x0x5f598c1bbeb0 (fun tp : (n2 = n3) => (deduction36 (fun tnp : (not (n2 = n3)) => (tnp tp))))))).
Qed.
Theorem deduction210 : (Prf_av_clause (av_if (not sp6) (dk_acl (dk_cl (dk_cons (not (red n2 v0)) dk_ec))))).
exact (fun nnsp6 : ((not (not sp6)) -> False) => (fun x0x5f598c1bd8f0 : ((not (red n2 v0)) -> False) => (deduction206 nnsp6 (fun tp : (red n2 n3) => (deduction125 n2 (fun tnp : (not (red n2 n3)) => (tnp tp)) x0x5f598c1bd8f0))))).
Qed.
Theorem deduction213 : (Prf_av_clause (av_if (not sp6) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp6 : ((not (not sp6)) -> False) => (deduction210 nnsp6 (fun tnp : (not (red n2 v0)) => (deduction110 (fun tp : (red n2 v0) => (tnp tp)))))).
Qed.
Theorem deduction214 : (Prf_av_clause (av_if (not sp6) (dk_acl (dk_cl dk_ec)))).
exact deduction213.
Qed.
Theorem deduction218 : (Prf_av_clause (av_if (not sp7) (dk_acl (dk_cl (dk_cons (red n2 n4) (dk_cons (n2 = n4) dk_ec)))))).
exact (fun nnsp7 : ((not (not sp7)) -> False) => (fun x0x5f598c1bbaf0 : ((red n2 n4) -> False) => (fun x0x5f598c1bfb30 : ((n2 = n4) -> False) => (deduction75 nnsp7 (fun tnp : (not (blue n2 n4)) => (deduction18 n2 n4 (fun tp : (blue n2 n4) => (tnp tp)) x0x5f598c1bbaf0 x0x5f598c1bfb30)))))).
Qed.
Theorem deduction219 : (Prf_av_clause (av_if (not sp7) (dk_acl (dk_cl (dk_cons (red n2 n4) dk_ec))))).
exact (fun nnsp7 : ((not (not sp7)) -> False) => (fun x0x5f598c1bbaf0 : ((red n2 n4) -> False) => (deduction218 nnsp7 x0x5f598c1bbaf0 (fun tp : (n2 = n4) => (deduction37 (fun tnp : (not (n2 = n4)) => (tnp tp))))))).
Qed.
Theorem deduction223 : (Prf_av_clause (av_if (not sp7) (dk_acl (dk_cl (dk_cons (not (red n2 v0)) dk_ec))))).
exact (fun nnsp7 : ((not (not sp7)) -> False) => (fun x0x5f598c1bd8f0 : ((not (red n2 v0)) -> False) => (deduction219 nnsp7 (fun tp : (red n2 n4) => (deduction126 n2 (fun tnp : (not (red n2 n4)) => (tnp tp)) x0x5f598c1bd8f0))))).
Qed.
Theorem deduction226 : (Prf_av_clause (av_if (not sp7) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp7 : ((not (not sp7)) -> False) => (deduction223 nnsp7 (fun tnp : (not (red n2 v0)) => (deduction110 (fun tp : (red n2 v0) => (tnp tp)))))).
Qed.
Theorem deduction227 : (Prf_av_clause (av_if (not sp7) (dk_acl (dk_cl dk_ec)))).
exact deduction226.
Qed.
Theorem deduction231 : (Prf_av_clause (av_if (not sp8) (dk_acl (dk_cl (dk_cons (red n2 n5) (dk_cons (n2 = n5) dk_ec)))))).
exact (fun nnsp8 : ((not (not sp8)) -> False) => (fun x0x5f598c1bb670 : ((red n2 n5) -> False) => (fun x0x5f598c1bfaf0 : ((n2 = n5) -> False) => (deduction79 nnsp8 (fun tnp : (not (blue n2 n5)) => (deduction18 n2 n5 (fun tp : (blue n2 n5) => (tnp tp)) x0x5f598c1bb670 x0x5f598c1bfaf0)))))).
Qed.
Theorem deduction232 : (Prf_av_clause (av_if (not sp8) (dk_acl (dk_cl (dk_cons (red n2 n5) dk_ec))))).
exact (fun nnsp8 : ((not (not sp8)) -> False) => (fun x0x5f598c1bb670 : ((red n2 n5) -> False) => (deduction231 nnsp8 x0x5f598c1bb670 (fun tp : (n2 = n5) => (deduction38 (fun tnp : (not (n2 = n5)) => (tnp tp))))))).
Qed.
Theorem deduction236 : (Prf_av_clause (av_if (not sp8) (dk_acl (dk_cl (dk_cons (not (red n2 v0)) dk_ec))))).
exact (fun nnsp8 : ((not (not sp8)) -> False) => (fun x0x5f598c1bd8f0 : ((not (red n2 v0)) -> False) => (deduction232 nnsp8 (fun tp : (red n2 n5) => (deduction127 n2 (fun tnp : (not (red n2 n5)) => (tnp tp)) x0x5f598c1bd8f0))))).
Qed.
Theorem deduction239 : (Prf_av_clause (av_if (not sp8) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp8 : ((not (not sp8)) -> False) => (deduction236 nnsp8 (fun tnp : (not (red n2 v0)) => (deduction110 (fun tp : (red n2 v0) => (tnp tp)))))).
Qed.
Theorem deduction240 : (Prf_av_clause (av_if (not sp8) (dk_acl (dk_cl dk_ec)))).
exact deduction239.
Qed.
Theorem deduction244 : (Prf_av_clause (av_if (not sp9) (dk_acl (dk_cl (dk_cons (red n2 n6) (dk_cons (n2 = n6) dk_ec)))))).
exact (fun nnsp9 : ((not (not sp9)) -> False) => (fun x0x5f598c1bb2b0 : ((red n2 n6) -> False) => (fun x0x5f598c1bfa30 : ((n2 = n6) -> False) => (deduction83 nnsp9 (fun tnp : (not (blue n2 n6)) => (deduction18 n2 n6 (fun tp : (blue n2 n6) => (tnp tp)) x0x5f598c1bb2b0 x0x5f598c1bfa30)))))).
Qed.
Theorem deduction245 : (Prf_av_clause (av_if (not sp9) (dk_acl (dk_cl (dk_cons (red n2 n6) dk_ec))))).
exact (fun nnsp9 : ((not (not sp9)) -> False) => (fun x0x5f598c1bb2b0 : ((red n2 n6) -> False) => (deduction244 nnsp9 x0x5f598c1bb2b0 (fun tp : (n2 = n6) => (deduction39 (fun tnp : (not (n2 = n6)) => (tnp tp))))))).
Qed.
Theorem deduction249 : (Prf_av_clause (av_if (not sp9) (dk_acl (dk_cl (dk_cons (not (red n2 v0)) dk_ec))))).
exact (fun nnsp9 : ((not (not sp9)) -> False) => (fun x0x5f598c1bd8f0 : ((not (red n2 v0)) -> False) => (deduction245 nnsp9 (fun tp : (red n2 n6) => (deduction128 n2 (fun tnp : (not (red n2 n6)) => (tnp tp)) x0x5f598c1bd8f0))))).
Qed.
Theorem deduction252 : (Prf_av_clause (av_if (not sp9) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp9 : ((not (not sp9)) -> False) => (deduction249 nnsp9 (fun tnp : (not (red n2 v0)) => (deduction110 (fun tp : (red n2 v0) => (tnp tp)))))).
Qed.
Theorem deduction253 : (Prf_av_clause (av_if (not sp9) (dk_acl (dk_cl dk_ec)))).
exact deduction252.
Qed.
Theorem deduction257 : (Prf_av_clause (av_if (not sp10) (dk_acl (dk_cl (dk_cons (red n3 n4) (dk_cons (n3 = n4) dk_ec)))))).
exact (fun nnsp10 : ((not (not sp10)) -> False) => (fun x0x5f598c1bae70 : ((red n3 n4) -> False) => (fun x0x5f598c1bf9b0 : ((n3 = n4) -> False) => (deduction87 nnsp10 (fun tnp : (not (blue n3 n4)) => (deduction18 n3 n4 (fun tp : (blue n3 n4) => (tnp tp)) x0x5f598c1bae70 x0x5f598c1bf9b0)))))).
Qed.
Theorem deduction258 : (Prf_av_clause (av_if (not sp10) (dk_acl (dk_cl (dk_cons (red n3 n4) dk_ec))))).
exact (fun nnsp10 : ((not (not sp10)) -> False) => (fun x0x5f598c1bae70 : ((red n3 n4) -> False) => (deduction257 nnsp10 x0x5f598c1bae70 (fun tp : (n3 = n4) => (deduction40 (fun tnp : (not (n3 = n4)) => (tnp tp))))))).
Qed.
Theorem deduction262 : (Prf_av_clause (av_if (not sp10) (dk_acl (dk_cl (dk_cons (not (red n3 v0)) dk_ec))))).
exact (fun nnsp10 : ((not (not sp10)) -> False) => (fun x0x5f598c1bd9b0 : ((not (red n3 v0)) -> False) => (deduction258 nnsp10 (fun tp : (red n3 n4) => (deduction126 n3 (fun tnp : (not (red n3 n4)) => (tnp tp)) x0x5f598c1bd9b0))))).
Qed.
Theorem deduction265 : (Prf_av_clause (av_if (not sp10) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp10 : ((not (not sp10)) -> False) => (deduction262 nnsp10 (fun tnp : (not (red n3 v0)) => (deduction111 (fun tp : (red n3 v0) => (tnp tp)))))).
Qed.
Theorem deduction266 : (Prf_av_clause (av_if (not sp10) (dk_acl (dk_cl dk_ec)))).
exact deduction265.
Qed.
Theorem deduction270 : (Prf_av_clause (av_if (not sp11) (dk_acl (dk_cl (dk_cons (red n3 n5) (dk_cons (n3 = n5) dk_ec)))))).
exact (fun nnsp11 : ((not (not sp11)) -> False) => (fun x0x5f598c1baa70 : ((red n3 n5) -> False) => (fun x0x5f598c1bf970 : ((n3 = n5) -> False) => (deduction91 nnsp11 (fun tnp : (not (blue n3 n5)) => (deduction18 n3 n5 (fun tp : (blue n3 n5) => (tnp tp)) x0x5f598c1baa70 x0x5f598c1bf970)))))).
Qed.
Theorem deduction271 : (Prf_av_clause (av_if (not sp11) (dk_acl (dk_cl (dk_cons (red n3 n5) dk_ec))))).
exact (fun nnsp11 : ((not (not sp11)) -> False) => (fun x0x5f598c1baa70 : ((red n3 n5) -> False) => (deduction270 nnsp11 x0x5f598c1baa70 (fun tp : (n3 = n5) => (deduction41 (fun tnp : (not (n3 = n5)) => (tnp tp))))))).
Qed.
Theorem deduction275 : (Prf_av_clause (av_if (not sp11) (dk_acl (dk_cl (dk_cons (not (red n3 v0)) dk_ec))))).
exact (fun nnsp11 : ((not (not sp11)) -> False) => (fun x0x5f598c1bd9b0 : ((not (red n3 v0)) -> False) => (deduction271 nnsp11 (fun tp : (red n3 n5) => (deduction127 n3 (fun tnp : (not (red n3 n5)) => (tnp tp)) x0x5f598c1bd9b0))))).
Qed.
Theorem deduction278 : (Prf_av_clause (av_if (not sp11) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp11 : ((not (not sp11)) -> False) => (deduction275 nnsp11 (fun tnp : (not (red n3 v0)) => (deduction111 (fun tp : (red n3 v0) => (tnp tp)))))).
Qed.
Theorem deduction279 : (Prf_av_clause (av_if (not sp11) (dk_acl (dk_cl dk_ec)))).
exact deduction278.
Qed.
Theorem deduction283 : (Prf_av_clause (av_if (not sp12) (dk_acl (dk_cl (dk_cons (red n3 n6) (dk_cons (n3 = n6) dk_ec)))))).
exact (fun nnsp12 : ((not (not sp12)) -> False) => (fun x0x5f598c1ba670 : ((red n3 n6) -> False) => (fun x0x5f598c1bf8f0 : ((n3 = n6) -> False) => (deduction95 nnsp12 (fun tnp : (not (blue n3 n6)) => (deduction18 n3 n6 (fun tp : (blue n3 n6) => (tnp tp)) x0x5f598c1ba670 x0x5f598c1bf8f0)))))).
Qed.
Theorem deduction284 : (Prf_av_clause (av_if (not sp12) (dk_acl (dk_cl (dk_cons (red n3 n6) dk_ec))))).
exact (fun nnsp12 : ((not (not sp12)) -> False) => (fun x0x5f598c1ba670 : ((red n3 n6) -> False) => (deduction283 nnsp12 x0x5f598c1ba670 (fun tp : (n3 = n6) => (deduction42 (fun tnp : (not (n3 = n6)) => (tnp tp))))))).
Qed.
Theorem deduction288 : (Prf_av_clause (av_if (not sp12) (dk_acl (dk_cl (dk_cons (not (red n3 v0)) dk_ec))))).
exact (fun nnsp12 : ((not (not sp12)) -> False) => (fun x0x5f598c1bd9b0 : ((not (red n3 v0)) -> False) => (deduction284 nnsp12 (fun tp : (red n3 n6) => (deduction128 n3 (fun tnp : (not (red n3 n6)) => (tnp tp)) x0x5f598c1bd9b0))))).
Qed.
Theorem deduction291 : (Prf_av_clause (av_if (not sp12) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp12 : ((not (not sp12)) -> False) => (deduction288 nnsp12 (fun tnp : (not (red n3 v0)) => (deduction111 (fun tp : (red n3 v0) => (tnp tp)))))).
Qed.
Theorem deduction292 : (Prf_av_clause (av_if (not sp12) (dk_acl (dk_cl dk_ec)))).
exact deduction291.
Qed.
Theorem deduction296 : (Prf_av_clause (av_if (not sp13) (dk_acl (dk_cl (dk_cons (red n4 n5) (dk_cons (n4 = n5) dk_ec)))))).
exact (fun nnsp13 : ((not (not sp13)) -> False) => (fun x0x5f598c1ba2b0 : ((red n4 n5) -> False) => (fun x0x5f598c1be530 : ((n4 = n5) -> False) => (deduction99 nnsp13 (fun tnp : (not (blue n4 n5)) => (deduction18 n4 n5 (fun tp : (blue n4 n5) => (tnp tp)) x0x5f598c1ba2b0 x0x5f598c1be530)))))).
Qed.
Theorem deduction297 : (Prf_av_clause (av_if (not sp13) (dk_acl (dk_cl (dk_cons (red n4 n5) dk_ec))))).
exact (fun nnsp13 : ((not (not sp13)) -> False) => (fun x0x5f598c1ba2b0 : ((red n4 n5) -> False) => (deduction296 nnsp13 x0x5f598c1ba2b0 (fun tp : (n4 = n5) => (deduction43 (fun tnp : (not (n4 = n5)) => (tnp tp))))))).
Qed.
Theorem deduction301 : (Prf_av_clause (av_if (not sp13) (dk_acl (dk_cl (dk_cons (not (red n4 v0)) dk_ec))))).
exact (fun nnsp13 : ((not (not sp13)) -> False) => (fun x0x5f598c1bda30 : ((not (red n4 v0)) -> False) => (deduction297 nnsp13 (fun tp : (red n4 n5) => (deduction127 n4 (fun tnp : (not (red n4 n5)) => (tnp tp)) x0x5f598c1bda30))))).
Qed.
Theorem deduction304 : (Prf_av_clause (av_if (not sp13) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp13 : ((not (not sp13)) -> False) => (deduction301 nnsp13 (fun tnp : (not (red n4 v0)) => (deduction112 (fun tp : (red n4 v0) => (tnp tp)))))).
Qed.
Theorem deduction305 : (Prf_av_clause (av_if (not sp13) (dk_acl (dk_cl dk_ec)))).
exact deduction304.
Qed.
Theorem deduction309 : (Prf_av_clause (av_if (not sp14) (dk_acl (dk_cl (dk_cons (red n4 n6) (dk_cons (n4 = n6) dk_ec)))))).
exact (fun nnsp14 : ((not (not sp14)) -> False) => (fun x0x5f598c1b9f70 : ((red n4 n6) -> False) => (fun x0x5f598c1be570 : ((n4 = n6) -> False) => (deduction103 nnsp14 (fun tnp : (not (blue n4 n6)) => (deduction18 n4 n6 (fun tp : (blue n4 n6) => (tnp tp)) x0x5f598c1b9f70 x0x5f598c1be570)))))).
Qed.
Theorem deduction310 : (Prf_av_clause (av_if (not sp14) (dk_acl (dk_cl (dk_cons (red n4 n6) dk_ec))))).
exact (fun nnsp14 : ((not (not sp14)) -> False) => (fun x0x5f598c1b9f70 : ((red n4 n6) -> False) => (deduction309 nnsp14 x0x5f598c1b9f70 (fun tp : (n4 = n6) => (deduction44 (fun tnp : (not (n4 = n6)) => (tnp tp))))))).
Qed.
Theorem deduction314 : (Prf_av_clause (av_if (not sp14) (dk_acl (dk_cl (dk_cons (not (red n4 v0)) dk_ec))))).
exact (fun nnsp14 : ((not (not sp14)) -> False) => (fun x0x5f598c1bda30 : ((not (red n4 v0)) -> False) => (deduction310 nnsp14 (fun tp : (red n4 n6) => (deduction128 n4 (fun tnp : (not (red n4 n6)) => (tnp tp)) x0x5f598c1bda30))))).
Qed.
Theorem deduction317 : (Prf_av_clause (av_if (not sp14) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp14 : ((not (not sp14)) -> False) => (deduction314 nnsp14 (fun tnp : (not (red n4 v0)) => (deduction112 (fun tp : (red n4 v0) => (tnp tp)))))).
Qed.
Theorem deduction318 : (Prf_av_clause (av_if (not sp14) (dk_acl (dk_cl dk_ec)))).
exact deduction317.
Qed.
Theorem deduction322 : (Prf_av_clause (av_if (not sp15) (dk_acl (dk_cl (dk_cons (red n5 n6) (dk_cons (n5 = n6) dk_ec)))))).
exact (fun nnsp15 : ((not (not sp15)) -> False) => (fun x0x5f598c1b9c30 : ((red n5 n6) -> False) => (fun x0x5f598c1be4b0 : ((n5 = n6) -> False) => (deduction107 nnsp15 (fun tnp : (not (blue n5 n6)) => (deduction18 n5 n6 (fun tp : (blue n5 n6) => (tnp tp)) x0x5f598c1b9c30 x0x5f598c1be4b0)))))).
Qed.
Theorem deduction323 : (Prf_av_clause (av_if (not sp15) (dk_acl (dk_cl (dk_cons (red n5 n6) dk_ec))))).
exact (fun nnsp15 : ((not (not sp15)) -> False) => (fun x0x5f598c1b9c30 : ((red n5 n6) -> False) => (deduction322 nnsp15 x0x5f598c1b9c30 (fun tp : (n5 = n6) => (deduction45 (fun tnp : (not (n5 = n6)) => (tnp tp))))))).
Qed.
Theorem deduction327 : (Prf_av_clause (av_if (not sp15) (dk_acl (dk_cl (dk_cons (not (red n5 v0)) dk_ec))))).
exact (fun nnsp15 : ((not (not sp15)) -> False) => (fun x0x5f598c1c0130 : ((not (red n5 v0)) -> False) => (deduction323 nnsp15 (fun tp : (red n5 n6) => (deduction128 n5 (fun tnp : (not (red n5 n6)) => (tnp tp)) x0x5f598c1c0130))))).
Qed.
Theorem deduction330 : (Prf_av_clause (av_if (not sp15) (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp15 : ((not (not sp15)) -> False) => (deduction327 nnsp15 (fun tnp : (not (red n5 v0)) => (deduction113 (fun tp : (red n5 v0) => (tnp tp)))))).
Qed.
Theorem deduction331 : (Prf_av_clause (av_if (not sp15) (dk_acl (dk_cl dk_ec)))).
exact deduction330.
Qed.
End DeduktiProof.
