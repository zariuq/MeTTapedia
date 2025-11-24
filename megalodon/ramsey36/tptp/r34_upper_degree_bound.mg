Section DeduktiProof.
Variable sK0 : set.
Variable sK1 : set.
Variable sK2 : set.
Variable sK3 : set.
Variable sK4 : set.
Variable adj : (set -> (set -> prop)).
Hypothesis axiom_1_adj_sym : (forall x0 : set, (forall x1 : set, ((adj x0 x1) -> (adj x1 x0)))).
Theorem deduction1 : (forall x0 : set, (forall x1 : set, ((adj x0 x1) -> (adj x1 x0)))).
exact axiom_1_adj_sym.
Qed.
Hypothesis axiom_3_triangle_free : (forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (adj x0 x1) (and (adj x1 x2) (adj x0 x2))))))).
Theorem deduction3 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (adj x0 x1) (and (adj x1 x2) (adj x0 x2))))))).
exact axiom_3_triangle_free.
Qed.
Hypothesis axiom_4_no_4_indep : (forall x3 : set, (forall x4 : set, (forall x5 : set, (forall x6 : set, ((and (not (x3 = x4)) (and (not (x3 = x5)) (and (not (x3 = x6)) (and (not (x4 = x5)) (and (not (x4 = x6)) (not (x5 = x6))))))) -> (or (adj x3 x4) (or (adj x3 x5) (or (adj x3 x6) (or (adj x4 x5) (or (adj x4 x6) (adj x5 x6))))))))))).
Theorem deduction4 : (forall x3 : set, (forall x4 : set, (forall x5 : set, (forall x6 : set, ((and (not (x3 = x4)) (and (not (x3 = x5)) (and (not (x3 = x6)) (and (not (x4 = x5)) (and (not (x4 = x6)) (not (x5 = x6))))))) -> (or (adj x3 x4) (or (adj x3 x5) (or (adj x3 x6) (or (adj x4 x5) (or (adj x4 x6) (adj x5 x6))))))))))).
exact axiom_4_no_4_indep.
Qed.
Hypothesis axiom_6_four_neighbors : (exists x7 : set, (exists x8 : set, (exists x9 : set, (exists x10 : set, (exists x11 : set, (and (not (x8 = x9)) (and (not (x8 = x10)) (and (not (x8 = x11)) (and (not (x9 = x10)) (and (not (x9 = x11)) (and (not (x10 = x11)) (and (not (x7 = x8)) (and (not (x7 = x9)) (and (not (x7 = x10)) (and (not (x7 = x11)) (and (adj x7 x8) (and (adj x7 x9) (and (adj x7 x10) (adj x7 x11))))))))))))))))))).
Theorem deduction6 : (exists x7 : set, (exists x8 : set, (exists x9 : set, (exists x10 : set, (exists x11 : set, (and (not (x8 = x9)) (and (not (x8 = x10)) (and (not (x8 = x11)) (and (not (x9 = x10)) (and (not (x9 = x11)) (and (not (x10 = x11)) (and (not (x7 = x8)) (and (not (x7 = x9)) (and (not (x7 = x10)) (and (not (x7 = x11)) (and (adj x7 x8) (and (adj x7 x9) (and (adj x7 x10) (adj x7 x11))))))))))))))))))).
exact axiom_6_four_neighbors.
Qed.
Hypothesis sorry9 : ((forall x3 : set, (forall x4 : set, (forall x5 : set, (forall x6 : set, ((and (not (x3 = x4)) (and (not (x3 = x5)) (and (not (x3 = x6)) (and (not (x4 = x5)) (and (not (x4 = x6)) (not (x5 = x6))))))) -> (or (adj x3 x4) (or (adj x3 x5) (or (adj x3 x6) (or (adj x4 x5) (or (adj x4 x6) (adj x5 x6))))))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, ((and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x1 = x2)) (and (not (x1 = x3)) (not (x2 = x3))))))) -> (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3)))))))))))).
Theorem deduction9 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, ((and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x1 = x2)) (and (not (x1 = x3)) (not (x2 = x3))))))) -> (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3))))))))))).
exact (sorry9 deduction4).
Qed.
Hypothesis sorry11 : ((exists x7 : set, (exists x8 : set, (exists x9 : set, (exists x10 : set, (exists x11 : set, (and (not (x8 = x9)) (and (not (x8 = x10)) (and (not (x8 = x11)) (and (not (x9 = x10)) (and (not (x9 = x11)) (and (not (x10 = x11)) (and (not (x7 = x8)) (and (not (x7 = x9)) (and (not (x7 = x10)) (and (not (x7 = x11)) (and (adj x7 x8) (and (adj x7 x9) (and (adj x7 x10) (adj x7 x11))))))))))))))))))) -> (exists x0 : set, (exists x1 : set, (exists x2 : set, (exists x3 : set, (exists x4 : set, (and (not (x1 = x2)) (and (not (x1 = x3)) (and (not (x1 = x4)) (and (not (x2 = x3)) (and (not (x2 = x4)) (and (not (x3 = x4)) (and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x0 = x4)) (and (adj x0 x1) (and (adj x0 x2) (and (adj x0 x3) (adj x0 x4)))))))))))))))))))).
Theorem deduction11 : (exists x0 : set, (exists x1 : set, (exists x2 : set, (exists x3 : set, (exists x4 : set, (and (not (x1 = x2)) (and (not (x1 = x3)) (and (not (x1 = x4)) (and (not (x2 = x3)) (and (not (x2 = x4)) (and (not (x3 = x4)) (and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x0 = x4)) (and (adj x0 x1) (and (adj x0 x2) (and (adj x0 x3) (adj x0 x4))))))))))))))))))).
exact (sorry11 deduction6).
Qed.
Hypothesis sorry13 : ((forall x0 : set, (forall x1 : set, ((adj x0 x1) -> (adj x1 x0)))) -> (forall x0 : set, (forall x1 : set, (or (not (adj x0 x1)) (adj x1 x0))))).
Theorem deduction13 : (forall x0 : set, (forall x1 : set, (or (not (adj x0 x1)) (adj x1 x0)))).
exact (sorry13 deduction1).
Qed.
Hypothesis sorry14 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (adj x0 x1) (and (adj x1 x2) (adj x0 x2))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (adj x0 x1)) (or (not (adj x1 x2)) (not (adj x0 x2)))))))).
Theorem deduction14 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (adj x0 x1)) (or (not (adj x1 x2)) (not (adj x0 x2))))))).
exact (sorry14 deduction3).
Qed.
Hypothesis sorry15 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, ((and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x1 = x2)) (and (not (x1 = x3)) (not (x2 = x3))))))) -> (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3))))))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, (or (or (x0 = x1) (or (x0 = x2) (or (x0 = x3) (or (x1 = x2) (or (x1 = x3) (x2 = x3)))))) (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3)))))))))))).
Theorem deduction15 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, (or (or (x0 = x1) (or (x0 = x2) (or (x0 = x3) (or (x1 = x2) (or (x1 = x3) (x2 = x3)))))) (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3))))))))))).
exact (sorry15 deduction9).
Qed.
Hypothesis sorry16 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, (or (or (x0 = x1) (or (x0 = x2) (or (x0 = x3) (or (x1 = x2) (or (x1 = x3) (x2 = x3)))))) (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3))))))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, (or (x0 = x1) (or (x0 = x2) (or (x0 = x3) (or (x1 = x2) (or (x1 = x3) (or (x2 = x3) (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3))))))))))))))))).
Theorem deduction16 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, (or (x0 = x1) (or (x0 = x2) (or (x0 = x3) (or (x1 = x2) (or (x1 = x3) (or (x2 = x3) (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3)))))))))))))))).
exact (sorry16 deduction15).
Qed.
Hypothesis sorry17 : ((exists x0 : set, (exists x1 : set, (exists x2 : set, (exists x3 : set, (exists x4 : set, (and (not (x1 = x2)) (and (not (x1 = x3)) (and (not (x1 = x4)) (and (not (x2 = x3)) (and (not (x2 = x4)) (and (not (x3 = x4)) (and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x0 = x4)) (and (adj x0 x1) (and (adj x0 x2) (and (adj x0 x3) (adj x0 x4))))))))))))))))))) -> (and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4))))))))))))))).
Theorem deduction17 : ((exists x0 : set, (exists x1 : set, (exists x2 : set, (exists x3 : set, (exists x4 : set, (and (not (x1 = x2)) (and (not (x1 = x3)) (and (not (x1 = x4)) (and (not (x2 = x3)) (and (not (x2 = x4)) (and (not (x3 = x4)) (and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x0 = x4)) (and (adj x0 x1) (and (adj x0 x2) (and (adj x0 x3) (adj x0 x4))))))))))))))))))) -> (and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4))))))))))))))).
exact sorry17.
Qed.
Hypothesis sorry18 : ((exists x0 : set, (exists x1 : set, (exists x2 : set, (exists x3 : set, (exists x4 : set, (and (not (x1 = x2)) (and (not (x1 = x3)) (and (not (x1 = x4)) (and (not (x2 = x3)) (and (not (x2 = x4)) (and (not (x3 = x4)) (and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x0 = x4)) (and (adj x0 x1) (and (adj x0 x2) (and (adj x0 x3) (adj x0 x4))))))))))))))))))) -> (((exists x0 : set, (exists x1 : set, (exists x2 : set, (exists x3 : set, (exists x4 : set, (and (not (x1 = x2)) (and (not (x1 = x3)) (and (not (x1 = x4)) (and (not (x2 = x3)) (and (not (x2 = x4)) (and (not (x3 = x4)) (and (not (x0 = x1)) (and (not (x0 = x2)) (and (not (x0 = x3)) (and (not (x0 = x4)) (and (adj x0 x1) (and (adj x0 x2) (and (adj x0 x3) (adj x0 x4))))))))))))))))))) -> (and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4))))))))))))))) -> (and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))))).
Theorem deduction18 : (and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))).
exact (sorry18 deduction11 deduction17).
Qed.
Hypothesis sorry19 : ((forall x0 : set, (forall x1 : set, (or (not (adj x0 x1)) (adj x1 x0)))) -> (forall x0 : set, (forall x1 : set, (dk_cons (not (adj x0 x1)) (dk_cons (adj x1 x0) dk_ec))))).
Theorem deduction19 : (forall x0 : set, (forall x1 : set, (dk_cons (not (adj x0 x1)) (dk_cons (adj x1 x0) dk_ec)))).
exact (sorry19 deduction13).
Qed.
Hypothesis sorry21 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (adj x0 x1)) (or (not (adj x1 x2)) (not (adj x0 x2))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (dk_cons (not (adj x1 x2)) (dk_cons (not (adj x0 x2)) (dk_cons (not (adj x0 x1)) dk_ec))))))).
Theorem deduction21 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (dk_cons (not (adj x1 x2)) (dk_cons (not (adj x0 x2)) (dk_cons (not (adj x0 x1)) dk_ec)))))).
exact (sorry21 deduction14).
Qed.
Hypothesis sorry22 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, (or (x0 = x1) (or (x0 = x2) (or (x0 = x3) (or (x1 = x2) (or (x1 = x3) (or (x2 = x3) (or (adj x0 x1) (or (adj x0 x2) (or (adj x0 x3) (or (adj x1 x2) (or (adj x1 x3) (adj x2 x3)))))))))))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, (dk_cons (adj x2 x3) (dk_cons (adj x1 x3) (dk_cons (adj x1 x2) (dk_cons (adj x0 x3) (dk_cons (adj x0 x2) (dk_cons (adj x0 x1) (dk_cons (x2 = x3) (dk_cons (x1 = x3) (dk_cons (x1 = x2) (dk_cons (x0 = x3) (dk_cons (x0 = x2) (dk_cons (x0 = x1) dk_ec))))))))))))))))).
Theorem deduction22 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (forall x3 : set, (dk_cons (adj x2 x3) (dk_cons (adj x1 x3) (dk_cons (adj x1 x2) (dk_cons (adj x0 x3) (dk_cons (adj x0 x2) (dk_cons (adj x0 x1) (dk_cons (x2 = x3) (dk_cons (x1 = x3) (dk_cons (x1 = x2) (dk_cons (x0 = x3) (dk_cons (x0 = x2) (dk_cons (x0 = x1) dk_ec)))))))))))))))).
exact (sorry22 deduction16).
Qed.
Hypothesis sorry23 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (not (sK1 = sK2)) dk_ec)).
Theorem deduction23 : (dk_cons (not (sK1 = sK2)) dk_ec).
exact (sorry23 deduction18).
Qed.
Hypothesis sorry24 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (not (sK1 = sK3)) dk_ec)).
Theorem deduction24 : (dk_cons (not (sK1 = sK3)) dk_ec).
exact (sorry24 deduction18).
Qed.
Hypothesis sorry25 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (not (sK1 = sK4)) dk_ec)).
Theorem deduction25 : (dk_cons (not (sK1 = sK4)) dk_ec).
exact (sorry25 deduction18).
Qed.
Hypothesis sorry26 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (not (sK2 = sK3)) dk_ec)).
Theorem deduction26 : (dk_cons (not (sK2 = sK3)) dk_ec).
exact (sorry26 deduction18).
Qed.
Hypothesis sorry27 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (not (sK2 = sK4)) dk_ec)).
Theorem deduction27 : (dk_cons (not (sK2 = sK4)) dk_ec).
exact (sorry27 deduction18).
Qed.
Hypothesis sorry28 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (not (sK3 = sK4)) dk_ec)).
Theorem deduction28 : (dk_cons (not (sK3 = sK4)) dk_ec).
exact (sorry28 deduction18).
Qed.
Hypothesis sorry33 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (adj sK0 sK1) dk_ec)).
Theorem deduction33 : (dk_cons (adj sK0 sK1) dk_ec).
exact (sorry33 deduction18).
Qed.
Hypothesis sorry34 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (adj sK0 sK2) dk_ec)).
Theorem deduction34 : (dk_cons (adj sK0 sK2) dk_ec).
exact (sorry34 deduction18).
Qed.
Hypothesis sorry35 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (adj sK0 sK3) dk_ec)).
Theorem deduction35 : (dk_cons (adj sK0 sK3) dk_ec).
exact (sorry35 deduction18).
Qed.
Hypothesis sorry36 : ((and (not (sK1 = sK2)) (and (not (sK1 = sK3)) (and (not (sK1 = sK4)) (and (not (sK2 = sK3)) (and (not (sK2 = sK4)) (and (not (sK3 = sK4)) (and (not (sK0 = sK1)) (and (not (sK0 = sK2)) (and (not (sK0 = sK3)) (and (not (sK0 = sK4)) (and (adj sK0 sK1) (and (adj sK0 sK2) (and (adj sK0 sK3) (adj sK0 sK4)))))))))))))) -> (dk_cons (adj sK0 sK4) dk_ec)).
Theorem deduction36 : (dk_cons (adj sK0 sK4) dk_ec).
exact (sorry36 deduction18).
Qed.
Theorem deduction37 : (dk_cons (adj sK1 sK0) dk_ec).
exact (fun x0x5ea0f599d570 : ((adj sK1 sK0) -> False) => (deduction19 sK0 sK1 (fun tnp : (not (adj sK0 sK1)) => (deduction33 (fun tp : (adj sK0 sK1) => (tnp tp)))) x0x5ea0f599d570)).
Qed.
Theorem deduction38 : (dk_cons (adj sK2 sK0) dk_ec).
exact (fun x0x5ea0f599d530 : ((adj sK2 sK0) -> False) => (deduction19 sK0 sK2 (fun tnp : (not (adj sK0 sK2)) => (deduction34 (fun tp : (adj sK0 sK2) => (tnp tp)))) x0x5ea0f599d530)).
Qed.
Theorem deduction40 : (dk_cons (adj sK4 sK0) dk_ec).
exact (fun x0x5ea0f599d470 : ((adj sK4 sK0) -> False) => (deduction19 sK0 sK4 (fun tnp : (not (adj sK0 sK4)) => (deduction36 (fun tp : (adj sK0 sK4) => (tnp tp)))) x0x5ea0f599d470)).
Qed.
Theorem deduction43 : (forall x0 : set, (dk_cons (not (adj x0 sK2)) (dk_cons (not (adj x0 sK0)) dk_ec))).
exact (fun x0 : set => (fun x0x5ea0f599d370 : ((not (adj x0 sK2)) -> False) => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (deduction21 x0 sK0 sK2 (fun tnp : (not (adj sK0 sK2)) => (deduction34 (fun tp : (adj sK0 sK2) => (tnp tp)))) x0x5ea0f599d370 x0x5ea0f599d3b0)))).
Qed.
Theorem deduction44 : (forall x0 : set, (dk_cons (not (adj x0 sK3)) (dk_cons (not (adj x0 sK0)) dk_ec))).
exact (fun x0 : set => (fun x0x5ea0f599d330 : ((not (adj x0 sK3)) -> False) => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (deduction21 x0 sK0 sK3 (fun tnp : (not (adj sK0 sK3)) => (deduction35 (fun tp : (adj sK0 sK3) => (tnp tp)))) x0x5ea0f599d330 x0x5ea0f599d3b0)))).
Qed.
Theorem deduction46 : (forall x0 : set, (dk_cons (not (adj x0 sK1)) (dk_cons (not (adj x0 sK0)) dk_ec))).
exact (fun x0 : set => (fun x0x5ea0f599f070 : ((not (adj x0 sK1)) -> False) => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (deduction21 x0 sK1 sK0 (fun tnp : (not (adj sK1 sK0)) => (deduction37 (fun tp : (adj sK1 sK0) => (tnp tp)))) x0x5ea0f599d3b0 x0x5ea0f599f070)))).
Qed.
Theorem deduction107 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (dk_cons (not (adj x0 sK0)) (dk_cons (adj x1 x2) (dk_cons (adj sK2 x2) (dk_cons (adj sK2 x1) (dk_cons (adj x0 x2) (dk_cons (adj x0 x1) (dk_cons (x1 = x2) (dk_cons (sK2 = x2) (dk_cons (sK2 = x1) (dk_cons (x0 = x2) (dk_cons (x0 = x1) (dk_cons (sK2 = x0) dk_ec))))))))))))))).
exact (fun x0 : set => (fun x1 : set => (fun x2 : set => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (fun x0x5ea0f59a0830 : ((adj x1 x2) -> False) => (fun x0x5ea0f599c170 : ((adj sK2 x2) -> False) => (fun x0x5ea0f599ee70 : ((adj sK2 x1) -> False) => (fun x0x5ea0f59a07f0 : ((adj x0 x2) -> False) => (fun x0x5ea0f59a0a30 : ((adj x0 x1) -> False) => (fun x0x5ea0f599fa30 : ((x1 = x2) -> False) => (fun x0x5ea0f599ee30 : ((sK2 = x2) -> False) => (fun x0x5ea0f599c4b0 : ((sK2 = x1) -> False) => (fun x0x5ea0f599fab0 : ((x0 = x2) -> False) => (fun x0x5ea0f599faf0 : ((x0 = x1) -> False) => (fun x0x5ea0f599c470 : ((sK2 = x0) -> False) => (deduction43 x0 (fun tnp : (not (adj x0 sK2)) => (deduction22 x0 sK2 x1 x2 x0x5ea0f59a0830 x0x5ea0f599c170 x0x5ea0f599ee70 x0x5ea0f59a07f0 x0x5ea0f59a0a30 (fun tp : (adj x0 sK2) => (tnp tp)) x0x5ea0f599fa30 x0x5ea0f599ee30 x0x5ea0f599c4b0 x0x5ea0f599fab0 x0x5ea0f599faf0 (comml sK2 x0 x0x5ea0f599c470))) x0x5ea0f599d3b0)))))))))))))))).
Qed.
Theorem deduction428 : (forall x0 : set, (forall x1 : set, (dk_cons (adj x0 x1) (dk_cons (adj sK2 x1) (dk_cons (adj sK2 x0) (dk_cons (adj sK4 x1) (dk_cons (adj sK4 x0) (dk_cons (x0 = x1) (dk_cons (sK2 = x1) (dk_cons (sK2 = x0) (dk_cons (sK4 = x1) (dk_cons (sK4 = x0) (dk_cons (sK2 = sK4) dk_ec))))))))))))).
exact (fun x0 : set => (fun x1 : set => (fun x0x5ea0f59a0a30 : ((adj x0 x1) -> False) => (fun x0x5ea0f599ee70 : ((adj sK2 x1) -> False) => (fun x0x5ea0f599a870 : ((adj sK2 x0) -> False) => (fun x0x5ea0f599b9f0 : ((adj sK4 x1) -> False) => (fun x0x5ea0f599a7f0 : ((adj sK4 x0) -> False) => (fun x0x5ea0f599faf0 : ((x0 = x1) -> False) => (fun x0x5ea0f599c4b0 : ((sK2 = x1) -> False) => (fun x0x5ea0f599c470 : ((sK2 = x0) -> False) => (fun x0x5ea0f599b970 : ((sK4 = x1) -> False) => (fun x0x5ea0f599b930 : ((sK4 = x0) -> False) => (fun x0x5ea0f599e530 : ((sK2 = sK4) -> False) => (deduction107 sK4 x0 x1 (fun tnp : (not (adj sK4 sK0)) => (deduction40 (fun tp : (adj sK4 sK0) => (tnp tp)))) x0x5ea0f59a0a30 x0x5ea0f599ee70 x0x5ea0f599a870 x0x5ea0f599b9f0 x0x5ea0f599a7f0 x0x5ea0f599faf0 x0x5ea0f599c4b0 x0x5ea0f599c470 x0x5ea0f599b970 x0x5ea0f599b930 x0x5ea0f599e530)))))))))))))).
Qed.
Theorem deduction430 : (forall x0 : set, (forall x1 : set, (dk_cons (adj sK4 x1) (dk_cons (adj sK4 x0) (dk_cons (adj x0 x1) (dk_cons (adj sK2 x0) (dk_cons (adj sK2 x1) (dk_cons (x0 = x1) (dk_cons (sK2 = x1) (dk_cons (sK2 = x0) (dk_cons (sK4 = x1) (dk_cons (sK4 = x0) dk_ec)))))))))))).
exact (fun x0 : set => (fun x1 : set => (fun x0x5ea0f599b9f0 : ((adj sK4 x1) -> False) => (fun x0x5ea0f599a7f0 : ((adj sK4 x0) -> False) => (fun x0x5ea0f59a0a30 : ((adj x0 x1) -> False) => (fun x0x5ea0f599a870 : ((adj sK2 x0) -> False) => (fun x0x5ea0f599ee70 : ((adj sK2 x1) -> False) => (fun x0x5ea0f599faf0 : ((x0 = x1) -> False) => (fun x0x5ea0f599c4b0 : ((sK2 = x1) -> False) => (fun x0x5ea0f599c470 : ((sK2 = x0) -> False) => (fun x0x5ea0f599b970 : ((sK4 = x1) -> False) => (fun x0x5ea0f599b930 : ((sK4 = x0) -> False) => (deduction428 x0 x1 x0x5ea0f59a0a30 x0x5ea0f599ee70 x0x5ea0f599a870 x0x5ea0f599b9f0 x0x5ea0f599a7f0 x0x5ea0f599faf0 x0x5ea0f599c4b0 x0x5ea0f599c470 x0x5ea0f599b970 x0x5ea0f599b930 (fun tp : (sK2 = sK4) => (deduction27 (fun tnp : (not (sK2 = sK4)) => (tnp tp))))))))))))))))).
Qed.
Theorem deduction493 : (forall x0 : set, (dk_cons (adj sK4 sK3) (dk_cons (adj sK4 x0) (dk_cons (adj sK2 x0) (dk_cons (adj sK2 sK3) (dk_cons (sK3 = x0) (dk_cons (sK2 = sK3) (dk_cons (sK2 = x0) (dk_cons (sK3 = sK4) (dk_cons (sK4 = x0) (dk_cons (not (adj x0 sK0)) dk_ec))))))))))).
exact (fun x0 : set => (fun x0x5ea0f59985b0 : ((adj sK4 sK3) -> False) => (fun x0x5ea0f599a7f0 : ((adj sK4 x0) -> False) => (fun x0x5ea0f599a870 : ((adj sK2 x0) -> False) => (fun x0x5ea0f5998670 : ((adj sK2 sK3) -> False) => (fun x0x5ea0f599c030 : ((sK3 = x0) -> False) => (fun x0x5ea0f599e730 : ((sK2 = sK3) -> False) => (fun x0x5ea0f599c470 : ((sK2 = x0) -> False) => (fun x0x5ea0f599e4f0 : ((sK3 = sK4) -> False) => (fun x0x5ea0f599b930 : ((sK4 = x0) -> False) => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (deduction430 x0 sK3 x0x5ea0f59985b0 x0x5ea0f599a7f0 (fun tp : (adj x0 sK3) => (deduction44 x0 (fun tnp : (not (adj x0 sK3)) => (tnp tp)) x0x5ea0f599d3b0)) x0x5ea0f599a870 x0x5ea0f5998670 (comml sK3 x0 x0x5ea0f599c030) x0x5ea0f599e730 x0x5ea0f599c470 (comml sK3 sK4 x0x5ea0f599e4f0) x0x5ea0f599b930)))))))))))).
Qed.
Theorem deduction515 : (forall x0 : set, (dk_cons (adj sK4 sK3) (dk_cons (adj sK4 x0) (dk_cons (adj sK2 x0) (dk_cons (adj sK2 sK3) (dk_cons (sK3 = x0) (dk_cons (sK2 = x0) (dk_cons (sK3 = sK4) (dk_cons (sK4 = x0) (dk_cons (not (adj x0 sK0)) dk_ec)))))))))).
exact (fun x0 : set => (fun x0x5ea0f59985b0 : ((adj sK4 sK3) -> False) => (fun x0x5ea0f599a7f0 : ((adj sK4 x0) -> False) => (fun x0x5ea0f599a870 : ((adj sK2 x0) -> False) => (fun x0x5ea0f5998670 : ((adj sK2 sK3) -> False) => (fun x0x5ea0f599c030 : ((sK3 = x0) -> False) => (fun x0x5ea0f599c470 : ((sK2 = x0) -> False) => (fun x0x5ea0f599e4f0 : ((sK3 = sK4) -> False) => (fun x0x5ea0f599b930 : ((sK4 = x0) -> False) => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (deduction493 x0 x0x5ea0f59985b0 x0x5ea0f599a7f0 x0x5ea0f599a870 x0x5ea0f5998670 x0x5ea0f599c030 (fun tp : (sK2 = sK3) => (deduction26 (fun tnp : (not (sK2 = sK3)) => (tnp tp)))) x0x5ea0f599c470 x0x5ea0f599e4f0 x0x5ea0f599b930 x0x5ea0f599d3b0))))))))))).
Qed.
Theorem deduction523 : (forall x0 : set, (dk_cons (adj sK4 sK3) (dk_cons (adj sK4 x0) (dk_cons (adj sK2 x0) (dk_cons (adj sK2 sK3) (dk_cons (sK3 = x0) (dk_cons (sK2 = x0) (dk_cons (sK4 = x0) (dk_cons (not (adj x0 sK0)) dk_ec))))))))).
exact (fun x0 : set => (fun x0x5ea0f59985b0 : ((adj sK4 sK3) -> False) => (fun x0x5ea0f599a7f0 : ((adj sK4 x0) -> False) => (fun x0x5ea0f599a870 : ((adj sK2 x0) -> False) => (fun x0x5ea0f5998670 : ((adj sK2 sK3) -> False) => (fun x0x5ea0f599c030 : ((sK3 = x0) -> False) => (fun x0x5ea0f599c470 : ((sK2 = x0) -> False) => (fun x0x5ea0f599b930 : ((sK4 = x0) -> False) => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (deduction515 x0 x0x5ea0f59985b0 x0x5ea0f599a7f0 x0x5ea0f599a870 x0x5ea0f5998670 x0x5ea0f599c030 x0x5ea0f599c470 (fun tp : (sK3 = sK4) => (deduction28 (fun tnp : (not (sK3 = sK4)) => (tnp tp)))) x0x5ea0f599b930 x0x5ea0f599d3b0)))))))))).
Qed.
Definition sp1 : prop := ((not (adj sK2 sK3)) -> False).
Theorem deduction532 : (Prf_av_clause (av_if sp1 (dk_acl (dk_cl (dk_cons (adj sK2 sK3) dk_ec))))).
exact (fun nnsp1 : ((not sp1) -> False) => (fun x0x5ea0f5998670 : ((adj sK2 sK3) -> False) => (nnsp1 (fun psp : sp1 => (psp x0x5ea0f5998670))))).
Qed.
Definition sp2 : prop := (forall x0 : set, ((not (not (adj x0 sK0))) -> ((not (adj sK4 x0)) -> ((not (sK4 = x0)) -> ((not (sK2 = x0)) -> ((not (sK3 = x0)) -> ((not (adj sK2 x0)) -> False))))))).
Theorem deduction535 : (Prf_av_clause (av_if sp2 (dk_acl (forall x0 : set, (dk_cons (not (adj x0 sK0)) (dk_cons (adj sK4 x0) (dk_cons (sK4 = x0) (dk_cons (sK2 = x0) (dk_cons (sK3 = x0) (dk_cons (adj sK2 x0) dk_ec)))))))))).
exact (fun nnsp2 : ((not sp2) -> False) => (fun x0 : set => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (fun x0x5ea0f599a7f0 : ((adj sK4 x0) -> False) => (fun x0x5ea0f599b930 : ((sK4 = x0) -> False) => (fun x0x5ea0f599c470 : ((sK2 = x0) -> False) => (fun x0x5ea0f599c030 : ((sK3 = x0) -> False) => (fun x0x5ea0f599a870 : ((adj sK2 x0) -> False) => (nnsp2 (fun psp : sp2 => (psp x0 x0x5ea0f599d3b0 x0x5ea0f599a7f0 x0x5ea0f599b930 x0x5ea0f599c470 x0x5ea0f599c030 x0x5ea0f599a870))))))))))).
Qed.
Definition sp3 : prop := ((not (adj sK4 sK3)) -> False).
Theorem deduction539 : (Prf_av_clause (av_if sp3 (dk_acl (dk_cl (dk_cons (adj sK4 sK3) dk_ec))))).
exact (fun nnsp3 : ((not sp3) -> False) => (fun x0x5ea0f59985b0 : ((adj sK4 sK3) -> False) => (nnsp3 (fun psp : sp3 => (psp x0x5ea0f59985b0))))).
Qed.
Theorem deduction540 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp3 (dk_cons sp2 (dk_cons sp1 dk_ec)))))).
exact (fun nnsp3 : (sp3 -> False) => (fun nnsp2 : (sp2 -> False) => (fun nnsp1 : (sp1 -> False) => (nnsp3 (fun x0x5ea0f59985b0 : ((adj sK4 sK3) -> False) => (nnsp2 (fun x0 : set => (fun x0x5ea0f599d3b0 : ((not (adj x0 sK0)) -> False) => (fun x0x5ea0f599a7f0 : ((adj sK4 x0) -> False) => (fun x0x5ea0f599b930 : ((sK4 = x0) -> False) => (fun x0x5ea0f599c470 : ((sK2 = x0) -> False) => (fun x0x5ea0f599c030 : ((sK3 = x0) -> False) => (fun x0x5ea0f599a870 : ((adj sK2 x0) -> False) => (nnsp1 (fun x0x5ea0f5998670 : ((adj sK2 sK3) -> False) => (deduction523 x0 x0x5ea0f59985b0 x0x5ea0f599a7f0 x0x5ea0f599a870 x0x5ea0f5998670 x0x5ea0f599c030 x0x5ea0f599c470 x0x5ea0f599b930 x0x5ea0f599d3b0)))))))))))))))).
Qed.
Definition sp4 : prop := ((not (adj sK2 sK1)) -> False).
Theorem deduction543 : (Prf_av_clause (av_if (not sp4) (dk_acl (dk_cl (dk_cons (not (adj sK2 sK1)) dk_ec))))).
exact (fun nnsp4 : ((not (not sp4)) -> False) => (fun x0x5ea0f59988f0 : ((not (adj sK2 sK1)) -> False) => (nnsp4 (fun psp : (not sp4) => (psp x0x5ea0f59988f0))))).
Qed.
Theorem deduction544 : (Prf_av_clause (av_if sp4 (dk_acl (dk_cl (dk_cons (adj sK2 sK1) dk_ec))))).
exact (fun nnsp4 : ((not sp4) -> False) => (fun x0x5ea0f59986f0 : ((adj sK2 sK1) -> False) => (nnsp4 (fun psp : sp4 => (psp x0x5ea0f59986f0))))).
Qed.
Definition sp6 : prop := ((not (adj sK4 sK1)) -> False).
Theorem deduction551 : (Prf_av_clause (av_if sp6 (dk_acl (dk_cl (dk_cons (adj sK4 sK1) dk_ec))))).
exact (fun nnsp6 : ((not sp6) -> False) => (fun x0x5ea0f5998630 : ((adj sK4 sK1) -> False) => (nnsp6 (fun psp : sp6 => (psp x0x5ea0f5998630))))).
Qed.
Theorem deduction608 : (Prf_av_clause (av_if sp4 (dk_acl (dk_cl (dk_cons (not (adj sK2 sK0)) dk_ec))))).
exact (fun nnsp4 : ((not sp4) -> False) => (fun x0x5ea0f599d3f0 : ((not (adj sK2 sK0)) -> False) => (deduction544 nnsp4 (fun tp : (adj sK2 sK1) => (deduction46 sK2 (fun tnp : (not (adj sK2 sK1)) => (tnp tp)) x0x5ea0f599d3f0))))).
Qed.
Theorem deduction614 : (Prf_av_clause (av_if sp4 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp4 : ((not sp4) -> False) => (deduction608 nnsp4 (fun tnp : (not (adj sK2 sK0)) => (deduction38 (fun tp : (adj sK2 sK0) => (tnp tp)))))).
Qed.
Theorem deduction615 : (Prf_av_clause (av_if sp4 (dk_acl (dk_cl dk_ec)))).
exact deduction614.
Qed.
Theorem deduction760 : (Prf_av_clause (av_if sp2 (dk_acl (dk_cl (dk_cons (adj sK4 sK1) (dk_cons (sK1 = sK4) (dk_cons (sK1 = sK2) (dk_cons (sK1 = sK3) (dk_cons (adj sK2 sK1) dk_ec))))))))).
exact (fun nnsp2 : ((not sp2) -> False) => (fun x0x5ea0f5998630 : ((adj sK4 sK1) -> False) => (fun x0x5ea0f599e5b0 : ((sK1 = sK4) -> False) => (fun x0x5ea0f599c130 : ((sK1 = sK2) -> False) => (fun x0x5ea0f599e7f0 : ((sK1 = sK3) -> False) => (fun x0x5ea0f59986f0 : ((adj sK2 sK1) -> False) => (deduction535 nnsp2 sK1 (fun tnp : (not (adj sK1 sK0)) => (deduction37 (fun tp : (adj sK1 sK0) => (tnp tp)))) x0x5ea0f5998630 (comml sK1 sK4 x0x5ea0f599e5b0) (comml sK1 sK2 x0x5ea0f599c130) (comml sK1 sK3 x0x5ea0f599e7f0) x0x5ea0f59986f0))))))).
Qed.
Theorem deduction767 : (Prf_av_clause (av_if sp2 (dk_acl (dk_cl (dk_cons (adj sK4 sK1) (dk_cons (sK1 = sK2) (dk_cons (sK1 = sK3) (dk_cons (adj sK2 sK1) dk_ec)))))))).
exact (fun nnsp2 : ((not sp2) -> False) => (fun x0x5ea0f5998630 : ((adj sK4 sK1) -> False) => (fun x0x5ea0f599c130 : ((sK1 = sK2) -> False) => (fun x0x5ea0f599e7f0 : ((sK1 = sK3) -> False) => (fun x0x5ea0f59986f0 : ((adj sK2 sK1) -> False) => (deduction760 nnsp2 x0x5ea0f5998630 (fun tp : (sK1 = sK4) => (deduction25 (fun tnp : (not (sK1 = sK4)) => (tnp tp)))) x0x5ea0f599c130 x0x5ea0f599e7f0 x0x5ea0f59986f0)))))).
Qed.
Theorem deduction777 : (Prf_av_clause (av_if sp2 (dk_acl (dk_cl (dk_cons (adj sK4 sK1) (dk_cons (sK1 = sK3) (dk_cons (adj sK2 sK1) dk_ec))))))).
exact (fun nnsp2 : ((not sp2) -> False) => (fun x0x5ea0f5998630 : ((adj sK4 sK1) -> False) => (fun x0x5ea0f599e7f0 : ((sK1 = sK3) -> False) => (fun x0x5ea0f59986f0 : ((adj sK2 sK1) -> False) => (deduction767 nnsp2 x0x5ea0f5998630 (fun tp : (sK1 = sK2) => (deduction23 (fun tnp : (not (sK1 = sK2)) => (tnp tp)))) x0x5ea0f599e7f0 x0x5ea0f59986f0))))).
Qed.
Theorem deduction787 : (Prf_av_clause (av_if sp2 (dk_acl (dk_cl (dk_cons (adj sK4 sK1) (dk_cons (adj sK2 sK1) dk_ec)))))).
exact (fun nnsp2 : ((not sp2) -> False) => (fun x0x5ea0f5998630 : ((adj sK4 sK1) -> False) => (fun x0x5ea0f59986f0 : ((adj sK2 sK1) -> False) => (deduction777 nnsp2 x0x5ea0f5998630 (fun tp : (sK1 = sK3) => (deduction24 (fun tnp : (not (sK1 = sK3)) => (tnp tp)))) x0x5ea0f59986f0)))).
Qed.
Theorem deduction788 : (Prf_av_clause (av_if sp2 (av_if (not sp4) (dk_acl (dk_cl (dk_cons (adj sK4 sK1) dk_ec)))))).
exact (fun nnsp2 : ((not sp2) -> False) => (fun nnsp4 : ((not (not sp4)) -> False) => (fun x0x5ea0f5998630 : ((adj sK4 sK1) -> False) => (deduction787 nnsp2 x0x5ea0f5998630 (fun tp : (adj sK2 sK1) => (deduction543 nnsp4 (fun tnp : (not (adj sK2 sK1)) => (tnp tp)))))))).
Qed.
Theorem deduction789 : (Prf_av_clause (dk_acl (dk_cl (dk_cons sp6 (dk_cons sp4 (dk_cons (not sp2) dk_ec)))))).
exact (fun nnsp6 : (sp6 -> False) => (fun nnsp4 : (sp4 -> False) => (fun nnsp2 : ((not sp2) -> False) => (nnsp6 (fun x0x5ea0f5998630 : ((adj sK4 sK1) -> False) => (deduction788 nnsp2 (fun nnnsp4 : ((not sp4) -> False) => (nnnsp4 nnsp4)) x0x5ea0f5998630)))))).
Qed.
Theorem deduction825 : (Prf_av_clause (av_if sp3 (dk_acl (dk_cl (dk_cons (not (adj sK4 sK0)) dk_ec))))).
exact (fun nnsp3 : ((not sp3) -> False) => (fun x0x5ea0f599ea30 : ((not (adj sK4 sK0)) -> False) => (deduction539 nnsp3 (fun tp : (adj sK4 sK3) => (deduction44 sK4 (fun tnp : (not (adj sK4 sK3)) => (tnp tp)) x0x5ea0f599ea30))))).
Qed.
Theorem deduction834 : (Prf_av_clause (av_if sp3 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp3 : ((not sp3) -> False) => (deduction825 nnsp3 (fun tnp : (not (adj sK4 sK0)) => (deduction40 (fun tp : (adj sK4 sK0) => (tnp tp)))))).
Qed.
Theorem deduction835 : (Prf_av_clause (av_if sp3 (dk_acl (dk_cl dk_ec)))).
exact deduction834.
Qed.
Theorem deduction966 : (Prf_av_clause (av_if sp6 (dk_acl (dk_cl (dk_cons (not (adj sK4 sK0)) dk_ec))))).
exact (fun nnsp6 : ((not sp6) -> False) => (fun x0x5ea0f599ea30 : ((not (adj sK4 sK0)) -> False) => (deduction551 nnsp6 (fun tp : (adj sK4 sK1) => (deduction46 sK4 (fun tnp : (not (adj sK4 sK1)) => (tnp tp)) x0x5ea0f599ea30))))).
Qed.
Theorem deduction975 : (Prf_av_clause (av_if sp6 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp6 : ((not sp6) -> False) => (deduction966 nnsp6 (fun tnp : (not (adj sK4 sK0)) => (deduction40 (fun tp : (adj sK4 sK0) => (tnp tp)))))).
Qed.
Theorem deduction976 : (Prf_av_clause (av_if sp6 (dk_acl (dk_cl dk_ec)))).
exact deduction975.
Qed.
Theorem deduction1016 : (Prf_av_clause (av_if sp1 (dk_acl (dk_cl (dk_cons (not (adj sK2 sK0)) dk_ec))))).
exact (fun nnsp1 : ((not sp1) -> False) => (fun x0x5ea0f599d3f0 : ((not (adj sK2 sK0)) -> False) => (deduction532 nnsp1 (fun tp : (adj sK2 sK3) => (deduction44 sK2 (fun tnp : (not (adj sK2 sK3)) => (tnp tp)) x0x5ea0f599d3f0))))).
Qed.
Theorem deduction1025 : (Prf_av_clause (av_if sp1 (dk_acl (dk_cl dk_ec)))).
exact (fun nnsp1 : ((not sp1) -> False) => (deduction1016 nnsp1 (fun tnp : (not (adj sK2 sK0)) => (deduction38 (fun tp : (adj sK2 sK0) => (tnp tp)))))).
Qed.
Theorem deduction1026 : (Prf_av_clause (av_if sp1 (dk_acl (dk_cl dk_ec)))).
exact deduction1025.
Qed.
End DeduktiProof.
