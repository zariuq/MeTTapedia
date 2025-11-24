Section DeduktiProof.
Variable sK0 : set.
Variable sK1 : set.
Variable sK2 : set.
Variable adj : (set -> (set -> prop)).
Hypothesis axiom_1_adj_sym : (forall x0 : set, (forall x1 : set, ((adj x0 x1) -> (adj x1 x0)))).
Theorem deduction1 : (forall x0 : set, (forall x1 : set, ((adj x0 x1) -> (adj x1 x0)))).
exact axiom_1_adj_sym.
Qed.
Hypothesis axiom_3_triangle_free : (forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (adj x0 x1) (and (adj x1 x2) (adj x0 x2))))))).
Theorem deduction3 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (adj x0 x1) (and (adj x1 x2) (adj x0 x2))))))).
exact axiom_3_triangle_free.
Qed.
Hypothesis axiom_5_ : (not (forall x3 : set, (forall x0 : set, (forall x1 : set, ((and (adj x3 x0) (and (adj x3 x1) (not (x0 = x1)))) -> (not (adj x0 x1))))))).
Theorem deduction5 : (not (forall x3 : set, (forall x0 : set, (forall x1 : set, ((and (adj x3 x0) (and (adj x3 x1) (not (x0 = x1)))) -> (not (adj x0 x1))))))).
exact axiom_5_.
Qed.
Hypothesis sorry6 : ((not (forall x3 : set, (forall x0 : set, (forall x1 : set, ((and (adj x3 x0) (and (adj x3 x1) (not (x0 = x1)))) -> (not (adj x0 x1))))))) -> (not (forall x0 : set, (forall x1 : set, (forall x2 : set, ((and (adj x0 x1) (and (adj x0 x2) (not (x1 = x2)))) -> (not (adj x1 x2)))))))).
Theorem deduction6 : (not (forall x0 : set, (forall x1 : set, (forall x2 : set, ((and (adj x0 x1) (and (adj x0 x2) (not (x1 = x2)))) -> (not (adj x1 x2))))))).
exact (sorry6 deduction5).
Qed.
Hypothesis sorry7 : ((forall x0 : set, (forall x1 : set, ((adj x0 x1) -> (adj x1 x0)))) -> (forall x0 : set, (forall x1 : set, (or (not (adj x0 x1)) (adj x1 x0))))).
Theorem deduction7 : (forall x0 : set, (forall x1 : set, (or (not (adj x0 x1)) (adj x1 x0)))).
exact (sorry7 deduction1).
Qed.
Hypothesis sorry8 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (not (and (adj x0 x1) (and (adj x1 x2) (adj x0 x2))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (adj x0 x1)) (or (not (adj x1 x2)) (not (adj x0 x2)))))))).
Theorem deduction8 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (adj x0 x1)) (or (not (adj x1 x2)) (not (adj x0 x2))))))).
exact (sorry8 deduction3).
Qed.
Hypothesis sorry9 : ((not (forall x0 : set, (forall x1 : set, (forall x2 : set, ((and (adj x0 x1) (and (adj x0 x2) (not (x1 = x2)))) -> (not (adj x1 x2))))))) -> (exists x0 : set, (exists x1 : set, (exists x2 : set, (and (and (adj x0 x1) (and (adj x0 x2) (not (x1 = x2)))) (adj x1 x2)))))).
Theorem deduction9 : (exists x0 : set, (exists x1 : set, (exists x2 : set, (and (and (adj x0 x1) (and (adj x0 x2) (not (x1 = x2)))) (adj x1 x2))))).
exact (sorry9 deduction6).
Qed.
Hypothesis sorry10 : ((exists x0 : set, (exists x1 : set, (exists x2 : set, (and (and (adj x0 x1) (and (adj x0 x2) (not (x1 = x2)))) (adj x1 x2))))) -> (exists x0 : set, (exists x1 : set, (exists x2 : set, (and (adj x0 x1) (and (adj x0 x2) (and (not (x1 = x2)) (adj x1 x2)))))))).
Theorem deduction10 : (exists x0 : set, (exists x1 : set, (exists x2 : set, (and (adj x0 x1) (and (adj x0 x2) (and (not (x1 = x2)) (adj x1 x2))))))).
exact (sorry10 deduction9).
Qed.
Hypothesis sorry11 : ((exists x0 : set, (exists x1 : set, (exists x2 : set, (and (adj x0 x1) (and (adj x0 x2) (and (not (x1 = x2)) (adj x1 x2))))))) -> (and (adj sK0 sK1) (and (adj sK0 sK2) (and (not (sK1 = sK2)) (adj sK1 sK2))))).
Theorem deduction11 : ((exists x0 : set, (exists x1 : set, (exists x2 : set, (and (adj x0 x1) (and (adj x0 x2) (and (not (x1 = x2)) (adj x1 x2))))))) -> (and (adj sK0 sK1) (and (adj sK0 sK2) (and (not (sK1 = sK2)) (adj sK1 sK2))))).
exact sorry11.
Qed.
Hypothesis sorry12 : ((exists x0 : set, (exists x1 : set, (exists x2 : set, (and (adj x0 x1) (and (adj x0 x2) (and (not (x1 = x2)) (adj x1 x2))))))) -> (((exists x0 : set, (exists x1 : set, (exists x2 : set, (and (adj x0 x1) (and (adj x0 x2) (and (not (x1 = x2)) (adj x1 x2))))))) -> (and (adj sK0 sK1) (and (adj sK0 sK2) (and (not (sK1 = sK2)) (adj sK1 sK2))))) -> (and (adj sK0 sK1) (and (adj sK0 sK2) (and (not (sK1 = sK2)) (adj sK1 sK2)))))).
Theorem deduction12 : (and (adj sK0 sK1) (and (adj sK0 sK2) (and (not (sK1 = sK2)) (adj sK1 sK2)))).
exact (sorry12 deduction10 deduction11).
Qed.
Hypothesis sorry13 : ((forall x0 : set, (forall x1 : set, (or (not (adj x0 x1)) (adj x1 x0)))) -> (forall x0 : set, (forall x1 : set, (dk_cons (not (adj x0 x1)) (dk_cons (adj x1 x0) dk_ec))))).
Theorem deduction13 : (forall x0 : set, (forall x1 : set, (dk_cons (not (adj x0 x1)) (dk_cons (adj x1 x0) dk_ec)))).
exact (sorry13 deduction7).
Qed.
Hypothesis sorry15 : ((forall x0 : set, (forall x1 : set, (forall x2 : set, (or (not (adj x0 x1)) (or (not (adj x1 x2)) (not (adj x0 x2))))))) -> (forall x0 : set, (forall x1 : set, (forall x2 : set, (dk_cons (not (adj x1 x2)) (dk_cons (not (adj x0 x2)) (dk_cons (not (adj x0 x1)) dk_ec))))))).
Theorem deduction15 : (forall x0 : set, (forall x1 : set, (forall x2 : set, (dk_cons (not (adj x1 x2)) (dk_cons (not (adj x0 x2)) (dk_cons (not (adj x0 x1)) dk_ec)))))).
exact (sorry15 deduction8).
Qed.
Hypothesis sorry16 : ((and (adj sK0 sK1) (and (adj sK0 sK2) (and (not (sK1 = sK2)) (adj sK1 sK2)))) -> (dk_cons (adj sK0 sK1) dk_ec)).
Theorem deduction16 : (dk_cons (adj sK0 sK1) dk_ec).
exact (sorry16 deduction12).
Qed.
Hypothesis sorry17 : ((and (adj sK0 sK1) (and (adj sK0 sK2) (and (not (sK1 = sK2)) (adj sK1 sK2)))) -> (dk_cons (adj sK0 sK2) dk_ec)).
Theorem deduction17 : (dk_cons (adj sK0 sK2) dk_ec).
exact (sorry17 deduction12).
Qed.
Hypothesis sorry19 : ((and (adj sK0 sK1) (and (adj sK0 sK2) (and (not (sK1 = sK2)) (adj sK1 sK2)))) -> (dk_cons (adj sK1 sK2) dk_ec)).
Theorem deduction19 : (dk_cons (adj sK1 sK2) dk_ec).
exact (sorry19 deduction12).
Qed.
Theorem deduction20 : (dk_cons (adj sK1 sK0) dk_ec).
exact (fun x0x64d23df74c70 : ((adj sK1 sK0) -> False) => (deduction13 sK0 sK1 (fun tnp : (not (adj sK0 sK1)) => (deduction16 (fun tp : (adj sK0 sK1) => (tnp tp)))) x0x64d23df74c70)).
Qed.
Theorem deduction25 : (forall x0 : set, (dk_cons (not (adj x0 sK2)) (dk_cons (not (adj x0 sK0)) dk_ec))).
exact (fun x0 : set => (fun x0x64d23df74630 : ((not (adj x0 sK2)) -> False) => (fun x0x64d23df74670 : ((not (adj x0 sK0)) -> False) => (deduction15 x0 sK0 sK2 (fun tnp : (not (adj sK0 sK2)) => (deduction17 (fun tp : (adj sK0 sK2) => (tnp tp)))) x0x64d23df74630 x0x64d23df74670)))).
Qed.
Theorem deduction33 : (dk_cons (not (adj sK1 sK0)) dk_ec).
exact (fun x0x64d23df74870 : ((not (adj sK1 sK0)) -> False) => (deduction25 sK1 (fun tnp : (not (adj sK1 sK2)) => (deduction19 (fun tp : (adj sK1 sK2) => (tnp tp)))) x0x64d23df74870)).
Qed.
Theorem deduction34 : dk_ec.
exact (deduction33 (fun tnp : (not (adj sK1 sK0)) => (deduction20 (fun tp : (adj sK1 sK0) => (tnp tp))))).
Qed.
End DeduktiProof.
