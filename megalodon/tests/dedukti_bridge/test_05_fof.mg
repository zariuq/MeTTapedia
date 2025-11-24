Section DeduktiProof.
Variable a : set.
Variable p : (set -> prop).
Variable q : (set -> prop).
Hypothesis axiom_1_ax : (forall x0 : set, ((p x0) -> (q x0))).
Theorem deduction1 : (forall x0 : set, ((p x0) -> (q x0))).
exact axiom_1_ax.
Qed.
Hypothesis axiom_3_ : (not ((p a) -> (q a))).
Theorem deduction3 : (not ((p a) -> (q a))).
exact axiom_3_.
Qed.
Hypothesis sorry4 : ((forall x0 : set, ((p x0) -> (q x0))) -> (forall x0 : set, (or (not (p x0)) (q x0)))).
Theorem deduction4 : (forall x0 : set, (or (not (p x0)) (q x0))).
exact (sorry4 deduction1).
Qed.
Hypothesis sorry5 : ((not ((p a) -> (q a))) -> (and (p a) (not (q a)))).
Theorem deduction5 : (and (p a) (not (q a))).
exact (sorry5 deduction3).
Qed.
Hypothesis sorry6 : ((forall x0 : set, (or (not (p x0)) (q x0))) -> (forall x0 : set, (dk_cons (not (p x0)) (dk_cons (q x0) dk_ec)))).
Theorem deduction6 : (forall x0 : set, (dk_cons (not (p x0)) (dk_cons (q x0) dk_ec))).
exact (sorry6 deduction4).
Qed.
Hypothesis sorry7 : ((and (p a) (not (q a))) -> (dk_cons (p a) dk_ec)).
Theorem deduction7 : (dk_cons (p a) dk_ec).
exact (sorry7 deduction5).
Qed.
Hypothesis sorry8 : ((and (p a) (not (q a))) -> (dk_cons (not (q a)) dk_ec)).
Theorem deduction8 : (dk_cons (not (q a)) dk_ec).
exact (sorry8 deduction5).
Qed.
Theorem deduction9 : (dk_cons (q a) dk_ec).
exact (fun x0x5edf1d4777f0 : ((q a) -> False) => (deduction6 a (fun tnp : (not (p a)) => (deduction7 (fun tp : (p a) => (tnp tp)))) x0x5edf1d4777f0)).
Qed.
Theorem deduction10 : dk_ec.
exact (deduction9 (fun tp : (q a) => (deduction8 (fun tnp : (not (q a)) => (tnp tp))))).
Qed.
End DeduktiProof.
