Section DeduktiProof.
Variable a : set.
Variable f : (set -> prop).
Variable g : (set -> prop).
Hypothesis axiom_1_def_f : (forall x0 : set, (iff (f x0) (g x0))).
Theorem deduction1 : (forall x0 : set, (iff (f x0) (g x0))).
exact axiom_1_def_f.
Qed.
Hypothesis axiom_2_fa : (f a).
Theorem deduction2 : (f a).
exact axiom_2_fa.
Qed.
Hypothesis axiom_3_ng : (not (g a)).
Theorem deduction3 : (not (g a)).
exact axiom_3_ng.
Qed.
Hypothesis sorry7 : ((forall x0 : set, (iff (f x0) (g x0))) -> (forall x0 : set, ((f x0) -> (g x0)))).
Theorem deduction7 : (forall x0 : set, ((f x0) -> (g x0))).
exact (sorry7 deduction1).
Qed.
Hypothesis sorry8 : ((forall x0 : set, ((f x0) -> (g x0))) -> (forall x0 : set, (or (not (f x0)) (g x0)))).
Theorem deduction8 : (forall x0 : set, (or (not (f x0)) (g x0))).
exact (sorry8 deduction7).
Qed.
Hypothesis sorry9 : ((forall x0 : set, (or (not (f x0)) (g x0))) -> (forall x0 : set, (dk_cons (not (f x0)) (dk_cons (g x0) dk_ec)))).
Theorem deduction9 : (forall x0 : set, (dk_cons (not (f x0)) (dk_cons (g x0) dk_ec))).
exact (sorry9 deduction8).
Qed.
Hypothesis sorry10 : ((f a) -> (dk_cons (f a) dk_ec)).
Theorem deduction10 : (dk_cons (f a) dk_ec).
exact (sorry10 deduction2).
Qed.
Hypothesis sorry11 : ((not (g a)) -> (dk_cons (not (g a)) dk_ec)).
Theorem deduction11 : (dk_cons (not (g a)) dk_ec).
exact (sorry11 deduction3).
Qed.
Theorem deduction12 : (dk_cons (g a) dk_ec).
exact (fun x0x6036a1a767f0 : ((g a) -> False) => (deduction9 a (fun tnp : (not (f a)) => (deduction10 (fun tp : (f a) => (tnp tp)))) x0x6036a1a767f0)).
Qed.
Theorem deduction13 : dk_ec.
exact (deduction12 (fun tp : (g a) => (deduction11 (fun tnp : (not (g a)) => (tnp tp))))).
Qed.
End DeduktiProof.
