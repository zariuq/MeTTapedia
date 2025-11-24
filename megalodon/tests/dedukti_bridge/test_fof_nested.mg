Section DeduktiProof.
Variable f : (set -> set).
Variable g : (set -> set).
Variable a : set.
Variable b : set.
Hypothesis axiom_2_ : (not ((and (forall x0 : set, (forall x1 : set, (((f x0) = (f x1)) -> ((g x0) = (g x1))))) ((f a) = (f b))) -> ((g a) = (g b)))).
Theorem deduction2 : (not ((and (forall x0 : set, (forall x1 : set, (((f x0) = (f x1)) -> ((g x0) = (g x1))))) ((f a) = (f b))) -> ((g a) = (g b)))).
exact axiom_2_.
Qed.
Hypothesis sorry3 : ((not ((and (forall x0 : set, (forall x1 : set, (((f x0) = (f x1)) -> ((g x0) = (g x1))))) ((f a) = (f b))) -> ((g a) = (g b)))) -> (and (and (forall x0 : set, (forall x1 : set, (or (not ((f x0) = (f x1))) ((g x0) = (g x1))))) ((f a) = (f b))) (not ((g a) = (g b))))).
Theorem deduction3 : (and (and (forall x0 : set, (forall x1 : set, (or (not ((f x0) = (f x1))) ((g x0) = (g x1))))) ((f a) = (f b))) (not ((g a) = (g b)))).
exact (sorry3 deduction2).
Qed.
Hypothesis sorry4 : ((and (and (forall x0 : set, (forall x1 : set, (or (not ((f x0) = (f x1))) ((g x0) = (g x1))))) ((f a) = (f b))) (not ((g a) = (g b)))) -> (and (forall x0 : set, (forall x1 : set, (or (not ((f x0) = (f x1))) ((g x0) = (g x1))))) (and ((f a) = (f b)) (not ((g a) = (g b)))))).
Theorem deduction4 : (and (forall x0 : set, (forall x1 : set, (or (not ((f x0) = (f x1))) ((g x0) = (g x1))))) (and ((f a) = (f b)) (not ((g a) = (g b))))).
exact (sorry4 deduction3).
Qed.
Hypothesis sorry5 : ((and (forall x0 : set, (forall x1 : set, (or (not ((f x0) = (f x1))) ((g x0) = (g x1))))) (and ((f a) = (f b)) (not ((g a) = (g b))))) -> (forall x0 : set, (forall x1 : set, (dk_cons (not ((f x0) = (f x1))) (dk_cons ((g x0) = (g x1)) dk_ec))))).
Theorem deduction5 : (forall x0 : set, (forall x1 : set, (dk_cons (not ((f x0) = (f x1))) (dk_cons ((g x0) = (g x1)) dk_ec)))).
exact (sorry5 deduction4).
Qed.
Hypothesis sorry6 : ((and (forall x0 : set, (forall x1 : set, (or (not ((f x0) = (f x1))) ((g x0) = (g x1))))) (and ((f a) = (f b)) (not ((g a) = (g b))))) -> (dk_cons ((f a) = (f b)) dk_ec)).
Theorem deduction6 : (dk_cons ((f a) = (f b)) dk_ec).
exact (sorry6 deduction4).
Qed.
Hypothesis sorry7 : ((and (forall x0 : set, (forall x1 : set, (or (not ((f x0) = (f x1))) ((g x0) = (g x1))))) (and ((f a) = (f b)) (not ((g a) = (g b))))) -> (dk_cons (not ((g a) = (g b))) dk_ec)).
Theorem deduction7 : (dk_cons (not ((g a) = (g b))) dk_ec).
exact (sorry7 deduction4).
Qed.
Theorem deduction9 : (forall x0 : set, (dk_cons (not ((f x0) = (f a))) (dk_cons ((g x0) = (g b)) dk_ec))).
exact (fun x0 : set => (fun x0x5ba72d610af0 : ((not ((f x0) = (f a))) -> False) => (fun x0x5ba72d610a70 : (((g x0) = (g b)) -> False) => (deduction5 x0 b (fun q : (not ((f x0) = (f b))) => (deduction6 (fun r : ((f a) = (f b)) => (x0x5ba72d610af0 (comm (f a) (f b) r (fun z : set => (not ((f x0) = z))) q))))) x0x5ba72d610a70)))).
Qed.
Theorem deduction11 : (dk_cons ((g a) = (g b)) dk_ec).
exact (fun x0x5ba72d6115f0 : (((g a) = (g b)) -> False) => (deduction9 a (fun p : (not ((f a) = (f a))) => (p (eqI (f a)))) x0x5ba72d6115f0)).
Qed.
Theorem deduction12 : dk_ec.
exact (deduction11 (fun tp : ((g a) = (g b)) => (deduction7 (fun tnp : (not ((g a) = (g b))) => (tnp tp))))).
Qed.
End DeduktiProof.
