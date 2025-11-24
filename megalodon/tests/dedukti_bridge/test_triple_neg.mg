Section DeduktiProof.
Variable red : (set -> (set -> prop)).
Variable n3 : set.
Hypothesis deduction46 : (forall v0 : set, (forall v1 : set, (forall v2 : set, (dk_cons (not (red v1 v2)) (dk_cons (not (red v0 v2)) (dk_cons (not (red v0 v1)) dk_ec)))))).
Hypothesis deduction21 : (forall v0 : set, (dk_cons (red v0 n3) dk_ec)).
Theorem deduction125 : (forall v0 : set, (dk_cons (not (red v0 n3)) (dk_cons (not (red v0 v0)) dk_ec))).
exact (fun v0 : set => (fun h1 : ((not (red v0 n3)) -> False) => (fun h2 : ((not (red v0 v0)) -> False) => (deduction46 v0 v0 n3 (fun tnp : (not (red v0 n3)) => (deduction21 v0 (fun tp : (red v0 n3) => (tnp tp)))) h1 h2)))).
Qed.
End DeduktiProof.
