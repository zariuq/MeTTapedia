Section DeduktiProof.
Variable red : (set -> (set -> prop)).
Variable a : set.
Variable b : set.
Variable c : set.
Hypothesis clause_continuation : (dk_cPrf (dk_clause (dk_cons (not (red a b)) (dk_cons (not (red b c)) (dk_cons (not (red a c)) dk_ec))))).
End DeduktiProof.
