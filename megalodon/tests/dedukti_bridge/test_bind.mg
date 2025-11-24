Section DeduktiProof.
Variable P : (set -> prop).
Definition allP : prop := (forall x : set, (P x)).
End DeduktiProof.
