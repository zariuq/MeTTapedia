Section DeduktiProof.
Variable c0 : set.
Variable big_Q : (set -> prop).
Hypothesis axiom_2_assert_false : (not (big_Q c0)).
Theorem deduction2 : (not (big_Q c0)).
exact axiom_2_assert_false.
Qed.
Hypothesis axiom_3_force_true : (big_Q c0).
Theorem deduction3 : (big_Q c0).
exact axiom_3_force_true.
Qed.
Hypothesis sorry10 : ((not (big_Q c0)) -> (dk_cons (not (big_Q c0)) dk_ec)).
Theorem deduction10 : (dk_cons (not (big_Q c0)) dk_ec).
exact (sorry10 deduction2).
Qed.
Hypothesis sorry11 : ((big_Q c0) -> (dk_cons (big_Q c0) dk_ec)).
Theorem deduction11 : (dk_cons (big_Q c0) dk_ec).
exact (sorry11 deduction3).
Qed.
Theorem deduction12 : dk_ec.
exact (deduction10 (fun tnp : (not (big_Q c0)) => (deduction11 (fun tp : (big_Q c0) => (tnp tp))))).
Qed.
End DeduktiProof.
