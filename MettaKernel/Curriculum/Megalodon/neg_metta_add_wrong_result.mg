Definition AddInput211 : set := (2,1).
Definition AddComputedRecord211 : set := (AddInput211,add_nat 2 1).
Definition EvalAdd211 : set := {AddComputedRecord211}.

Theorem wrong_eval_add_2_1_4 : (AddInput211,4) :e EvalAdd211.
exact (SingI (AddInput211,4)).
Qed.
