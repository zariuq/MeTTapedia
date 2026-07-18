Definition AddInput211 : set := (2,1).
Definition AddComputedRecord211 : set := (AddInput211,add_nat 2 1).
Definition EvalAdd211 : set := {AddComputedRecord211}.

Theorem add_nat_2_1_eq_3 : add_nat 2 1 = 3.
rewrite (add_nat_SR 2 0 nat_0).
rewrite (add_nat_0R 2).
reflexivity.
Qed.

Theorem eval_add_2_1_3 : (AddInput211,3) :e EvalAdd211.
rewrite <- add_nat_2_1_eq_3.
exact (SingI AddComputedRecord211).
Qed.

Theorem eval_add_2_1_unique : forall y:set, (AddInput211,y) :e EvalAdd211 -> y = 3.
let y.
assume H: (AddInput211,y) :e EvalAdd211.
claim Hrecord: (AddInput211,y) = AddComputedRecord211.
{ exact (SingE AddComputedRecord211 (AddInput211,y) H). }
claim Hy: y = add_nat 2 1.
{ exact
    (andER
      (AddInput211 = AddInput211)
      (y = add_nat 2 1)
      (tuple_2_inj AddInput211 y AddInput211 (add_nat 2 1) Hrecord)). }
rewrite <- add_nat_2_1_eq_3.
exact Hy.
Qed.
