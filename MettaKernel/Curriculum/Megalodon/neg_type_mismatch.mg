(* NEGATIVE: a set offered where a proof (of x :e x) is required *)
Parameter In:set->set->prop.
Theorem bad : forall x:set, x :e x.
let x.
exact x.
Qed.
