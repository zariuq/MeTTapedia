Theorem test_claim : forall P Q:prop, P -> Q -> P /\ Q.
let P. let Q. assume HP: P. assume HQ: Q.
claim H: P.
  exact HP.
exact andI P Q H HQ.
Qed.