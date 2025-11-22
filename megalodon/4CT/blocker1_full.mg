Definition symm_diff : set -> set -> set :=
  fun A B => (A :\: B) :\/: (B :\: A).

Theorem symm_diff_self : forall X:set, symm_diff X X = Empty.
let X.
prove (X :\: X) :\/: (X :\: X) = Empty.
rewrite setminus_selfannih.
prove Empty :\/: Empty = Empty.
apply binunion_idl.
Qed.

Theorem symm_diff_comm : forall A B:set, symm_diff A B = symm_diff B A.
let A. let B.
prove (A :\: B) :\/: (B :\: A) = (B :\: A) :\/: (A :\: B).
apply binunion_com.
Qed.

Section KempeCycle.

Variable R : set.
Variable A : set.
Variable Ap : set.

Hypothesis R_A_disjoint : R :/\: A = Empty.
Hypothesis R_Ap_disjoint : R :/\: Ap = Empty.
Hypothesis A_Ap_disjoint : A :/\: Ap = Empty.

Theorem R_not_in_A : forall x:set, x :e R -> x /:e A.
let x.
assume HxR: x :e R.
assume HxA: x :e A.
prove False.
apply EmptyE x.
rewrite <- R_A_disjoint.
apply binintersectI.
- exact HxR.
- exact HxA.
Qed.

Theorem R_not_in_Ap : forall x:set, x :e R -> x /:e Ap.
let x.
assume HxR: x :e R.
assume HxAp: x :e Ap.
prove False.
apply EmptyE x.
rewrite <- R_Ap_disjoint.
apply binintersectI.
- exact HxR.
- exact HxAp.
Qed.

Theorem A_not_in_Ap : forall x:set, x :e A -> x /:e Ap.
let x.
assume HxA: x :e A.
assume HxAp: x :e Ap.
prove False.
apply EmptyE x.
rewrite <- A_Ap_disjoint.
apply binintersectI.
- exact HxA.
- exact HxAp.
Qed.

Theorem A_not_in_R : forall x:set, x :e A -> x /:e R.
let x.
assume HxA: x :e A.
assume HxR: x :e R.
prove False.
apply R_not_in_A x HxR HxA.
Qed.

Theorem Ap_not_in_R : forall x:set, x :e Ap -> x /:e R.
let x.
assume HxAp: x :e Ap.
assume HxR: x :e R.
prove False.
apply R_not_in_Ap x HxR HxAp.
Qed.

Theorem Ap_not_in_A : forall x:set, x :e Ap -> x /:e A.
let x.
assume HxAp: x :e Ap.
assume HxA: x :e A.
prove False.
apply A_not_in_Ap x HxA HxAp.
Qed.

Theorem per_run_xor_gives_interior : forall x:set,
  x :e symm_diff (R :\/: A) (R :\/: Ap) -> x :e A :\/: Ap.
let x.
assume Hx: x :e symm_diff (R :\/: A) (R :\/: Ap).
prove x :e A :\/: Ap.
apply binunionE ((R :\/: A) :\: (R :\/: Ap)) ((R :\/: Ap) :\: (R :\/: A)) x Hx.
- assume HxL: x :e (R :\/: A) :\: (R :\/: Ap).
  apply setminusE (R :\/: A) (R :\/: Ap) x HxL.
  assume Hx_in: x :e R :\/: A.
  assume Hx_nin: x /:e R :\/: Ap.
  apply binunionE R A x Hx_in.
  + assume HxR: x :e R.
    apply Hx_nin.
    apply binunionI1.
    exact HxR.
  + assume HxA: x :e A.
    apply binunionI1.
    exact HxA.
- assume HxR: x :e (R :\/: Ap) :\: (R :\/: A).
  apply setminusE (R :\/: Ap) (R :\/: A) x HxR.
  assume Hx_in: x :e R :\/: Ap.
  assume Hx_nin: x /:e R :\/: A.
  apply binunionE R Ap x Hx_in.
  + assume HxR2: x :e R.
    apply Hx_nin.
    apply binunionI1.
    exact HxR2.
  + assume HxAp: x :e Ap.
    apply binunionI2.
    exact HxAp.
Qed.

Theorem boundary_excluded_from_xor : forall x:set,
  x :e R -> x /:e symm_diff (R :\/: A) (R :\/: Ap).
let x.
assume HxR: x :e R.
assume Hcontra: x :e symm_diff (R :\/: A) (R :\/: Ap).
prove False.
apply binunionE ((R :\/: A) :\: (R :\/: Ap)) ((R :\/: Ap) :\: (R :\/: A)) x Hcontra.
- assume HxL: x :e (R :\/: A) :\: (R :\/: Ap).
  apply setminusE2 (R :\/: A) (R :\/: Ap) x HxL.
  apply binunionI1.
  exact HxR.
- assume HxR2: x :e (R :\/: Ap) :\: (R :\/: A).
  apply setminusE2 (R :\/: Ap) (R :\/: A) x HxR2.
  apply binunionI1.
  exact HxR.
Qed.

Theorem interior_in_xor_from_A : forall x:set,
  x :e A -> x :e symm_diff (R :\/: A) (R :\/: Ap).
let x.
assume HxA: x :e A.
prove x :e ((R :\/: A) :\: (R :\/: Ap)) :\/: ((R :\/: Ap) :\: (R :\/: A)).
apply binunionI1.
apply setminusI.
- apply binunionI2. exact HxA.
- assume Hcontra: x :e R :\/: Ap.
  apply binunionE R Ap x Hcontra.
  + assume HxR: x :e R.
    apply A_not_in_R x HxA HxR.
  + assume HxAp: x :e Ap.
    apply A_not_in_Ap x HxA HxAp.
Qed.

Theorem interior_in_xor_from_Ap : forall x:set,
  x :e Ap -> x :e symm_diff (R :\/: A) (R :\/: Ap).
let x.
assume HxAp: x :e Ap.
prove x :e ((R :\/: A) :\: (R :\/: Ap)) :\/: ((R :\/: Ap) :\: (R :\/: A)).
apply binunionI2.
apply setminusI.
- apply binunionI2. exact HxAp.
- assume Hcontra: x :e R :\/: A.
  apply binunionE R A x Hcontra.
  + assume HxR: x :e R.
    apply Ap_not_in_R x HxAp HxR.
  + assume HxA: x :e A.
    apply Ap_not_in_A x HxAp HxA.
Qed.

Theorem xor_domain_is_exactly_interior : forall x:set,
  x :e symm_diff (R :\/: A) (R :\/: Ap) <-> x :e A :\/: Ap.
let x.
apply iffI.
- exact per_run_xor_gives_interior x.
- assume Hx: x :e A :\/: Ap.
  apply binunionE A Ap x Hx.
  + exact interior_in_xor_from_A x.
  + exact interior_in_xor_from_Ap x.
Qed.

End KempeCycle.
