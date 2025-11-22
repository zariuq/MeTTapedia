Definition symm_diff : set -> set -> set :=
  fun A B => (A :\: B) :\/: (B :\: A).

Section Blocker1.

Variable D : set.
Variable R : set.
Variable A : set.
Variable Ap : set.

Hypothesis D_decomp : D = R :\/: A :\/: Ap.
Hypothesis R_disj_A : R :/\: A = Empty.
Hypothesis R_disj_Ap : R :/\: Ap = Empty.
Hypothesis A_disj_Ap : A :/\: Ap = Empty.
Hypothesis R_subset_D : R c= D.
Hypothesis A_subset_D : A c= D.
Hypothesis Ap_subset_D : Ap c= D.

Theorem per_run_xor_domain : forall x:set,
  x :e symm_diff (R :\/: A) (R :\/: Ap) -> x :e A :\/: Ap.
let x.
assume Hx: x :e symm_diff (R :\/: A) (R :\/: Ap).
prove x :e A :\/: Ap.
apply binunionE (((R :\/: A) :\: (R :\/: Ap))) (((R :\/: Ap) :\: (R :\/: A))) x Hx.
- assume HxL: x :e (R :\/: A) :\: (R :\/: Ap).
  apply setminusE (R :\/: A) (R :\/: Ap) x HxL.
  assume Hx_in: x :e R :\/: A.
  assume Hx_nin: x /:e R :\/: Ap.
  apply binunionE R A x Hx_in.
  + assume Hx_R: x :e R.
    apply Hx_nin.
    apply binunionI1.
    exact Hx_R.
  + assume Hx_A: x :e A.
    apply binunionI1.
    exact Hx_A.
- assume HxR: x :e (R :\/: Ap) :\: (R :\/: A).
  apply setminusE (R :\/: Ap) (R :\/: A) x HxR.
  assume Hx_in: x :e R :\/: Ap.
  assume Hx_nin: x /:e R :\/: A.
  apply binunionE R Ap x Hx_in.
  + assume Hx_R: x :e R.
    apply Hx_nin.
    apply binunionI1.
    exact Hx_R.
  + assume Hx_Ap: x :e Ap.
    apply binunionI2.
    exact Hx_Ap.
Qed.

Theorem boundary_not_in_xor : forall x:set,
  x :e R -> x /:e symm_diff (R :\/: A) (R :\/: Ap).
let x.
assume Hx_R: x :e R.
assume Hcontra: x :e symm_diff (R :\/: A) (R :\/: Ap).
prove False.
apply binunionE (((R :\/: A) :\: (R :\/: Ap))) (((R :\/: Ap) :\: (R :\/: A))) x Hcontra.
- assume HxL: x :e (R :\/: A) :\: (R :\/: Ap).
  apply setminusE2 (R :\/: A) (R :\/: Ap) x HxL.
  apply binunionI1.
  exact Hx_R.
- assume HxR: x :e (R :\/: Ap) :\: (R :\/: A).
  apply setminusE2 (R :\/: Ap) (R :\/: A) x HxR.
  apply binunionI1.
  exact Hx_R.
Qed.

End Blocker1.
