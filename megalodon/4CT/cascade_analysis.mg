Section CascadeAnalysis.

Variable R : set.
Variable A : set.
Variable Ap : set.
Variable a : set.

Hypothesis R_A_disjoint : forall x:set, ~(x :e R /\ x :e A).
Hypothesis R_Ap_disjoint : forall x:set, ~(x :e R /\ x :e Ap).
Hypothesis A_Ap_disjoint : forall x:set, ~(x :e A /\ x :e Ap).
Hypothesis a_in_A : a :e A.

Definition RA : set := R :\/: A.
Definition RAp : set := R :\/: Ap.
Definition symm_diff_result : set := (RA :\: RAp) :\/: (RAp :\: RA).
Definition interior : set := A :\/: Ap.

Theorem symm_diff_equals_interior :
  forall x:set, x :e symm_diff_result <-> x :e interior.
let x. apply iffI.
- assume Hsym: x :e symm_diff_result.
  prove x :e A :\/: Ap.
  apply binunionE (RA :\: RAp) (RAp :\: RA) x Hsym.
  + assume H1: x :e RA :\: RAp.
    claim HinRA: x :e RA.
    exact setminusE1 RA RAp x H1.
    claim HnotRAp: x /:e RAp.
    exact setminusE2 RA RAp x H1.
    apply binunionE R A x HinRA.
    * assume HinR: x :e R.
      prove False.
      apply HnotRAp.
      prove x :e R :\/: Ap.
      exact binunionI1 R Ap x HinR.
    * assume HinA: x :e A.
      apply binunionI1. exact HinA.
  + assume H2: x :e RAp :\: RA.
    claim HinRAp: x :e RAp.
    exact setminusE1 RAp RA x H2.
    claim HnotRA: x /:e RA.
    exact setminusE2 RAp RA x H2.
    apply binunionE R Ap x HinRAp.
    * assume HinR: x :e R.
      prove False.
      apply HnotRA.
      prove x :e R :\/: A.
      exact binunionI1 R A x HinR.
    * assume HinAp: x :e Ap.
      apply binunionI2. exact HinAp.
- assume Hint: x :e A :\/: Ap.
  prove x :e (RA :\: RAp) :\/: (RAp :\: RA).
  apply binunionE A Ap x Hint.
  + assume HinA: x :e A.
    apply binunionI1.
    prove x :e RA :\: RAp.
    apply setminusI.
    * prove x :e R :\/: A. exact binunionI2 R A x HinA.
    * prove x /:e R :\/: Ap.
      assume HinRAp: x :e R :\/: Ap.
      apply binunionE R Ap x HinRAp.
      - assume HinR: x :e R.
        apply R_A_disjoint x.
        apply andI. exact HinR. exact HinA.
      - assume HinAp: x :e Ap.
        apply A_Ap_disjoint x.
        apply andI. exact HinA. exact HinAp.
  + assume HinAp: x :e Ap.
    apply binunionI2.
    prove x :e RAp :\: RA.
    apply setminusI.
    * prove x :e R :\/: Ap. exact binunionI2 R Ap x HinAp.
    * prove x /:e R :\/: A.
      assume HinRA: x :e R :\/: A.
      apply binunionE R A x HinRA.
      - assume HinR: x :e R.
        apply R_Ap_disjoint x.
        apply andI. exact HinR. exact HinAp.
      - assume HinA: x :e A.
        apply A_Ap_disjoint x.
        apply andI. exact HinA. exact HinAp.
Qed.

Theorem boundary_excluded_from_symm_diff :
  forall x:set, x :e R -> x /:e symm_diff_result.
let x.
assume HinR: x :e R.
assume Hsym: x :e (RA :\: RAp) :\/: (RAp :\: RA).
prove False.
apply binunionE (RA :\: RAp) (RAp :\: RA) x Hsym.
- assume H1: x :e RA :\: RAp.
  claim HnotRAp: x /:e RAp.
  exact setminusE2 RA RAp x H1.
  apply HnotRAp.
  prove x :e R :\/: Ap.
  exact binunionI1 R Ap x HinR.
- assume H2: x :e RAp :\: RA.
  claim HnotRA: x /:e RA.
  exact setminusE2 RAp RA x H2.
  apply HnotRA.
  prove x :e R :\/: A.
  exact binunionI1 R A x HinR.
Qed.

Theorem goertzel_claim_false :
  ~(symm_diff_result = R).
assume Heq: symm_diff_result = R.
claim Ha_in_interior: a :e interior.
prove a :e A :\/: Ap.
exact binunionI1 A Ap a a_in_A.
claim Ha_in_symm: a :e symm_diff_result.
apply symm_diff_equals_interior a.
assume Hfwd: a :e symm_diff_result -> a :e interior.
assume Hbwd: a :e interior -> a :e symm_diff_result.
exact Hbwd Ha_in_interior.
claim Ha_in_R: a :e R.
rewrite <- Heq. exact Ha_in_symm.
apply R_A_disjoint a.
apply andI. exact Ha_in_R. exact a_in_A.
Qed.

Theorem lemma44_instantiation_impossible :
  ~(forall x:set, x :e symm_diff_result <-> x :e R).
assume Hiff: forall x:set, x :e symm_diff_result <-> x :e R.
claim Ha_in_interior: a :e interior.
prove a :e A :\/: Ap.
exact binunionI1 A Ap a a_in_A.
claim Ha_in_symm: a :e symm_diff_result.
apply symm_diff_equals_interior a.
assume Hfwd: a :e symm_diff_result -> a :e interior.
assume Hbwd: a :e interior -> a :e symm_diff_result.
exact Hbwd Ha_in_interior.
claim Ha_in_R: a :e R.
apply Hiff a.
assume Hfwd: a :e symm_diff_result -> a :e R.
assume Hbwd: a :e R -> a :e symm_diff_result.
exact Hfwd Ha_in_symm.
apply R_A_disjoint a.
apply andI. exact Ha_in_R. exact a_in_A.
Qed.

End CascadeAnalysis.
