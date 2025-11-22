Section Lemma43Refutation.

Variable R : set.
Variable A : set.
Variable Ap : set.

Hypothesis R_A_disjoint : forall x:set, ~(x :e R /\ x :e A).
Hypothesis R_Ap_disjoint : forall x:set, ~(x :e R /\ x :e Ap).
Hypothesis A_Ap_disjoint : forall x:set, ~(x :e A /\ x :e Ap).

Definition RA : set := R :\/: A.
Definition RAp : set := R :\/: Ap.
Definition interior : set := A :\/: Ap.

Theorem symm_diff_RA_RAp_forward :
  forall x:set, x :e (RA :\: RAp) :\/: (RAp :\: RA) -> x :e interior.
let x.
assume Hsym: x :e (RA :\: RAp) :\/: (RAp :\: RA).
prove x :e A :\/: Ap.
apply binunionE (RA :\: RAp) (RAp :\: RA) x Hsym.
- assume H1: x :e RA :\: RAp.
  claim HinRA: x :e RA.
  exact setminusE1 RA RAp x H1.
  claim HnotRAp: x /:e RAp.
  exact setminusE2 RA RAp x H1.
  apply binunionE R A x HinRA.
  + assume HinR: x :e R.
    prove False.
    apply HnotRAp.
    prove x :e R :\/: Ap.
    apply binunionI1. exact HinR.
  + assume HinA: x :e A.
    apply binunionI1. exact HinA.
- assume H2: x :e RAp :\: RA.
  claim HinRAp: x :e RAp.
  exact setminusE1 RAp RA x H2.
  claim HnotRA: x /:e RA.
  exact setminusE2 RAp RA x H2.
  apply binunionE R Ap x HinRAp.
  + assume HinR: x :e R.
    prove False.
    apply HnotRA.
    prove x :e R :\/: A.
    apply binunionI1. exact HinR.
  + assume HinAp: x :e Ap.
    apply binunionI2. exact HinAp.
Qed.

Theorem symm_diff_RA_RAp_backward :
  forall x:set, x :e interior -> x :e (RA :\: RAp) :\/: (RAp :\: RA).
let x.
assume Hint: x :e A :\/: Ap.
prove x :e (RA :\: RAp) :\/: (RAp :\: RA).
apply binunionE A Ap x Hint.
- assume HinA: x :e A.
  apply binunionI1.
  prove x :e RA :\: RAp.
  apply setminusI.
  + prove x :e R :\/: A. apply binunionI2. exact HinA.
  + prove x /:e R :\/: Ap.
    assume HinRAp: x :e R :\/: Ap.
    apply binunionE R Ap x HinRAp.
    * assume HinR: x :e R.
      apply R_A_disjoint x.
      apply andI. exact HinR. exact HinA.
    * assume HinAp: x :e Ap.
      apply A_Ap_disjoint x.
      apply andI. exact HinA. exact HinAp.
- assume HinAp: x :e Ap.
  apply binunionI2.
  prove x :e RAp :\: RA.
  apply setminusI.
  + prove x :e R :\/: Ap. apply binunionI2. exact HinAp.
  + prove x /:e R :\/: A.
    assume HinRA: x :e R :\/: A.
    apply binunionE R A x HinRA.
    * assume HinR: x :e R.
      apply R_Ap_disjoint x.
      apply andI. exact HinR. exact HinAp.
    * assume HinA: x :e A.
      apply A_Ap_disjoint x.
      apply andI. exact HinA. exact HinAp.
Qed.

Theorem boundary_not_in_symm_diff :
  forall x:set, x :e R -> ~(x :e (RA :\: RAp) :\/: (RAp :\: RA)).
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

Theorem goertzel_lemma43_is_false :
  (forall x:set, x :e interior <-> x :e (RA :\: RAp) :\/: (RAp :\: RA)) /\
  (forall x:set, x :e R -> ~(x :e (RA :\: RAp) :\/: (RAp :\: RA))).
apply andI.
- let x. apply iffI.
  + exact symm_diff_RA_RAp_backward x.
  + exact symm_diff_RA_RAp_forward x.
- exact boundary_not_in_symm_diff.
Qed.

End Lemma43Refutation.
