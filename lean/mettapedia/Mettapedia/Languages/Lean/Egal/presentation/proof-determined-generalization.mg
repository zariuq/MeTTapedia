(** The proof, not the example, determines the generalization.

    Lean's showcase (GSLT dynamics), read into Egal whole.  Terms are
    literals, variables and a binary mul; Deriv a b holds the root
    derivations from a to b, by two rules: mulZeroR t derives mul t 0 -> 0,
    and mulZeroL t derives mul 0 t -> 0.  A derivation is data (Deriv lives
    in Type), so the rule that made it is part of it.

    The example mul 0 0 -> 0 has two derivations, one per rule: both rules
    apply there, and each derivation records which one did.  Each determines
    its own generalization: generalize reads only the derivation's rule, and
    generalize_sound derives every instance, typed at the indices generalize
    computes.  Lean's two theorems, read and proved above, say that both
    generalizations meet the example and that neither subsumes the other.
    Here: the two derivations are distinct elements of one fiber, and each
    generalization holds at every term x, by the same rule as its example. **)

Section ProofDeterminedGeneralization.

(** Short names for the reading's, in this section only. **)
Let Tm : set := Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm.
Let Deriv : set -> set -> set := Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Deriv.
Let lit : set -> set := Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_node.
Let mul : set -> set -> set := Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_node.
Let zero : set := lit (LeanNum 0).
Let example : set := mul zero zero.
Let byRight : set := Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight.
Let byLeft : set := Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByLeft.
Let generalize : set -> set -> set := fun d x => Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize example zero d x.
Let generalize_sound : set -> set -> set := fun d x => Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize_sound example zero d x.
Let fst : set -> set := fun p => Lean_Prod_fst Tm Tm p.
Let snd : set -> set := fun p => Lean_Prod_snd Tm Tm p.
Let pair : set -> set -> set := fun a b => Lean_Prod_mk_node Tm Tm a b.

Theorem Ex_one_example_two_derivations : byRight :e Deriv example zero /\ byLeft :e Deriv example zero.
apply andI.
- exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight_In.
- exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByLeft_In.
Qed.

Theorem Ex_the_derivations_differ : byRight <> byLeft.
prove Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight <> Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByLeft.
rewrite Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight_eq_1. rewrite Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByLeft_eq_1.
exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Deriv_noconf0_1 zero zero.
Qed.

(** Every instance of a generalization is derived, by its example's rule:
    generalize_sound's type, at the indices generalize computes there. **)

Theorem Ex_right_generalization : forall x :e Tm, generalize_sound byRight x :e Deriv (mul x zero) zero.
let x. assume Hx: x :e Tm.
claim HZ: zero :e Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_typed (LeanNum 0) (LeanNum_In 0 nat_0). }
claim HE: example :e Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_typed zero HZ zero HZ. }
claim Hn: mul x zero :e Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_typed x Hx zero HZ. }
claim E: generalize byRight x = pair (mul x zero) zero.
{ prove Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize example zero Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight x = pair (mul x zero) zero.
  rewrite Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight_eq_1.
  exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize_eq_1 zero HZ x Hx example HE zero HZ. }
claim A: fst (generalize byRight x) = mul x zero.
{ rewrite E. exact Lean_Prod_fst_mk Tm Tm (mul x zero) Hn zero HZ. }
claim B: snd (generalize byRight x) = zero.
{ rewrite E. exact Lean_Prod_snd_mk Tm Tm (mul x zero) Hn zero HZ. }
claim T: generalize_sound byRight x :e Deriv (fst (generalize byRight x)) (snd (generalize byRight x)).
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize_sound_In example HE zero HZ Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight
    Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByRight_In x Hx. }
exact In_fam_eq (fun z => Deriv z zero) (fst (generalize byRight x)) (mul x zero) A (generalize_sound byRight x)
  (In_fam_eq (fun z => Deriv (fst (generalize byRight x)) z) (snd (generalize byRight x)) zero B (generalize_sound byRight x) T).
Qed.

Theorem Ex_left_generalization : forall x :e Tm, generalize_sound byLeft x :e Deriv (mul zero x) zero.
let x. assume Hx: x :e Tm.
claim HZ: zero :e Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_lit_typed (LeanNum 0) (LeanNum_In 0 nat_0). }
claim HE: example :e Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_typed zero HZ zero HZ. }
claim Hn: mul zero x :e Tm.
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_Tm_mul_typed zero HZ x Hx. }
claim E: generalize byLeft x = pair (mul zero x) zero.
{ prove Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize example zero Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByLeft x = pair (mul zero x) zero.
  rewrite Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByLeft_eq_1.
  exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize_eq_2 zero HZ x Hx example HE zero HZ. }
claim A: fst (generalize byLeft x) = mul zero x.
{ rewrite E. exact Lean_Prod_fst_mk Tm Tm (mul zero x) Hn zero HZ. }
claim B: snd (generalize byLeft x) = zero.
{ rewrite E. exact Lean_Prod_snd_mk Tm Tm (mul zero x) Hn zero HZ. }
claim T: generalize_sound byLeft x :e Deriv (fst (generalize byLeft x)) (snd (generalize byLeft x)).
{ exact Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_generalize_sound_In example HE zero HZ Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByLeft
    Lean_Mettapedia_GSLT_Dynamics_ProofDeterminedGeneralization_exampleByLeft_In x Hx. }
exact In_fam_eq (fun z => Deriv z zero) (fst (generalize byLeft x)) (mul zero x) A (generalize_sound byLeft x)
  (In_fam_eq (fun z => Deriv (fst (generalize byLeft x)) z) (snd (generalize byLeft x)) zero B (generalize_sound byLeft x) T).
Qed.

End ProofDeterminedGeneralization.
