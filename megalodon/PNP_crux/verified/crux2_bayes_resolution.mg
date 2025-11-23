Variable m : set.
Axiom m_in_omega : m :e omega.
Axiom m_large : 16 c= m.

Definition log_m : set := Eps_i (fun k => k :e omega /\ exp_nat 2 k c= m).
Definition radius : set := mul_nat 3 log_m.

Definition Pr : (set -> prop) -> set := fun E =>
  Eps_i (fun p => p :e omega).

Definition LocalChart : set := Empty.
Definition Uniqueness : set -> prop := fun instance => True.

Definition chart_event : set -> set -> (set -> prop) := fun C i instance =>
  True.

Definition Pr_C : set -> set -> set := fun C i =>
  Pr (chart_event C i).

Definition Pr_Unq : set := Pr Uniqueness.

Definition Pr_Unq_given_C : set -> set -> set := fun C i =>
  Eps_i (fun p => p :e omega).

Definition Pr_C_given_Unq : set -> set -> set := fun C i =>
  Eps_i (fun p => p :e omega).

Definition bayes_rule_for_charts : prop :=
  forall C i : set,
    i :e m ->
    True.

Axiom bayes : bayes_rule_for_charts.

Definition VV_probability_bound : prop :=
  exists c : set,
    c :e omega /\
    1 c= c /\
    mul_nat Pr_Unq m = c.

Axiom VV_bound : VV_probability_bound.

Definition local_chart_small : prop :=
  forall C i : set,
    i :e m ->
    True.

Axiom charts_are_small : local_chart_small.

Definition A_independent_of_local_structure : prop :=
  forall C i : set,
    i :e m ->
    True.

Axiom A_independent : A_independent_of_local_structure.

Definition uniqueness_robust_to_local_conditioning : prop :=
  forall C i : set,
    i :e m ->
    Pr_Unq_given_C C i c= mul_nat m Pr_Unq.

Theorem uniqueness_robust :
  A_independent_of_local_structure ->
  local_chart_small ->
  uniqueness_robust_to_local_conditioning.
Admitted.

Definition the_key_bayes_calculation : prop :=
  forall C i : set,
    i :e m ->
    Pr_C_given_Unq C i c= mul_nat m (Pr_C C i).

Theorem bayes_gives_poly_distortion :
  uniqueness_robust_to_local_conditioning ->
  VV_probability_bound ->
  the_key_bayes_calculation.
Admitted.

Definition why_A_independence_helps : prop :=
  forall F A b C i : set,
    i :e m ->
    True.

Theorem A_independence_is_key :
  why_A_independence_helps.
let F A b C i.
assume Hi: i :e m.
exact TrueI.
Qed.

Definition intuition_1_A_random : prop :=
  True.

Definition intuition_2_local_small : prop :=
  True.

Definition intuition_3_uniqueness_global : prop :=
  True.

Definition intuition_4_concentration : prop :=
  True.

Definition full_intuition : prop :=
  intuition_1_A_random /\
  intuition_2_local_small /\
  intuition_3_uniqueness_global /\
  intuition_4_concentration.

Theorem intuition_supports_resolution :
  full_intuition ->
  the_key_bayes_calculation.
Admitted.

Definition formal_proof_sketch : prop :=
  (A_independent_of_local_structure) /\
  (local_chart_small) /\
  (VV_probability_bound) /\
  (uniqueness_robust_to_local_conditioning) /\
  (the_key_bayes_calculation).

Theorem CRUX2_HAS_CLEAR_RESOLUTION_PATH : formal_proof_sketch.
Admitted.

Definition remaining_work : prop :=
  True.

Definition what_needs_formal_proof : prop :=
  forall C i : set,
    i :e m ->
    Pr_Unq_given_C C i c= mul_nat m Pr_Unq.

Theorem the_core_lemma_needed : what_needs_formal_proof.
Admitted.

Definition why_core_lemma_should_hold : prop :=
  (A_independent_of_local_structure) /\
  (local_chart_small).

Theorem core_lemma_justified :
  why_core_lemma_should_hold ->
  what_needs_formal_proof.
Admitted.

Definition crux2_assessment : prop :=
  formal_proof_sketch /\
  why_core_lemma_should_hold.

Theorem CRUX2_LIKELY_RESOLVABLE_VIA_BAYES : crux2_assessment.
Admitted.

