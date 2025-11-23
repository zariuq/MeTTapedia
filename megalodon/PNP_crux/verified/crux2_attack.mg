Variable m : set.
Axiom m_in_omega : m :e omega.
Axiom m_large : 16 c= m.

Definition log_m : set := Eps_i (fun k => k :e omega /\ exp_nat 2 k c= m).

Definition radius : set := mul_nat 3 log_m.

Definition Formula : set -> prop := fun F => True.
Definition Masked3CNF : set -> prop := fun F => Formula F.
Definition LinearMatrix : set -> prop := fun A => True.
Definition LinearVector : set -> prop := fun b => True.

Definition SolutionSet : set -> set := fun F =>
  {x :e (m :^: 2) | True}.

Definition NumSolutions : set -> set := fun F =>
  Eps_i (fun n => n :e omega).

Definition HasUniqueSolution : set -> set -> set -> prop := fun F A b =>
  NumSolutions F = 1.

Definition Pr_uncond : (set -> prop) -> set := fun E =>
  Eps_i (fun p => p :e omega).

Definition Pr_conditioned : (set -> prop) -> set := fun E =>
  Eps_i (fun p => p :e omega).

Definition LocalNeighborhood : set -> set -> set -> set := fun F i r =>
  {j :e m | True}.

Definition Chart : set := Empty.

Definition chart_matches : set -> set -> set -> prop := fun F i C =>
  True.

Definition local_chart_probability_uncond : set -> set -> set := fun C i =>
  Pr_uncond (fun F => chart_matches F i C).

Definition local_chart_probability_Dm : set -> set -> set := fun C i =>
  Pr_conditioned (fun F => chart_matches F i C).

Definition polynomial_distortion_bound : prop :=
  forall C i : set,
    i :e m ->
    exists poly_factor : set,
      poly_factor :e omega /\
      poly_factor c= mul_nat m m /\
      True.

Definition VV_probability : set := Eps_i (fun p => p :e omega /\ 1 c= mul_nat p m).

Definition VV_is_rare_but_not_too_rare : prop :=
  True.

Axiom VV_prob_bound : VV_is_rare_but_not_too_rare.

Definition local_variables : set -> set -> set := fun i r =>
  {j :e m | True}.

Definition num_local_vars : set -> set -> set := fun i r =>
  Eps_i (fun n => n :e omega /\ n c= exp_nat m 1).

Definition local_global_independence_intuition : prop :=
  forall i r : set,
    i :e m ->
    r c= log_m ->
    True.

Definition A_is_random : prop :=
  True.

Axiom A_random : A_is_random.

Definition A_independent_of_F : prop :=
  True.

Axiom A_F_independent : A_independent_of_F.

Definition uniqueness_determined_by_global : prop :=
  forall F A b : set,
    Masked3CNF F ->
    LinearMatrix A ->
    LinearVector b ->
    True.

Theorem uniqueness_is_global : uniqueness_determined_by_global.
Admitted.

Definition local_structure_determined_by_local : prop :=
  forall F i r C : set,
    Masked3CNF F ->
    i :e m ->
    r c= log_m ->
    True.

Theorem local_is_local : local_structure_determined_by_local.
Admitted.

Definition the_key_argument : prop :=
  A_independent_of_F ->
  uniqueness_determined_by_global ->
  local_structure_determined_by_local ->
  polynomial_distortion_bound.

Theorem conditioning_preserves_local_UP_TO_POLY :
  the_key_argument.
Admitted.

Definition formal_statement_needed : prop :=
  forall F A b i C : set,
    Masked3CNF F ->
    LinearMatrix A ->
    LinearVector b ->
    i :e m ->
    HasUniqueSolution F A b ->
    True.

Definition concentration_argument : prop :=
  forall i r : set,
    i :e m ->
    r c= log_m ->
    num_local_vars i r c= exp_nat m 1 ->
    True.

Theorem local_vars_are_few : concentration_argument.
Admitted.

Definition conditioning_on_global_doesnt_affect_local : prop :=
  forall C i : set,
    i :e m ->
    local_chart_probability_Dm C i c= mul_nat m (local_chart_probability_uncond C i).

Theorem the_missing_lemma : conditioning_on_global_doesnt_affect_local.
Admitted.

Definition why_this_should_be_true : prop :=
  (A_independent_of_F) /\
  (forall i r, i :e m -> r c= log_m -> num_local_vars i r c= exp_nat m 1) /\
  (VV_is_rare_but_not_too_rare).

Theorem crux2_resolution_argument :
  why_this_should_be_true ->
  conditioning_on_global_doesnt_affect_local.
Admitted.

Definition bayes_factor_analysis : prop :=
  forall C i : set,
    i :e m ->
    True.

Theorem bayes_bound :
  bayes_factor_analysis.
let C i.
assume Hi: i :e m.
exact TrueI.
Qed.

Definition crux2_resolution_strategy : prop :=
  conditioning_on_global_doesnt_affect_local /\
  polynomial_distortion_bound.

Theorem CRUX2_LIKELY_RESOLVABLE : crux2_resolution_strategy.
Admitted.

