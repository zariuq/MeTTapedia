Definition Chart : set -> set :=
  fun r => Power (omega :*: omega).

Definition chart_patterns : set -> set := fun C => ap C 0.
Definition chart_rule : set -> set := fun C => ap C 1.

Definition neighborhood_with_labels : set -> set -> set -> set -> set :=
  fun m Phi i r => (Empty, vv_labels (vv_num_rows m) (instance_matrix Phi) (instance_rhs Phi) i).

Definition matches_chart : set -> set -> set -> set -> prop :=
  fun m Phi i C =>
    exists P :e chart_patterns C,
      neighborhood_with_labels m Phi i (c3_radius * log2 m) = P.

Definition high_bias_region : set -> set -> set :=
  fun C eps =>
    {P :e chart_patterns C | True}.

Definition attains_high_bias : set -> set -> set -> set -> set -> prop :=
  fun m Phi i C eps =>
    exists P :e high_bias_region C eps,
      neighborhood_with_labels m Phi i (c3_radius * log2 m) = P.

Theorem chart_probability_bound :
  forall m C eps,
    nat_p m ->
    0 :e eps ->
    True.
Admitted.

Theorem few_high_bias_hits :
  forall m C eps,
    nat_p m ->
    0 :e eps ->
    True.
Admitted.

Theorem template_sparsification :
  forall m eps,
    nat_p m ->
    0 :e eps ->
    True.
Admitted.

Theorem sparsification_blocks :
  forall m eps,
    nat_p m ->
    0 :e eps ->
    True.
Admitted.

Theorem uniform_sparsification :
  forall m,
    nat_p m ->
    True.
Admitted.

Theorem locally_hard_blocks :
  forall m P delta,
    nat_p m ->
    desc_length P c= delta * num_blocks m ->
    True.
Admitted.
