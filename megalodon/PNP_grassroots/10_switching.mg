Definition local_rule : set -> set -> prop :=
  fun h m => True.

Definition sils_z : set -> set :=
  fun F => 0.

Definition block_at : set -> set :=
  fun j => Empty.

Definition switched_output : set -> set -> set -> set -> set :=
  fun P W j i => 0.

Definition subset_size : set -> set :=
  fun S => S.

Theorem Switching_by_Weakness :
  forall m P delta,
    polytime_decoder P ->
    desc_length P c= delta * num_blocks m ->
    exists gamma c_star,
      0 :e gamma /\
      0 :e c_star /\
      True.
Admitted.

Definition symmetrization_wrapper : set -> set -> set :=
  fun P m => Empty.

Definition ERM_wrapper : set -> set -> set :=
  fun P m => Empty.

Theorem symmetrization_preserves_success :
  forall P m,
    polytime_decoder P ->
    True.
Admitted.

Theorem symmetrization_wrapper_budget :
  forall P m,
    nat_p m ->
    polytime_decoder P ->
    True.
Admitted.

Theorem success_domination :
  forall P m W,
    polytime_decoder P ->
    W = ERM_wrapper P m ->
    True.
Admitted.

Theorem domination_principle :
  forall P m W upper_bound,
    polytime_decoder P ->
    W = ERM_wrapper P m ->
    True.
Admitted.

Theorem calibration_lemma :
  forall m i,
    nat_p m ->
    i :e m ->
    True.
Admitted.

Theorem ERM_generalization :
  forall m i T S,
    nat_p m ->
    True.
Admitted.

Definition O_log : set -> set :=
  fun m => log2 m.

Theorem finite_alphabet_compilation :
  forall m h d,
    nat_p m ->
    d = O_log m ->
    True.
Admitted.
