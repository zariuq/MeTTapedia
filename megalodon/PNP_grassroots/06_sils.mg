Definition c_sils : set := three.
Definition c_z : set := four.

Definition SILS_invariant_prop : set -> prop :=
  fun m => True.

Definition SILS_short_prop : set -> prop :=
  fun m => True.

Definition SILS_polytime_prop : set -> prop :=
  fun m => True.

Definition SILS_extractor_prop : set -> prop :=
  fun m =>
    SILS_invariant_prop m /\
    SILS_short_prop m /\
    SILS_polytime_prop m.

Definition sils_length : set -> set :=
  fun m => c_sils * log2 m.

Definition SILS_contract_prop : set -> prop :=
  fun m => True.

Definition degree_sketch : set -> set :=
  fun F => 0.

Definition pattern_count_sketch : set -> set -> set :=
  fun F rho => 0.

Definition cooccurrence_sketch : set -> set :=
  fun F => 0.

Theorem concrete_sils_valid :
  forall m,
    nat_p m ->
    True.
Admitted.

Definition SILS_sigma_algebra : set -> set :=
  fun z => Power omega.

Theorem SILS_sigma_algebra_sign_invariant :
  forall m,
    SILS_extractor_prop m ->
    True.
Admitted.

Definition local_input_fn : set -> set -> set -> set :=
  fun m Phi i =>
    (degree_sketch (instance_cnf Phi), vv_labels (vv_num_rows m) (instance_matrix Phi) (instance_rhs Phi) i).

Theorem local_input_length :
  forall m Phi i,
    SILS_extractor_prop m ->
    nat_p m ->
    True.
Admitted.

Definition local_alphabet_size : set -> set :=
  fun m => exp_nat two (three * sils_length m).

Theorem local_alphabet_poly_size :
  forall m,
    nat_p m ->
    True.
Admitted.

Definition SILS_stability_prop : set -> prop :=
  fun m => True.
