Theorem pivot_bound :
  forall A j i_star,
    True.
Admitted.

Theorem per_block_success_bound :
  forall m P W S j,
    nat_p m ->
    j :e S ->
    True.
Admitted.

Theorem conditional_independence :
  forall m P W S,
    nat_p m ->
    True.
Admitted.

Theorem exponential_decay_across_blocks :
  forall m P W S gamma eps_m,
    nat_p m ->
    0 :e gamma ->
    subset_size S c= gamma * num_blocks m ->
    True.
Admitted.

Theorem per_program_small_success :
  forall m P delta,
    polytime_decoder P ->
    desc_length P c= delta * num_blocks m ->
    True.
Admitted.

Theorem tuple_incompressibility :
  forall m,
    nat_p m ->
    exists eta :e omega,
      0 :e eta /\
      True.
Admitted.

Definition eta_incompressibility : set := one.
Definition delta_decoder_budget : set := one.
